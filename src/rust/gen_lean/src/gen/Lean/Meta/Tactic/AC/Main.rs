// Lean compiler output
// Module: Lean.Meta.Tactic.AC.Main
// Imports: Lean.Meta.Tactic.Refl Lean.Meta.Tactic.Simp.Main Lean.Elab.Tactic.Rewrite Init.Omega
use crate::r#gen::Init::Data::AC::{
    l_Lean_Data_AC_Expr_toList, l_Lean_Data_AC_mergeIdem, l_Lean_Data_AC_sort,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::MetaTypes::l_Lean_Meta_Simp_neutralConfig;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_getFVarIds;
use crate::r#gen::Lean::Elab::Tactic::Location::l_Lean_Elab_Tactic_expandLocation;
use crate::r#gen::Lean::Elab::Tactic::Rewrite::{
    initialize_Lean_Elab_Tactic_Rewrite, runtime_initialize_Lean_Elab_Tactic_Rewrite,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_const___override,
    l_Lean_Expr_hasMVar, l_Lean_Expr_hash, l_Lean_Expr_isAppOfArity, l_Lean_instInhabitedExpr,
    l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp7, l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst,
    l_Lean_mkNatLit,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkAppM, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkExpectedPropHint,
    l_Lean_Meta_mkListLit,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getType___redArg,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance;
use crate::r#gen::Lean::Meta::Tactic::Refl::{
    initialize_Lean_Meta_Tactic_Refl, l_Lean_MVarId_refl, runtime_initialize_Lean_Meta_Tactic_Refl,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, l_Lean_Meta_Simp_main,
    l_Lean_Meta_applySimpResultToLocalDecl, runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    l_Lean_Meta_Simp_mkContext___redArg, l_Lean_Meta_applySimpResultToTarget,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getNondepPropHyps, l_Lean_MVarId_getType,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::{lean_expr_eqv, lean_expr_lt};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Lean_Meta_AC_instInhabitedPreContext_default___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_AC_instInhabitedPreContext_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_instInhabitedPreContext_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_instInhabitedPreContext_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_AC_instInhabitedPreContext_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AC_instInhabitedPreContext_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_instInhabitedPreContext_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_AC_instInhabitedPreContext_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_AC_instInhabitedPreContext: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__0_value:
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
    m_fun: l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__1_value:
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
    m_fun: l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__2_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
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
static mut l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__0_value:
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
    m_fun: l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__1_value:
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
    m_fun: l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__2_value:
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
    m_fun: l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_AC_instEvalInformationPreContextACExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_instEvalInformationPreContextACExpr___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__1_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__2_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_getInstance___lam__0___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Meta_AC_getInstance___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_getInstance___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_AC_getInstance___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_getInstance___lam__0___closed__2_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [103, 111, 116, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0],
};
static mut l_Lean_Meta_AC_getInstance___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_AC_getInstance___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_getInstance___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_AC_getInstance___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [77, 101, 116, 97, 0],
    };
static mut l_Lean_Meta_AC_getInstance___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_getInstance___closed__1_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [65, 67, 0],
    };
static mut l_Lean_Meta_AC_getInstance___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_AC_getInstance___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__0_value)
                as *mut crate::leanh::LeanObject,
            142734480563613395 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_AC_getInstance___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value)
                as *mut crate::leanh::LeanObject,
            3374584087459423852 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_AC_getInstance___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_AC_getInstance___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_getInstance___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_AC_getInstance___closed__4_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [116, 114, 121, 105, 110, 103, 58, 32, 0],
    };
static mut l_Lean_Meta_AC_getInstance___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_AC_getInstance___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_getInstance___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_AC_preContext___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [83, 116, 100, 0],
    };
static mut l_Lean_Meta_AC_preContext___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_preContext___closed__1_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [65, 115, 115, 111, 99, 105, 97, 116, 105, 118, 101, 0],
    };
static mut l_Lean_Meta_AC_preContext___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_AC_preContext___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_AC_preContext___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__1_value)
                as *mut crate::leanh::LeanObject,
            17561379004628073218 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_AC_preContext___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_preContext___closed__3_value: crate::leanh::LeanStringObject<12> =
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
        m_data: [67, 111, 109, 109, 117, 116, 97, 116, 105, 118, 101, 0],
    };
static mut l_Lean_Meta_AC_preContext___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_AC_preContext___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_AC_preContext___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__3_value)
                as *mut crate::leanh::LeanObject,
            234445833000607850 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_AC_preContext___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_preContext___closed__5_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [73, 100, 101, 109, 112, 111, 116, 101, 110, 116, 79, 112, 0],
    };
static mut l_Lean_Meta_AC_preContext___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_AC_preContext___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15734321041234825264 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_AC_preContext___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__5_value)
                as *mut crate::leanh::LeanObject,
            16442335306435255285 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_AC_preContext___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__0_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__1_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_AC_toACExpr___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_toACExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_AC_toACExpr___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_toACExpr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [76, 97, 119, 102, 117, 108, 73, 100, 101, 110, 116, 105, 116, 121, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_preContext___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,18153903751919310386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [105, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,6605161548626312362 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__0_value) as *mut crate::leanh::LeanObject,13655884332201764339 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_abstractAtoms___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_AC_abstractAtoms___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_abstractAtoms___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18184376426117065311 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,9480010471355609749 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 111, 109, 101, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18184376426117065311 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,4893146552088433753 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [80, 76, 105, 102, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,6088973394548839111 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [68, 97, 116, 97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [86, 97, 114, 105, 97, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__7_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject,9501819735499948977 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value) as *mut crate::leanh::LeanObject,16019485435159814966 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject,3861239522009765266 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__7_value) as *mut crate::leanh::LeanObject,16415900469135977554 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__10_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [117, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,6088973394548839111 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__10_value) as *mut crate::leanh::LeanObject,9674958116709672659 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject,9501819735499948977 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value) as *mut crate::leanh::LeanObject,16019485435159814966 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject,3861239522009765266 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 110, 116, 101, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject,9501819735499948977 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value) as *mut crate::leanh::LeanObject,16019485435159814966 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__2_value) as *mut crate::leanh::LeanObject,84945704079860692 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__7_value) as *mut crate::leanh::LeanObject,4453592708455358140 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 120, 112, 114, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [118, 97, 114, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject,9501819735499948977 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value) as *mut crate::leanh::LeanObject,16019485435159814966 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__0_value) as *mut crate::leanh::LeanObject,4142842345610983300 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__1_value) as *mut crate::leanh::LeanObject,2615219353473610045 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 112, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject,9501819735499948977 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value) as *mut crate::leanh::LeanObject,16019485435159814966 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__0_value) as *mut crate::leanh::LeanObject,4142842345610983300 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__4_value) as *mut crate::leanh::LeanObject,10223445664318413121 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0_value:
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
static mut l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_buildNormProof___lam__0___closed__0_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Meta_AC_buildNormProof___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_buildNormProof___lam__0___closed__1_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_AC_buildNormProof___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_AC_buildNormProof___lam__0___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12882480457794858234 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_AC_buildNormProof___lam__0___closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        9255189395584251158 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AC_buildNormProof___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_AC_buildNormProof___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_buildNormProof___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_AC_buildNormProof___lam__0___closed__4_value:
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
    m_data: [101, 113, 95, 111, 102, 95, 110, 111, 114, 109, 0],
};
static mut l_Lean_Meta_AC_buildNormProof___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject,9501819735499948977 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16019485435159814966 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__2_value) as *mut crate::leanh::LeanObject,84945704079860692 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__4_value)
            as *mut crate::leanh::LeanObject,
        9179272946984890006 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_AC_buildNormProof___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_buildNormProof___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_AC_buildNormProof___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_buildNormProof___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_AC_buildNormProof___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_buildNormProof___closed__2_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 65, 67, 46,
            77, 97, 105, 110, 0,
        ],
    };
static mut l_Lean_Meta_AC_buildNormProof___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_buildNormProof___closed__3_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 65, 67, 46, 98, 117, 105, 108, 100, 78,
            111, 114, 109, 80, 114, 111, 111, 102, 0,
        ],
    };
static mut l_Lean_Meta_AC_buildNormProof___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_buildNormProof___closed__4_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 112, 114, 111, 111, 102, 32, 116,
            121, 112, 101, 0,
        ],
    };
static mut l_Lean_Meta_AC_buildNormProof___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_buildNormProof___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_AC_buildNormProof___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_buildNormProof___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_AC_rewriteUnnormalized___lam__0___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_AC_rewriteUnnormalized___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_rewriteUnnormalized___lam__1___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 2,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_AC_rewriteUnnormalized___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_rewriteUnnormalized___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_rewriteUnnormalized___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_AC_rewriteUnnormalized___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_rewriteUnnormalized___closed__2_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_AC_rewriteUnnormalized___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_rewriteUnnormalized___closed__3_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_AC_rewriteUnnormalized___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_rewriteUnnormalized___closed__4_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_AC_rewriteUnnormalized___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_AC_rewriteUnnormalized___closed__12_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_AC_post___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_rewriteUnnormalized___closed__13_value: crate::leanh::LeanCtorObject<6> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 8) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__12_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__4_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_AC_rewriteUnnormalized___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_rewriteUnnormalized___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 99, 82, 102, 108, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__2_value) as *mut crate::leanh::LeanObject,7715960029724150523 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 99, 82, 102, 108, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__0_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value) as *mut crate::leanh::LeanObject,4395064566925243057 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__4_value) as *mut crate::leanh::LeanObject,1701625677982403319 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 174 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 24 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 176 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 46 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 24 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 46 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 174 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 28 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 174 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 28 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_acNfTargetTactic___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_AC_acNfTargetTactic___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_AC_acNfTargetTactic___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_acNfTargetTactic___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_AC_evalNf0___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [97, 99, 78, 102, 48, 0],
    };
static mut l_Lean_Meta_AC_evalNf0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_evalNf0___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_AC_evalNf0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_AC_evalNf0___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_AC_evalNf0___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_AC_evalNf0___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_AC_evalNf0___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_AC_evalNf0___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_AC_evalNf0___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_AC_evalNf0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1417592241587213395 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_AC_evalNf0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_evalNf0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_AC_evalNf0___closed__2_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_AC_evalNf0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_AC_evalNf0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 118, 97, 108, 78, 102, 48, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__0_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value) as *mut crate::leanh::LeanObject,4395064566925243057 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__0_value) as *mut crate::leanh::LeanObject,3949617222807927774 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__0_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__1_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__2_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__0_value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__3_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value) as *mut crate::leanh::LeanObject,18261494228143523011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__4_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value) as *mut crate::leanh::LeanObject,15227250166979325724 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 97, 105, 110, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__5_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16913488441394344241 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__7_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,13454052014816254836 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__8_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,16331625422460483701 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__9_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__0_value) as *mut crate::leanh::LeanObject,6529122282418073661 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__10_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value) as *mut crate::leanh::LeanObject,5699569296177960122 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__11_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__12_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11954242793459158303 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__13_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__14_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10545831821676603178 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__15_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject,15790189264248630955 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__16_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__0_value) as *mut crate::leanh::LeanObject,12585191707788623907 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__17_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__1_value) as *mut crate::leanh::LeanObject,5924600686160568722 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__18_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_AC_getInstance___closed__1_value) as *mut crate::leanh::LeanObject,12745499798033413697 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__19_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__6_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10569299302877638704 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3199_ = crate::leanh::lean_box(0);
    v___x_3200_ = l_Lean_Meta_AC_instInhabitedPreContext_default___closed__1;
    v___x_3201_ = l_Lean_Expr_const___override(v___x_3200_, v___x_3199_);
    return v___x_3201_;
}
pub unsafe fn _init_l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3202_ = crate::leanh::lean_box(0);
    v___x_3203_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2_once),
        _init_l_Lean_Meta_AC_instInhabitedPreContext_default___closed__2,
    );
    v___x_3204_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3205_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3205_, 0, v___x_3204_);
    crate::leanh::lean_ctor_set(v___x_3205_, 1, v___x_3203_);
    crate::leanh::lean_ctor_set(v___x_3205_, 2, v___x_3203_);
    crate::leanh::lean_ctor_set(v___x_3205_, 3, v___x_3202_);
    crate::leanh::lean_ctor_set(v___x_3205_, 4, v___x_3202_);
    return v___x_3205_;
}
pub unsafe fn _init_l_Lean_Meta_AC_instInhabitedPreContext_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3206_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3_once),
        _init_l_Lean_Meta_AC_instInhabitedPreContext_default___closed__3,
    );
    return v___x_3206_;
}
pub unsafe fn _init_l_Lean_Meta_AC_instInhabitedPreContext() -> *mut crate::leanh::LeanObject {
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3207_ = l_Lean_Meta_AC_instInhabitedPreContext_default;
    return v___x_3207_;
}
pub unsafe fn l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0(
    mut v_ctx_3208_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_comm_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3209_ = crate::leanh::lean_ctor_get(v_ctx_3208_, 0);
    v_comm_3210_ = crate::leanh::lean_ctor_get(v_fst_3209_, 3);
    if crate::leanh::lean_obj_tag(v_comm_3210_) == 0 {
        let mut v___x_3211_: u8 = 0;
        v___x_3211_ = 0;
        return v___x_3211_;
    } else {
        let mut v___x_3212_: u8 = 0;
        v___x_3212_ = 1;
        return v___x_3212_;
    }
}
pub unsafe fn l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0___boxed(
    mut v_ctx_3213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3214_: u8 = 0;
    let mut v_r_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3214_ =
        l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__0(v_ctx_3213_);
    crate::leanh::lean_dec_ref(v_ctx_3213_);
    v_r_3215_ = crate::leanh::lean_box((v_res_3214_) as usize);
    return v_r_3215_;
}
pub unsafe fn l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1(
    mut v_ctx_3216_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idem_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_3217_ = crate::leanh::lean_ctor_get(v_ctx_3216_, 0);
    v_idem_3218_ = crate::leanh::lean_ctor_get(v_fst_3217_, 4);
    if crate::leanh::lean_obj_tag(v_idem_3218_) == 0 {
        let mut v___x_3219_: u8 = 0;
        v___x_3219_ = 0;
        return v___x_3219_;
    } else {
        let mut v___x_3220_: u8 = 0;
        v___x_3220_ = 1;
        return v___x_3220_;
    }
}
pub unsafe fn l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1___boxed(
    mut v_ctx_3221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3222_: u8 = 0;
    let mut v_r_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3222_ =
        l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__1(v_ctx_3221_);
    crate::leanh::lean_dec_ref(v_ctx_3221_);
    v_r_3223_ = crate::leanh::lean_box((v_res_3222_) as usize);
    return v_r_3223_;
}
pub unsafe fn l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2(
    mut v___x_3224_: u8,
    mut v_ctx_3225_: *mut crate::leanh::LeanObject,
    mut v_x_3226_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_snd_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: u8 = 0;
    v_snd_3227_ = crate::leanh::lean_ctor_get(v_ctx_3225_, 1);
    v___x_3228_ = crate::leanh::lean_box((v___x_3224_) as usize);
    v___x_3229_ = lean_array_get(v___x_3228_, v_snd_3227_, v_x_3226_);
    crate::leanh::lean_dec(v___x_3228_);
    v___x_3230_ = (crate::leanh::lean_unbox(v___x_3229_) as u8);
    crate::leanh::lean_dec(v___x_3229_);
    return v___x_3230_;
}
pub unsafe fn l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2___boxed(
    mut v___x_3231_: *mut crate::leanh::LeanObject,
    mut v_ctx_3232_: *mut crate::leanh::LeanObject,
    mut v_x_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_53__boxed_3234_: u8 = 0;
    let mut v_res_3235_: u8 = 0;
    let mut v_r_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_53__boxed_3234_ = (crate::leanh::lean_unbox(v___x_3231_) as u8);
    v_res_3235_ = l_Lean_Meta_AC_instContextInformationProdPreContextArrayBool___lam__2(
        v___x_53__boxed_3234_,
        v_ctx_3232_,
        v_x_3233_,
    );
    crate::leanh::lean_dec(v_x_3233_);
    crate::leanh::lean_dec_ref(v_ctx_3232_);
    v_r_3236_ = crate::leanh::lean_box((v_res_3235_) as usize);
    return v_r_3236_;
}
pub unsafe fn l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0(
    mut v_x_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3250_ = l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0;
    return v___x_3250_;
}
pub unsafe fn l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___boxed(
    mut v_x_3251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3252_ = l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0(v_x_3251_);
    crate::leanh::lean_dec_ref(v_x_3251_);
    return v_res_3252_;
}
pub unsafe fn l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1(
    mut v_x_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3256_, 0, v___y_3254_);
    crate::leanh::lean_ctor_set(v___x_3256_, 1, v___y_3255_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1___boxed(
    mut v_x_3257_: *mut crate::leanh::LeanObject,
    mut v___y_3258_: *mut crate::leanh::LeanObject,
    mut v___y_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3260_ = l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__1(
        v_x_3257_,
        v___y_3258_,
        v___y_3259_,
    );
    crate::leanh::lean_dec_ref(v_x_3257_);
    return v_res_3260_;
}
pub unsafe fn l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2(
    mut v_x_3261_: *mut crate::leanh::LeanObject,
    mut v_x_3262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3263_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3263_, 0, v_x_3262_);
    return v___x_3263_;
}
pub unsafe fn l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2___boxed(
    mut v_x_3264_: *mut crate::leanh::LeanObject,
    mut v_x_3265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3266_ = l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__2(v_x_3264_, v_x_3265_);
    crate::leanh::lean_dec_ref(v_x_3264_);
    return v_res_3266_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(
    mut v_msgData_3275_: *mut crate::leanh::LeanObject,
    mut v___y_3276_: *mut crate::leanh::LeanObject,
    mut v___y_3277_: *mut crate::leanh::LeanObject,
    mut v___y_3278_: *mut crate::leanh::LeanObject,
    mut v___y_3279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3281_ = lean_st_ref_get(v___y_3279_);
    v_env_3282_ = crate::leanh::lean_ctor_get(v___x_3281_, 0);
    crate::leanh::lean_inc_ref(v_env_3282_);
    crate::leanh::lean_dec(v___x_3281_);
    v___x_3283_ = lean_st_ref_get(v___y_3277_);
    v_mctx_3284_ = crate::leanh::lean_ctor_get(v___x_3283_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3284_);
    crate::leanh::lean_dec(v___x_3283_);
    v_lctx_3285_ = crate::leanh::lean_ctor_get(v___y_3276_, 2);
    v_options_3286_ = crate::leanh::lean_ctor_get(v___y_3278_, 2);
    crate::leanh::lean_inc_ref(v_options_3286_);
    crate::leanh::lean_inc_ref(v_lctx_3285_);
    v___x_3287_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3287_, 0, v_env_3282_);
    crate::leanh::lean_ctor_set(v___x_3287_, 1, v_mctx_3284_);
    crate::leanh::lean_ctor_set(v___x_3287_, 2, v_lctx_3285_);
    crate::leanh::lean_ctor_set(v___x_3287_, 3, v_options_3286_);
    v___x_3288_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3288_, 0, v___x_3287_);
    crate::leanh::lean_ctor_set(v___x_3288_, 1, v_msgData_3275_);
    v___x_3289_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3289_, 0, v___x_3288_);
    return v___x_3289_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0___boxed(
    mut v_msgData_3290_: *mut crate::leanh::LeanObject,
    mut v___y_3291_: *mut crate::leanh::LeanObject,
    mut v___y_3292_: *mut crate::leanh::LeanObject,
    mut v___y_3293_: *mut crate::leanh::LeanObject,
    mut v___y_3294_: *mut crate::leanh::LeanObject,
    mut v___y_3295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3296_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(v_msgData_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
    crate::leanh::lean_dec(v___y_3294_);
    crate::leanh::lean_dec_ref(v___y_3293_);
    crate::leanh::lean_dec(v___y_3292_);
    crate::leanh::lean_dec_ref(v___y_3291_);
    return v_res_3296_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0() -> f64 {
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: f64 = 0.0;
    v___x_3297_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3298_ = lean_float_of_nat(v___x_3297_);
    return v___x_3298_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(
    mut v_cls_3302_: *mut crate::leanh::LeanObject,
    mut v_msg_3303_: *mut crate::leanh::LeanObject,
    mut v___y_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
    mut v___y_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3314_: u8 = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3327_: u8 = 0;
    let mut v_tid_3328_: u64 = 0;
    let mut v_traces_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3332_: u8 = 0;
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: f64 = 0.0;
    let mut v___x_3335_: u8 = 0;
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3353_: u8 = 0;
    let mut v_isSharedCheck_3354_: u8 = 0;
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3309_ = crate::leanh::lean_ctor_get(v___y_3306_, 5);
                v___x_3310_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0_spec__0(v_msg_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
                v_a_3311_ = crate::leanh::lean_ctor_get(v___x_3310_, 0);
                v_isSharedCheck_3355_ = (!crate::leanh::lean_is_exclusive(v___x_3310_)) as u8;
                if v_isSharedCheck_3355_ == 0 {
                    v___x_3313_ = v___x_3310_;
                    v_isShared_3314_ = v_isSharedCheck_3355_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3311_);
                    crate::leanh::lean_dec(v___x_3310_);
                    v___x_3313_ = crate::leanh::lean_box(0);
                    v_isShared_3314_ = v_isSharedCheck_3355_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3315_ = lean_st_ref_take(v___y_3307_);
                v_traceState_3316_ = crate::leanh::lean_ctor_get(v___x_3315_, 4);
                v_env_3317_ = crate::leanh::lean_ctor_get(v___x_3315_, 0);
                v_nextMacroScope_3318_ = crate::leanh::lean_ctor_get(v___x_3315_, 1);
                v_ngen_3319_ = crate::leanh::lean_ctor_get(v___x_3315_, 2);
                v_auxDeclNGen_3320_ = crate::leanh::lean_ctor_get(v___x_3315_, 3);
                v_cache_3321_ = crate::leanh::lean_ctor_get(v___x_3315_, 5);
                v_messages_3322_ = crate::leanh::lean_ctor_get(v___x_3315_, 6);
                v_infoState_3323_ = crate::leanh::lean_ctor_get(v___x_3315_, 7);
                v_snapshotTasks_3324_ = crate::leanh::lean_ctor_get(v___x_3315_, 8);
                v_isSharedCheck_3354_ = (!crate::leanh::lean_is_exclusive(v___x_3315_)) as u8;
                if v_isSharedCheck_3354_ == 0 {
                    v___x_3326_ = v___x_3315_;
                    v_isShared_3327_ = v_isSharedCheck_3354_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3324_);
                    crate::leanh::lean_inc(v_infoState_3323_);
                    crate::leanh::lean_inc(v_messages_3322_);
                    crate::leanh::lean_inc(v_cache_3321_);
                    crate::leanh::lean_inc(v_traceState_3316_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3320_);
                    crate::leanh::lean_inc(v_ngen_3319_);
                    crate::leanh::lean_inc(v_nextMacroScope_3318_);
                    crate::leanh::lean_inc(v_env_3317_);
                    crate::leanh::lean_dec(v___x_3315_);
                    v___x_3326_ = crate::leanh::lean_box(0);
                    v_isShared_3327_ = v_isSharedCheck_3354_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3328_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3316_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3329_ = crate::leanh::lean_ctor_get(v_traceState_3316_, 0);
                v_isSharedCheck_3353_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3316_)) as u8;
                if v_isSharedCheck_3353_ == 0 {
                    v___x_3331_ = v_traceState_3316_;
                    v_isShared_3332_ = v_isSharedCheck_3353_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3329_);
                    crate::leanh::lean_dec(v_traceState_3316_);
                    v___x_3331_ = crate::leanh::lean_box(0);
                    v_isShared_3332_ = v_isSharedCheck_3353_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3333_ = crate::leanh::lean_box(0);
                v___x_3334_ = crate::leanh::lean_float_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0_once
                    ),
                    _init_l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__0,
                );
                v___x_3335_ = 0;
                v___x_3336_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__1;
                v___x_3337_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3337_, 0, v_cls_3302_);
                crate::leanh::lean_ctor_set(v___x_3337_, 1, v___x_3333_);
                crate::leanh::lean_ctor_set(v___x_3337_, 2, v___x_3336_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3337_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3334_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3337_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3334_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3337_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3335_,
                );
                v___x_3338_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___closed__2;
                v___x_3339_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3339_, 0, v___x_3337_);
                crate::leanh::lean_ctor_set(v___x_3339_, 1, v_a_3311_);
                crate::leanh::lean_ctor_set(v___x_3339_, 2, v___x_3338_);
                crate::leanh::lean_inc(v_ref_3309_);
                v___x_3340_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3340_, 0, v_ref_3309_);
                crate::leanh::lean_ctor_set(v___x_3340_, 1, v___x_3339_);
                v___x_3341_ = l_Lean_PersistentArray_push___redArg(v_traces_3329_, v___x_3340_);
                if v_isShared_3332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3331_, 0, v___x_3341_);
                    v___x_3343_ = v___x_3331_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3352_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3341_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3352_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3328_,
                    );
                    v___x_3343_ = v_reuseFailAlloc_3352_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3327_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3326_, 4, v___x_3343_);
                    v___x_3345_ = v___x_3326_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_env_3317_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_nextMacroScope_3318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 2, v_ngen_3319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 3, v_auxDeclNGen_3320_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 4, v___x_3343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 5, v_cache_3321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 6, v_messages_3322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 7, v_infoState_3323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 8, v_snapshotTasks_3324_);
                    v___x_3345_ = v_reuseFailAlloc_3351_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3346_ = lean_st_ref_set(v___y_3307_, v___x_3345_);
                v___x_3347_ = crate::leanh::lean_box(0);
                if v_isShared_3314_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3313_, 0, v___x_3347_);
                    v___x_3349_ = v___x_3313_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
                    v___x_3349_ = v_reuseFailAlloc_3350_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0___boxed(
    mut v_cls_3356_: *mut crate::leanh::LeanObject,
    mut v_msg_3357_: *mut crate::leanh::LeanObject,
    mut v___y_3358_: *mut crate::leanh::LeanObject,
    mut v___y_3359_: *mut crate::leanh::LeanObject,
    mut v___y_3360_: *mut crate::leanh::LeanObject,
    mut v___y_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(
        v_cls_3356_,
        v_msg_3357_,
        v___y_3358_,
        v___y_3359_,
        v___y_3360_,
        v___y_3361_,
    );
    crate::leanh::lean_dec(v___y_3361_);
    crate::leanh::lean_dec_ref(v___y_3360_);
    crate::leanh::lean_dec(v___y_3359_);
    crate::leanh::lean_dec_ref(v___y_3358_);
    return v_res_3363_;
}
pub unsafe fn _init_l_Lean_Meta_AC_getInstance___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3368_ = l_Lean_Meta_AC_getInstance___lam__0___closed__2;
    v___x_3369_ = l_Lean_stringToMessageData(v___x_3368_);
    return v___x_3369_;
}
pub unsafe fn l_Lean_Meta_AC_getInstance___lam__0(
    mut v_a_3370_: *mut crate::leanh::LeanObject,
    mut v___x_3371_: *mut crate::leanh::LeanObject,
    mut v_____r_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
    mut v___y_3374_: *mut crate::leanh::LeanObject,
    mut v___y_3375_: *mut crate::leanh::LeanObject,
    mut v___y_3376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3383_: u8 = 0;
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3391_: u8 = 0;
    let mut v_inheritedTraceOptions_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3401_: u8 = 0;
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3405_: u8 = 0;
    let mut v_isSharedCheck_3406_: u8 = 0;
    let mut v_a_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3378_ = crate::leanh::lean_box(0);
                v___x_3379_ = l_Lean_Meta_synthInstance(
                    v_a_3370_,
                    v___x_3378_,
                    v___y_3373_,
                    v___y_3374_,
                    v___y_3375_,
                    v___y_3376_,
                );
                if crate::leanh::lean_obj_tag(v___x_3379_) == 0 {
                    v_a_3380_ = crate::leanh::lean_ctor_get(v___x_3379_, 0);
                    v_isSharedCheck_3406_ = (!crate::leanh::lean_is_exclusive(v___x_3379_)) as u8;
                    if v_isSharedCheck_3406_ == 0 {
                        v___x_3382_ = v___x_3379_;
                        v_isShared_3383_ = v_isSharedCheck_3406_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3380_);
                        crate::leanh::lean_dec(v___x_3379_);
                        v___x_3382_ = crate::leanh::lean_box(0);
                        v_isShared_3383_ = v_isSharedCheck_3406_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3371_);
                    v_a_3407_ = crate::leanh::lean_ctor_get(v___x_3379_, 0);
                    v_isSharedCheck_3414_ = (!crate::leanh::lean_is_exclusive(v___x_3379_)) as u8;
                    if v_isSharedCheck_3414_ == 0 {
                        v___x_3409_ = v___x_3379_;
                        v_isShared_3410_ = v_isSharedCheck_3414_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3407_);
                        crate::leanh::lean_dec(v___x_3379_);
                        v___x_3409_ = crate::leanh::lean_box(0);
                        v_isShared_3410_ = v_isSharedCheck_3414_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_options_3390_ = crate::leanh::lean_ctor_get(v___y_3375_, 2);
                v_hasTrace_3391_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3390_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3391_ == 0 {
                    crate::leanh::lean_dec(v___x_3371_);
                    state = 2;
                    continue;
                } else {
                    v_inheritedTraceOptions_3392_ = crate::leanh::lean_ctor_get(v___y_3375_, 13);
                    v___x_3393_ = l_Lean_Meta_AC_getInstance___lam__0___closed__1;
                    crate::leanh::lean_inc(v___x_3371_);
                    v___x_3394_ = l_Lean_Name_append(v___x_3393_, v___x_3371_);
                    v___x_3395_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3392_,
                        v_options_3390_,
                        v___x_3394_,
                    );
                    crate::leanh::lean_dec(v___x_3394_);
                    if v___x_3395_ == 0 {
                        crate::leanh::lean_dec(v___x_3371_);
                        state = 2;
                        continue;
                    } else {
                        v___x_3396_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_AC_getInstance___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_AC_getInstance___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Meta_AC_getInstance___lam__0___closed__3,
                        );
                        v___x_3397_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(
                            v___x_3371_,
                            v___x_3396_,
                            v___y_3373_,
                            v___y_3374_,
                            v___y_3375_,
                            v___y_3376_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3397_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3397_, 1);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_3382_);
                            crate::leanh::lean_dec(v_a_3380_);
                            v_a_3398_ = crate::leanh::lean_ctor_get(v___x_3397_, 0);
                            v_isSharedCheck_3405_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3397_)) as u8;
                            if v_isSharedCheck_3405_ == 0 {
                                v___x_3400_ = v___x_3397_;
                                v_isShared_3401_ = v_isSharedCheck_3405_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3398_);
                                crate::leanh::lean_dec(v___x_3397_);
                                v___x_3400_ = crate::leanh::lean_box(0);
                                v_isShared_3401_ = v_isSharedCheck_3405_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3385_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3385_, 0, v_a_3380_);
                v___x_3386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3386_, 0, v___x_3385_);
                if v_isShared_3383_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3382_, 0, v___x_3386_);
                    v___x_3388_ = v___x_3382_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3389_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
                    v___x_3388_ = v_reuseFailAlloc_3389_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3388_;
            }
            4 => {
                if v_isShared_3401_ == 0 {
                    v___x_3403_ = v___x_3400_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
                    v___x_3403_ = v_reuseFailAlloc_3404_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3403_;
            }
            6 => {
                if v_isShared_3410_ == 0 {
                    v___x_3412_ = v___x_3409_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
                    v___x_3412_ = v_reuseFailAlloc_3413_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_getInstance___lam__0___boxed(
    mut v_a_3415_: *mut crate::leanh::LeanObject,
    mut v___x_3416_: *mut crate::leanh::LeanObject,
    mut v_____r_3417_: *mut crate::leanh::LeanObject,
    mut v___y_3418_: *mut crate::leanh::LeanObject,
    mut v___y_3419_: *mut crate::leanh::LeanObject,
    mut v___y_3420_: *mut crate::leanh::LeanObject,
    mut v___y_3421_: *mut crate::leanh::LeanObject,
    mut v___y_3422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3423_ = l_Lean_Meta_AC_getInstance___lam__0(
        v_a_3415_,
        v___x_3416_,
        v_____r_3417_,
        v___y_3418_,
        v___y_3419_,
        v___y_3420_,
        v___y_3421_,
    );
    crate::leanh::lean_dec(v___y_3421_);
    crate::leanh::lean_dec_ref(v___y_3420_);
    crate::leanh::lean_dec(v___y_3419_);
    crate::leanh::lean_dec_ref(v___y_3418_);
    return v_res_3423_;
}
pub unsafe fn _init_l_Lean_Meta_AC_getInstance___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3429_ = l_Lean_Meta_AC_getInstance___closed__2;
    v___x_3430_ = l_Lean_Meta_AC_getInstance___lam__0___closed__1;
    v___x_3431_ = l_Lean_Name_append(v___x_3430_, v___x_3429_);
    return v___x_3431_;
}
pub unsafe fn _init_l_Lean_Meta_AC_getInstance___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_Meta_AC_getInstance___closed__4;
    v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
    return v___x_3434_;
}
pub unsafe fn l_Lean_Meta_AC_getInstance(
    mut v_cls_3435_: *mut crate::leanh::LeanObject,
    mut v_exprs_3436_: *mut crate::leanh::LeanObject,
    mut v_a_3437_: *mut crate::leanh::LeanObject,
    mut v_a_3438_: *mut crate::leanh::LeanObject,
    mut v_a_3439_: *mut crate::leanh::LeanObject,
    mut v_a_3440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: u8 = 0;
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: u8 = 0;
    let mut v___x_3451_: u8 = 0;
    let mut v___y_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3457_: u8 = 0;
    let mut v_a_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3462_: u8 = 0;
    let mut v_a_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3468_: u8 = 0;
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: u8 = 0;
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3464_ = l_Lean_Meta_mkAppM(
                    v_cls_3435_,
                    v_exprs_3436_,
                    v_a_3437_,
                    v_a_3438_,
                    v_a_3439_,
                    v_a_3440_,
                );
                if crate::leanh::lean_obj_tag(v___x_3464_) == 0 {
                    v_options_3465_ = crate::leanh::lean_ctor_get(v_a_3439_, 2);
                    v_a_3466_ = crate::leanh::lean_ctor_get(v___x_3464_, 0);
                    crate::leanh::lean_inc(v_a_3466_);
                    crate::leanh::lean_dec_ref_known(v___x_3464_, 1);
                    v_inheritedTraceOptions_3467_ = crate::leanh::lean_ctor_get(v_a_3439_, 13);
                    v_hasTrace_3468_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_3465_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_3469_ = l_Lean_Meta_AC_getInstance___closed__2;
                    if v_hasTrace_3468_ == 0 {
                        state = 6;
                        continue;
                    } else {
                        v___x_3473_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_AC_getInstance___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_Meta_AC_getInstance___closed__3_once),
                            _init_l_Lean_Meta_AC_getInstance___closed__3,
                        );
                        v___x_3474_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3467_,
                            v_options_3465_,
                            v___x_3473_,
                        );
                        if v___x_3474_ == 0 {
                            state = 6;
                            continue;
                        } else {
                            v___x_3475_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_AC_getInstance___closed__5),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_AC_getInstance___closed__5_once
                                ),
                                _init_l_Lean_Meta_AC_getInstance___closed__5,
                            );
                            crate::leanh::lean_inc(v_a_3466_);
                            v___x_3476_ = l_Lean_indentExpr(v_a_3466_);
                            v___x_3477_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3477_, 0, v___x_3475_);
                            crate::leanh::lean_ctor_set(v___x_3477_, 1, v___x_3476_);
                            v___x_3478_ = l_Lean_addTrace___at___00Lean_Meta_AC_getInstance_spec__0(
                                v___x_3469_,
                                v___x_3477_,
                                v_a_3437_,
                                v_a_3438_,
                                v_a_3439_,
                                v_a_3440_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3478_) == 0 {
                                v_a_3479_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
                                crate::leanh::lean_inc(v_a_3479_);
                                crate::leanh::lean_dec_ref_known(v___x_3478_, 1);
                                v___x_3480_ = l_Lean_Meta_AC_getInstance___lam__0(
                                    v_a_3466_,
                                    v___x_3469_,
                                    v_a_3479_,
                                    v_a_3437_,
                                    v_a_3438_,
                                    v_a_3439_,
                                    v_a_3440_,
                                );
                                v___y_3453_ = v___x_3480_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_3466_);
                                v_a_3481_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
                                crate::leanh::lean_inc(v_a_3481_);
                                crate::leanh::lean_dec_ref_known(v___x_3478_, 1);
                                v_a_3449_ = v_a_3481_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_3482_ = crate::leanh::lean_ctor_get(v___x_3464_, 0);
                    crate::leanh::lean_inc(v_a_3482_);
                    crate::leanh::lean_dec_ref_known(v___x_3464_, 1);
                    v_a_3449_ = v_a_3482_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_3444_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3443_);
                    v___x_3445_ = crate::leanh::lean_box(0);
                    v___x_3446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3446_, 0, v___x_3445_);
                    return v___x_3446_;
                } else {
                    v___x_3447_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3447_, 0, v___y_3443_);
                    return v___x_3447_;
                }
            }
            2 => {
                v___x_3450_ = l_Lean_Exception_isInterrupt(v_a_3449_);
                if v___x_3450_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_3449_);
                    v___x_3451_ = l_Lean_Exception_isRuntime(v_a_3449_);
                    v___y_3443_ = v_a_3449_;
                    v___y_3444_ = v___x_3451_;
                    state = 1;
                    continue;
                } else {
                    v___y_3443_ = v_a_3449_;
                    v___y_3444_ = v___x_3450_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_3453_) == 0 {
                    v_a_3454_ = crate::leanh::lean_ctor_get(v___y_3453_, 0);
                    v_isSharedCheck_3462_ = (!crate::leanh::lean_is_exclusive(v___y_3453_)) as u8;
                    if v_isSharedCheck_3462_ == 0 {
                        v___x_3456_ = v___y_3453_;
                        v_isShared_3457_ = v_isSharedCheck_3462_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3454_);
                        crate::leanh::lean_dec(v___y_3453_);
                        v___x_3456_ = crate::leanh::lean_box(0);
                        v_isShared_3457_ = v_isSharedCheck_3462_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_3463_ = crate::leanh::lean_ctor_get(v___y_3453_, 0);
                    crate::leanh::lean_inc(v_a_3463_);
                    crate::leanh::lean_dec_ref_known(v___y_3453_, 1);
                    v_a_3449_ = v_a_3463_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_a_3458_ = crate::leanh::lean_ctor_get(v_a_3454_, 0);
                crate::leanh::lean_inc(v_a_3458_);
                crate::leanh::lean_dec(v_a_3454_);
                if v_isShared_3457_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3456_, 0, v_a_3458_);
                    v___x_3460_ = v___x_3456_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3458_);
                    v___x_3460_ = v_reuseFailAlloc_3461_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3460_;
            }
            6 => {
                v___x_3471_ = crate::leanh::lean_box(0);
                v___x_3472_ = l_Lean_Meta_AC_getInstance___lam__0(
                    v_a_3466_,
                    v___x_3469_,
                    v___x_3471_,
                    v_a_3437_,
                    v_a_3438_,
                    v_a_3439_,
                    v_a_3440_,
                );
                v___y_3453_ = v___x_3472_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_getInstance___boxed(
    mut v_cls_3483_: *mut crate::leanh::LeanObject,
    mut v_exprs_3484_: *mut crate::leanh::LeanObject,
    mut v_a_3485_: *mut crate::leanh::LeanObject,
    mut v_a_3486_: *mut crate::leanh::LeanObject,
    mut v_a_3487_: *mut crate::leanh::LeanObject,
    mut v_a_3488_: *mut crate::leanh::LeanObject,
    mut v_a_3489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3490_ = l_Lean_Meta_AC_getInstance(
        v_cls_3483_,
        v_exprs_3484_,
        v_a_3485_,
        v_a_3486_,
        v_a_3487_,
        v_a_3488_,
    );
    crate::leanh::lean_dec(v_a_3488_);
    crate::leanh::lean_dec_ref(v_a_3487_);
    crate::leanh::lean_dec(v_a_3486_);
    crate::leanh::lean_dec_ref(v_a_3485_);
    return v_res_3490_;
}
pub unsafe fn l_Lean_Meta_AC_preContext(
    mut v_expr_3504_: *mut crate::leanh::LeanObject,
    mut v_a_3505_: *mut crate::leanh::LeanObject,
    mut v_a_3506_: *mut crate::leanh::LeanObject,
    mut v_a_3507_: *mut crate::leanh::LeanObject,
    mut v_a_3508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3518_: u8 = 0;
    let mut v_val_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3531_: u8 = 0;
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3540_: u8 = 0;
    let mut v_a_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3544_: u8 = 0;
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3548_: u8 = 0;
    let mut v_a_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3552_: u8 = 0;
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3556_: u8 = 0;
    let mut v_isSharedCheck_3557_: u8 = 0;
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3562_: u8 = 0;
    let mut v_a_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3510_ = l_Lean_Meta_AC_preContext___closed__2;
                v___x_3511_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3512_ = lean_mk_empty_array_with_capacity(v___x_3511_);
                crate::leanh::lean_inc_ref(v_expr_3504_);
                v___x_3513_ = lean_array_push(v___x_3512_, v_expr_3504_);
                crate::leanh::lean_inc_ref(v___x_3513_);
                v___x_3514_ = l_Lean_Meta_AC_getInstance(
                    v___x_3510_,
                    v___x_3513_,
                    v_a_3505_,
                    v_a_3506_,
                    v_a_3507_,
                    v_a_3508_,
                );
                if crate::leanh::lean_obj_tag(v___x_3514_) == 0 {
                    v_a_3515_ = crate::leanh::lean_ctor_get(v___x_3514_, 0);
                    v_isSharedCheck_3562_ = (!crate::leanh::lean_is_exclusive(v___x_3514_)) as u8;
                    if v_isSharedCheck_3562_ == 0 {
                        v___x_3517_ = v___x_3514_;
                        v_isShared_3518_ = v_isSharedCheck_3562_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3515_);
                        crate::leanh::lean_dec(v___x_3514_);
                        v___x_3517_ = crate::leanh::lean_box(0);
                        v_isShared_3518_ = v_isSharedCheck_3562_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3513_);
                    crate::leanh::lean_dec_ref(v_expr_3504_);
                    v_a_3563_ = crate::leanh::lean_ctor_get(v___x_3514_, 0);
                    v_isSharedCheck_3570_ = (!crate::leanh::lean_is_exclusive(v___x_3514_)) as u8;
                    if v_isSharedCheck_3570_ == 0 {
                        v___x_3565_ = v___x_3514_;
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3563_);
                        crate::leanh::lean_dec(v___x_3514_);
                        v___x_3565_ = crate::leanh::lean_box(0);
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3515_) == 1 {
                    crate::leanh::lean_del_object(v___x_3517_);
                    v_val_3519_ = crate::leanh::lean_ctor_get(v_a_3515_, 0);
                    v_isSharedCheck_3557_ = (!crate::leanh::lean_is_exclusive(v_a_3515_)) as u8;
                    if v_isSharedCheck_3557_ == 0 {
                        v___x_3521_ = v_a_3515_;
                        v_isShared_3522_ = v_isSharedCheck_3557_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3519_);
                        crate::leanh::lean_dec(v_a_3515_);
                        v___x_3521_ = crate::leanh::lean_box(0);
                        v_isShared_3522_ = v_isSharedCheck_3557_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3515_);
                    crate::leanh::lean_dec_ref(v___x_3513_);
                    crate::leanh::lean_dec_ref(v_expr_3504_);
                    v___x_3558_ = crate::leanh::lean_box(0);
                    if v_isShared_3518_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3517_, 0, v___x_3558_);
                        v___x_3560_ = v___x_3517_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3558_);
                        v___x_3560_ = v_reuseFailAlloc_3561_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3523_ = l_Lean_Meta_AC_preContext___closed__4;
                crate::leanh::lean_inc_ref(v___x_3513_);
                v___x_3524_ = l_Lean_Meta_AC_getInstance(
                    v___x_3523_,
                    v___x_3513_,
                    v_a_3505_,
                    v_a_3506_,
                    v_a_3507_,
                    v_a_3508_,
                );
                if crate::leanh::lean_obj_tag(v___x_3524_) == 0 {
                    v_a_3525_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                    crate::leanh::lean_inc(v_a_3525_);
                    crate::leanh::lean_dec_ref_known(v___x_3524_, 1);
                    v___x_3526_ = l_Lean_Meta_AC_preContext___closed__6;
                    v___x_3527_ = l_Lean_Meta_AC_getInstance(
                        v___x_3526_,
                        v___x_3513_,
                        v_a_3505_,
                        v_a_3506_,
                        v_a_3507_,
                        v_a_3508_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3527_) == 0 {
                        v_a_3528_ = crate::leanh::lean_ctor_get(v___x_3527_, 0);
                        v_isSharedCheck_3540_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3527_)) as u8;
                        if v_isSharedCheck_3540_ == 0 {
                            v___x_3530_ = v___x_3527_;
                            v_isShared_3531_ = v_isSharedCheck_3540_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3528_);
                            crate::leanh::lean_dec(v___x_3527_);
                            v___x_3530_ = crate::leanh::lean_box(0);
                            v_isShared_3531_ = v_isSharedCheck_3540_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3525_);
                        crate::leanh::lean_del_object(v___x_3521_);
                        crate::leanh::lean_dec(v_val_3519_);
                        crate::leanh::lean_dec_ref(v_expr_3504_);
                        v_a_3541_ = crate::leanh::lean_ctor_get(v___x_3527_, 0);
                        v_isSharedCheck_3548_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3527_)) as u8;
                        if v_isSharedCheck_3548_ == 0 {
                            v___x_3543_ = v___x_3527_;
                            v_isShared_3544_ = v_isSharedCheck_3548_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3541_);
                            crate::leanh::lean_dec(v___x_3527_);
                            v___x_3543_ = crate::leanh::lean_box(0);
                            v_isShared_3544_ = v_isSharedCheck_3548_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3521_);
                    crate::leanh::lean_dec(v_val_3519_);
                    crate::leanh::lean_dec_ref(v___x_3513_);
                    crate::leanh::lean_dec_ref(v_expr_3504_);
                    v_a_3549_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                    v_isSharedCheck_3556_ = (!crate::leanh::lean_is_exclusive(v___x_3524_)) as u8;
                    if v_isSharedCheck_3556_ == 0 {
                        v___x_3551_ = v___x_3524_;
                        v_isShared_3552_ = v_isSharedCheck_3556_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3549_);
                        crate::leanh::lean_dec(v___x_3524_);
                        v___x_3551_ = crate::leanh::lean_box(0);
                        v_isShared_3552_ = v_isSharedCheck_3556_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3532_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3533_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3533_, 0, v___x_3532_);
                crate::leanh::lean_ctor_set(v___x_3533_, 1, v_expr_3504_);
                crate::leanh::lean_ctor_set(v___x_3533_, 2, v_val_3519_);
                crate::leanh::lean_ctor_set(v___x_3533_, 3, v_a_3525_);
                crate::leanh::lean_ctor_set(v___x_3533_, 4, v_a_3528_);
                if v_isShared_3522_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3521_, 0, v___x_3533_);
                    v___x_3535_ = v___x_3521_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3533_);
                    v___x_3535_ = v_reuseFailAlloc_3539_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3531_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3530_, 0, v___x_3535_);
                    v___x_3537_ = v___x_3530_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3538_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3535_);
                    v___x_3537_ = v_reuseFailAlloc_3538_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3537_;
            }
            6 => {
                if v_isShared_3544_ == 0 {
                    v___x_3546_ = v___x_3543_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
                    v___x_3546_ = v_reuseFailAlloc_3547_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3546_;
            }
            8 => {
                if v_isShared_3552_ == 0 {
                    v___x_3554_ = v___x_3551_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3555_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
                    v___x_3554_ = v_reuseFailAlloc_3555_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3554_;
            }
            10 => {
                return v___x_3560_;
            }
            11 => {
                if v_isShared_3566_ == 0 {
                    v___x_3568_ = v___x_3565_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
                    v___x_3568_ = v_reuseFailAlloc_3569_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_preContext___boxed(
    mut v_expr_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
    mut v_a_3576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3577_ =
        l_Lean_Meta_AC_preContext(v_expr_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
    crate::leanh::lean_dec(v_a_3575_);
    crate::leanh::lean_dec_ref(v_a_3574_);
    crate::leanh::lean_dec(v_a_3573_);
    crate::leanh::lean_dec_ref(v_a_3572_);
    return v_res_3577_;
}
pub unsafe fn l_Lean_Meta_AC_PreExpr_ctorIdx(
    mut v_x_3578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3578_) == 0 {
        let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3579_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3579_;
    } else {
        let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3580_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3580_;
    }
}
pub unsafe fn l_Lean_Meta_AC_PreExpr_ctorIdx___boxed(
    mut v_x_3581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3582_ = l_Lean_Meta_AC_PreExpr_ctorIdx(v_x_3581_);
    crate::leanh::lean_dec_ref(v_x_3581_);
    return v_res_3582_;
}
pub unsafe fn l_Lean_Meta_AC_PreExpr_ctorElim___redArg(
    mut v_t_3583_: *mut crate::leanh::LeanObject,
    mut v_k_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_3583_) == 0 {
        let mut v_lhs_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_lhs_3585_ = crate::leanh::lean_ctor_get(v_t_3583_, 0);
        crate::leanh::lean_inc_ref(v_lhs_3585_);
        v_rhs_3586_ = crate::leanh::lean_ctor_get(v_t_3583_, 1);
        crate::leanh::lean_inc_ref(v_rhs_3586_);
        crate::leanh::lean_dec_ref_known(v_t_3583_, 2);
        v___x_3587_ = crate::leanh::lean_apply_2(v_k_3584_, v_lhs_3585_, v_rhs_3586_);
        return v___x_3587_;
    } else {
        let mut v_e_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_e_3588_ = crate::leanh::lean_ctor_get(v_t_3583_, 0);
        crate::leanh::lean_inc_ref(v_e_3588_);
        crate::leanh::lean_dec_ref_known(v_t_3583_, 1);
        v___x_3589_ = crate::leanh::lean_apply_1(v_k_3584_, v_e_3588_);
        return v___x_3589_;
    }
}
pub unsafe fn l_Lean_Meta_AC_PreExpr_ctorElim(
    mut v_motive_3590_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3591_: *mut crate::leanh::LeanObject,
    mut v_t_3592_: *mut crate::leanh::LeanObject,
    mut v_h_3593_: *mut crate::leanh::LeanObject,
    mut v_k_3594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3595_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_3592_, v_k_3594_);
    return v___x_3595_;
}
pub unsafe fn l_Lean_Meta_AC_PreExpr_ctorElim___boxed(
    mut v_motive_3596_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3597_: *mut crate::leanh::LeanObject,
    mut v_t_3598_: *mut crate::leanh::LeanObject,
    mut v_h_3599_: *mut crate::leanh::LeanObject,
    mut v_k_3600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3601_ = l_Lean_Meta_AC_PreExpr_ctorElim(
        v_motive_3596_,
        v_ctorIdx_3597_,
        v_t_3598_,
        v_h_3599_,
        v_k_3600_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3597_);
    return v_res_3601_;
}
pub unsafe fn l_Lean_Meta_AC_PreExpr_op_elim___redArg(
    mut v_t_3602_: *mut crate::leanh::LeanObject,
    mut v_op_3603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3604_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_3602_, v_op_3603_);
    return v___x_3604_;
}
pub unsafe fn l_Lean_Meta_AC_PreExpr_op_elim(
    mut v_motive_3605_: *mut crate::leanh::LeanObject,
    mut v_t_3606_: *mut crate::leanh::LeanObject,
    mut v_h_3607_: *mut crate::leanh::LeanObject,
    mut v_op_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3609_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_3606_, v_op_3608_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_Meta_AC_PreExpr_var_elim___redArg(
    mut v_t_3610_: *mut crate::leanh::LeanObject,
    mut v_var_3611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3612_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_3610_, v_var_3611_);
    return v___x_3612_;
}
pub unsafe fn l_Lean_Meta_AC_PreExpr_var_elim(
    mut v_motive_3613_: *mut crate::leanh::LeanObject,
    mut v_t_3614_: *mut crate::leanh::LeanObject,
    mut v_h_3615_: *mut crate::leanh::LeanObject,
    mut v_var_3616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3617_ = l_Lean_Meta_AC_PreExpr_ctorElim___redArg(v_t_3614_, v_var_3616_);
    return v___x_3617_;
}
pub unsafe fn l_Lean_Meta_AC_bin(
    mut v_op_3618_: *mut crate::leanh::LeanObject,
    mut v_l_3619_: *mut crate::leanh::LeanObject,
    mut v_r_3620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3621_ = l_Lean_Expr_app___override(v_op_3618_, v_l_3619_);
    v___x_3622_ = l_Lean_Expr_app___override(v___x_3621_, v_r_3620_);
    return v___x_3622_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(
    mut v_a_3623_: *mut crate::leanh::LeanObject,
    mut v_x_3624_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3625_: u8 = 0;
    let mut v_key_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3624_) == 0 {
                    v___x_3625_ = 0;
                    return v___x_3625_;
                } else {
                    v_key_3626_ = crate::leanh::lean_ctor_get(v_x_3624_, 0);
                    v_tail_3627_ = crate::leanh::lean_ctor_get(v_x_3624_, 2);
                    v___x_3628_ = lean_expr_eqv(v_key_3626_, v_a_3623_);
                    if v___x_3628_ == 0 {
                        v_x_3624_ = v_tail_3627_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3628_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg___boxed(
    mut v_a_3630_: *mut crate::leanh::LeanObject,
    mut v_x_3631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3632_: u8 = 0;
    let mut v_r_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_3630_, v_x_3631_);
    crate::leanh::lean_dec(v_x_3631_);
    crate::leanh::lean_dec_ref(v_a_3630_);
    v_r_3633_ = crate::leanh::lean_box((v_res_3632_) as usize);
    return v_r_3633_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_3634_: *mut crate::leanh::LeanObject,
    mut v_x_3635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: u64 = 0;
    let mut v___x_3644_: u64 = 0;
    let mut v___x_3645_: u64 = 0;
    let mut v_fold_3646_: u64 = 0;
    let mut v___x_3647_: u64 = 0;
    let mut v___x_3648_: u64 = 0;
    let mut v___x_3649_: u64 = 0;
    let mut v___x_3650_: usize = 0;
    let mut v___x_3651_: usize = 0;
    let mut v___x_3652_: usize = 0;
    let mut v___x_3653_: usize = 0;
    let mut v___x_3654_: usize = 0;
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3635_) == 0 {
                    return v_x_3634_;
                } else {
                    v_key_3636_ = crate::leanh::lean_ctor_get(v_x_3635_, 0);
                    v_value_3637_ = crate::leanh::lean_ctor_get(v_x_3635_, 1);
                    v_tail_3638_ = crate::leanh::lean_ctor_get(v_x_3635_, 2);
                    v_isSharedCheck_3661_ = (!crate::leanh::lean_is_exclusive(v_x_3635_)) as u8;
                    if v_isSharedCheck_3661_ == 0 {
                        v___x_3640_ = v_x_3635_;
                        v_isShared_3641_ = v_isSharedCheck_3661_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3638_);
                        crate::leanh::lean_inc(v_value_3637_);
                        crate::leanh::lean_inc(v_key_3636_);
                        crate::leanh::lean_dec(v_x_3635_);
                        v___x_3640_ = crate::leanh::lean_box(0);
                        v_isShared_3641_ = v_isSharedCheck_3661_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3642_ = lean_array_get_size(v_x_3634_);
                v___x_3643_ = l_Lean_Expr_hash(v_key_3636_);
                v___x_3644_ = 32u64;
                v___x_3645_ = lean_uint64_shift_right(v___x_3643_, v___x_3644_);
                v_fold_3646_ = lean_uint64_xor(v___x_3643_, v___x_3645_);
                v___x_3647_ = 16u64;
                v___x_3648_ = lean_uint64_shift_right(v_fold_3646_, v___x_3647_);
                v___x_3649_ = lean_uint64_xor(v_fold_3646_, v___x_3648_);
                v___x_3650_ = lean_uint64_to_usize(v___x_3649_);
                v___x_3651_ = lean_usize_of_nat(v___x_3642_);
                v___x_3652_ = 1usize;
                v___x_3653_ = lean_usize_sub(v___x_3651_, v___x_3652_);
                v___x_3654_ = lean_usize_land(v___x_3650_, v___x_3653_);
                v___x_3655_ = lean_array_uget_borrowed(v_x_3634_, v___x_3654_);
                crate::leanh::lean_inc(v___x_3655_);
                if v_isShared_3641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3640_, 2, v___x_3655_);
                    v___x_3657_ = v___x_3640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_key_3636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_value_3637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 2, v___x_3655_);
                    v___x_3657_ = v_reuseFailAlloc_3660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3658_ = lean_array_uset(v_x_3634_, v___x_3654_, v___x_3657_);
                v_x_3634_ = v___x_3658_;
                v_x_3635_ = v_tail_3638_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(
    mut v_i_3662_: *mut crate::leanh::LeanObject,
    mut v_source_3663_: *mut crate::leanh::LeanObject,
    mut v_target_3664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: u8 = 0;
    let mut v_es_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3665_ = lean_array_get_size(v_source_3663_);
                v___x_3666_ = lean_nat_dec_lt(v_i_3662_, v___x_3665_);
                if v___x_3666_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3663_);
                    crate::leanh::lean_dec(v_i_3662_);
                    return v_target_3664_;
                } else {
                    v_es_3667_ = lean_array_fget(v_source_3663_, v_i_3662_);
                    v___x_3668_ = crate::leanh::lean_box(0);
                    v_source_3669_ = lean_array_fset(v_source_3663_, v_i_3662_, v___x_3668_);
                    v_target_3670_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3664_, v_es_3667_);
                    v___x_3671_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3672_ = lean_nat_add(v_i_3662_, v___x_3671_);
                    crate::leanh::lean_dec(v_i_3662_);
                    v_i_3662_ = v___x_3672_;
                    v_source_3663_ = v_source_3669_;
                    v_target_3664_ = v_target_3670_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(
    mut v_data_3674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3675_ = lean_array_get_size(v_data_3674_);
    v___x_3676_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3677_ = lean_nat_mul(v___x_3675_, v___x_3676_);
    v___x_3678_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3679_ = crate::leanh::lean_box(0);
    v___x_3680_ = lean_mk_array(v_nbuckets_3677_, v___x_3679_);
    v___x_3681_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(v___x_3678_, v_data_3674_, v___x_3680_);
    return v___x_3681_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(
    mut v_m_3682_: *mut crate::leanh::LeanObject,
    mut v_a_3683_: *mut crate::leanh::LeanObject,
    mut v_b_3684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u64 = 0;
    let mut v___x_3689_: u64 = 0;
    let mut v___x_3690_: u64 = 0;
    let mut v_fold_3691_: u64 = 0;
    let mut v___x_3692_: u64 = 0;
    let mut v___x_3693_: u64 = 0;
    let mut v___x_3694_: u64 = 0;
    let mut v___x_3695_: usize = 0;
    let mut v___x_3696_: usize = 0;
    let mut v___x_3697_: usize = 0;
    let mut v___x_3698_: usize = 0;
    let mut v___x_3699_: usize = 0;
    let mut v_bkt_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: u8 = 0;
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: u8 = 0;
    let mut v_val_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3722_: u8 = 0;
    let mut v_unused_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3685_ = crate::leanh::lean_ctor_get(v_m_3682_, 0);
                v_buckets_3686_ = crate::leanh::lean_ctor_get(v_m_3682_, 1);
                v___x_3687_ = lean_array_get_size(v_buckets_3686_);
                v___x_3688_ = l_Lean_Expr_hash(v_a_3683_);
                v___x_3689_ = 32u64;
                v___x_3690_ = lean_uint64_shift_right(v___x_3688_, v___x_3689_);
                v_fold_3691_ = lean_uint64_xor(v___x_3688_, v___x_3690_);
                v___x_3692_ = 16u64;
                v___x_3693_ = lean_uint64_shift_right(v_fold_3691_, v___x_3692_);
                v___x_3694_ = lean_uint64_xor(v_fold_3691_, v___x_3693_);
                v___x_3695_ = lean_uint64_to_usize(v___x_3694_);
                v___x_3696_ = lean_usize_of_nat(v___x_3687_);
                v___x_3697_ = 1usize;
                v___x_3698_ = lean_usize_sub(v___x_3696_, v___x_3697_);
                v___x_3699_ = lean_usize_land(v___x_3695_, v___x_3698_);
                v_bkt_3700_ = lean_array_uget_borrowed(v_buckets_3686_, v___x_3699_);
                v___x_3701_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_3683_, v_bkt_3700_);
                if v___x_3701_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_3686_);
                    crate::leanh::lean_inc(v_size_3685_);
                    v_isSharedCheck_3722_ = (!crate::leanh::lean_is_exclusive(v_m_3682_)) as u8;
                    if v_isSharedCheck_3722_ == 0 {
                        v_unused_3723_ = crate::leanh::lean_ctor_get(v_m_3682_, 1);
                        crate::leanh::lean_dec(v_unused_3723_);
                        v_unused_3724_ = crate::leanh::lean_ctor_get(v_m_3682_, 0);
                        crate::leanh::lean_dec(v_unused_3724_);
                        v___x_3703_ = v_m_3682_;
                        v_isShared_3704_ = v_isSharedCheck_3722_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3682_);
                        v___x_3703_ = crate::leanh::lean_box(0);
                        v_isShared_3704_ = v_isSharedCheck_3722_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3684_);
                    crate::leanh::lean_dec_ref(v_a_3683_);
                    return v_m_3682_;
                }
            }
            1 => {
                v___x_3705_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3706_ = lean_nat_add(v_size_3685_, v___x_3705_);
                crate::leanh::lean_dec(v_size_3685_);
                crate::leanh::lean_inc(v_bkt_3700_);
                v___x_3707_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3707_, 0, v_a_3683_);
                crate::leanh::lean_ctor_set(v___x_3707_, 1, v_b_3684_);
                crate::leanh::lean_ctor_set(v___x_3707_, 2, v_bkt_3700_);
                v_buckets_x27_3708_ = lean_array_uset(v_buckets_3686_, v___x_3699_, v___x_3707_);
                v___x_3709_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3710_ = lean_nat_mul(v_size_x27_3706_, v___x_3709_);
                v___x_3711_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3712_ = lean_nat_div(v___x_3710_, v___x_3711_);
                crate::leanh::lean_dec(v___x_3710_);
                v___x_3713_ = lean_array_get_size(v_buckets_x27_3708_);
                v___x_3714_ = lean_nat_dec_le(v___x_3712_, v___x_3713_);
                crate::leanh::lean_dec(v___x_3712_);
                if v___x_3714_ == 0 {
                    v_val_3715_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_buckets_x27_3708_);
                    if v_isShared_3704_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3703_, 1, v_val_3715_);
                        crate::leanh::lean_ctor_set(v___x_3703_, 0, v_size_x27_3706_);
                        v___x_3717_ = v___x_3703_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_size_x27_3706_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_val_3715_);
                        v___x_3717_ = v_reuseFailAlloc_3718_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_3704_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3703_, 1, v_buckets_x27_3708_);
                        crate::leanh::lean_ctor_set(v___x_3703_, 0, v_size_x27_3706_);
                        v___x_3720_ = v___x_3703_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3721_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_size_x27_3706_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_buckets_x27_3708_);
                        v___x_3720_ = v_reuseFailAlloc_3721_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3717_;
            }
            3 => {
                return v___x_3720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(
    mut v_op_3725_: *mut crate::leanh::LeanObject,
    mut v_a_3726_: *mut crate::leanh::LeanObject,
    mut v_a_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
    mut v_a_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3749_: u8 = 0;
    let mut v___x_3750_: u8 = 0;
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3764_: u8 = 0;
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3769_: u8 = 0;
    let mut v_fst_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3784_: u8 = 0;
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_isSharedCheck_3786_: u8 = 0;
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut v_a_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3726_) == 5 {
                    v_fn_3741_ = crate::leanh::lean_ctor_get(v_a_3726_, 0);
                    if crate::leanh::lean_obj_tag(v_fn_3741_) == 5 {
                        v_arg_3742_ = crate::leanh::lean_ctor_get(v_a_3726_, 1);
                        v_fn_3743_ = crate::leanh::lean_ctor_get(v_fn_3741_, 0);
                        v_arg_3744_ = crate::leanh::lean_ctor_get(v_fn_3741_, 1);
                        crate::leanh::lean_inc_ref(v_fn_3743_);
                        crate::leanh::lean_inc_ref(v_op_3725_);
                        v___x_3745_ = l_Lean_Meta_isExprDefEq(
                            v_op_3725_, v_fn_3743_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3745_) == 0 {
                            v_a_3746_ = crate::leanh::lean_ctor_get(v___x_3745_, 0);
                            v_isSharedCheck_3787_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3745_)) as u8;
                            if v_isSharedCheck_3787_ == 0 {
                                v___x_3748_ = v___x_3745_;
                                v_isShared_3749_ = v_isSharedCheck_3787_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3746_);
                                crate::leanh::lean_dec(v___x_3745_);
                                v___x_3748_ = crate::leanh::lean_box(0);
                                v_isShared_3749_ = v_isSharedCheck_3787_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_3726_, 2);
                            crate::leanh::lean_dec_ref(v_a_3727_);
                            crate::leanh::lean_dec_ref(v_op_3725_);
                            v_a_3788_ = crate::leanh::lean_ctor_get(v___x_3745_, 0);
                            v_isSharedCheck_3795_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3745_)) as u8;
                            if v_isSharedCheck_3795_ == 0 {
                                v___x_3790_ = v___x_3745_;
                                v_isShared_3791_ = v_isSharedCheck_3795_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3788_);
                                crate::leanh::lean_dec(v___x_3745_);
                                v___x_3790_ = crate::leanh::lean_box(0);
                                v_isShared_3791_ = v_isSharedCheck_3795_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_op_3725_);
                        v_e_3734_ = v_a_3726_;
                        v___y_3735_ = v_a_3727_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_op_3725_);
                    v_e_3734_ = v_a_3726_;
                    v___y_3735_ = v_a_3727_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3736_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_3734_);
                v___x_3737_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v___y_3735_, v_e_3734_, v___x_3736_);
                v___x_3738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3738_, 0, v_e_3734_);
                v___x_3739_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3739_, 0, v___x_3738_);
                crate::leanh::lean_ctor_set(v___x_3739_, 1, v___x_3737_);
                v___x_3740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3740_, 0, v___x_3739_);
                return v___x_3740_;
            }
            2 => {
                v___x_3750_ = (crate::leanh::lean_unbox(v_a_3746_) as u8);
                crate::leanh::lean_dec(v_a_3746_);
                if v___x_3750_ == 0 {
                    crate::leanh::lean_dec_ref(v_op_3725_);
                    v___x_3751_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_a_3726_);
                    v___x_3752_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v_a_3727_, v_a_3726_, v___x_3751_);
                    v___x_3753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3753_, 0, v_a_3726_);
                    v___x_3754_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3754_, 0, v___x_3753_);
                    crate::leanh::lean_ctor_set(v___x_3754_, 1, v___x_3752_);
                    if v_isShared_3749_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3748_, 0, v___x_3754_);
                        v___x_3756_ = v___x_3748_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3757_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3754_);
                        v___x_3756_ = v_reuseFailAlloc_3757_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_arg_3744_);
                    crate::leanh::lean_inc_ref(v_arg_3742_);
                    crate::leanh::lean_del_object(v___x_3748_);
                    crate::leanh::lean_dec_ref_known(v_a_3726_, 2);
                    crate::leanh::lean_inc_ref(v_op_3725_);
                    v___x_3758_ =
                        l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(
                            v_op_3725_,
                            v_arg_3744_,
                            v_a_3727_,
                            v_a_3728_,
                            v_a_3729_,
                            v_a_3730_,
                            v_a_3731_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3758_) == 0 {
                        v_a_3759_ = crate::leanh::lean_ctor_get(v___x_3758_, 0);
                        crate::leanh::lean_inc(v_a_3759_);
                        crate::leanh::lean_dec_ref_known(v___x_3758_, 1);
                        v_fst_3760_ = crate::leanh::lean_ctor_get(v_a_3759_, 0);
                        v_snd_3761_ = crate::leanh::lean_ctor_get(v_a_3759_, 1);
                        v_isSharedCheck_3786_ = (!crate::leanh::lean_is_exclusive(v_a_3759_)) as u8;
                        if v_isSharedCheck_3786_ == 0 {
                            v___x_3763_ = v_a_3759_;
                            v_isShared_3764_ = v_isSharedCheck_3786_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3761_);
                            crate::leanh::lean_inc(v_fst_3760_);
                            crate::leanh::lean_dec(v_a_3759_);
                            v___x_3763_ = crate::leanh::lean_box(0);
                            v_isShared_3764_ = v_isSharedCheck_3786_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_3742_);
                        crate::leanh::lean_dec_ref(v_op_3725_);
                        return v___x_3758_;
                    }
                }
            }
            3 => {
                return v___x_3756_;
            }
            4 => {
                v___x_3765_ =
                    l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(
                        v_op_3725_,
                        v_arg_3742_,
                        v_snd_3761_,
                        v_a_3728_,
                        v_a_3729_,
                        v_a_3730_,
                        v_a_3731_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3765_) == 0 {
                    v_a_3766_ = crate::leanh::lean_ctor_get(v___x_3765_, 0);
                    v_isSharedCheck_3785_ = (!crate::leanh::lean_is_exclusive(v___x_3765_)) as u8;
                    if v_isSharedCheck_3785_ == 0 {
                        v___x_3768_ = v___x_3765_;
                        v_isShared_3769_ = v_isSharedCheck_3785_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3766_);
                        crate::leanh::lean_dec(v___x_3765_);
                        v___x_3768_ = crate::leanh::lean_box(0);
                        v_isShared_3769_ = v_isSharedCheck_3785_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3763_);
                    crate::leanh::lean_dec(v_fst_3760_);
                    return v___x_3765_;
                }
            }
            5 => {
                v_fst_3770_ = crate::leanh::lean_ctor_get(v_a_3766_, 0);
                v_snd_3771_ = crate::leanh::lean_ctor_get(v_a_3766_, 1);
                v_isSharedCheck_3784_ = (!crate::leanh::lean_is_exclusive(v_a_3766_)) as u8;
                if v_isSharedCheck_3784_ == 0 {
                    v___x_3773_ = v_a_3766_;
                    v_isShared_3774_ = v_isSharedCheck_3784_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3771_);
                    crate::leanh::lean_inc(v_fst_3770_);
                    crate::leanh::lean_dec(v_a_3766_);
                    v___x_3773_ = crate::leanh::lean_box(0);
                    v_isShared_3774_ = v_isSharedCheck_3784_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3764_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3763_, 1, v_fst_3770_);
                    v___x_3776_ = v___x_3763_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3783_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_fst_3760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_fst_3770_);
                    v___x_3776_ = v_reuseFailAlloc_3783_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3774_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3773_, 0, v___x_3776_);
                    v___x_3778_ = v___x_3773_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_snd_3771_);
                    v___x_3778_ = v_reuseFailAlloc_3782_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3769_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3768_, 0, v___x_3778_);
                    v___x_3780_ = v___x_3768_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3781_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
                    v___x_3780_ = v_reuseFailAlloc_3781_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3780_;
            }
            10 => {
                if v_isShared_3791_ == 0 {
                    v___x_3793_ = v___x_3790_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3794_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
                    v___x_3793_ = v_reuseFailAlloc_3794_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr___boxed(
    mut v_op_3796_: *mut crate::leanh::LeanObject,
    mut v_a_3797_: *mut crate::leanh::LeanObject,
    mut v_a_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_a_3800_: *mut crate::leanh::LeanObject,
    mut v_a_3801_: *mut crate::leanh::LeanObject,
    mut v_a_3802_: *mut crate::leanh::LeanObject,
    mut v_a_3803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3804_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(
        v_op_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_,
    );
    crate::leanh::lean_dec(v_a_3802_);
    crate::leanh::lean_dec_ref(v_a_3801_);
    crate::leanh::lean_dec(v_a_3800_);
    crate::leanh::lean_dec_ref(v_a_3799_);
    return v_res_3804_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0(
    mut v_00_u03b2_3805_: *mut crate::leanh::LeanObject,
    mut v_m_3806_: *mut crate::leanh::LeanObject,
    mut v_a_3807_: *mut crate::leanh::LeanObject,
    mut v_b_3808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3809_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0___redArg(v_m_3806_, v_a_3807_, v_b_3808_);
    return v___x_3809_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0(
    mut v_00_u03b2_3810_: *mut crate::leanh::LeanObject,
    mut v_a_3811_: *mut crate::leanh::LeanObject,
    mut v_x_3812_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3813_: u8 = 0;
    v___x_3813_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_3811_, v_x_3812_);
    return v___x_3813_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___boxed(
    mut v_00_u03b2_3814_: *mut crate::leanh::LeanObject,
    mut v_a_3815_: *mut crate::leanh::LeanObject,
    mut v_x_3816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3817_: u8 = 0;
    let mut v_r_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3817_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0(v_00_u03b2_3814_, v_a_3815_, v_x_3816_);
    crate::leanh::lean_dec(v_x_3816_);
    crate::leanh::lean_dec_ref(v_a_3815_);
    v_r_3818_ = crate::leanh::lean_box((v_res_3817_) as usize);
    return v_r_3818_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1(
    mut v_00_u03b2_3819_: *mut crate::leanh::LeanObject,
    mut v_data_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_data_3820_);
    return v___x_3821_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3822_: *mut crate::leanh::LeanObject,
    mut v_i_3823_: *mut crate::leanh::LeanObject,
    mut v_source_3824_: *mut crate::leanh::LeanObject,
    mut v_target_3825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3826_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2___redArg(v_i_3823_, v_source_3824_, v_target_3825_);
    return v___x_3826_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3827_: *mut crate::leanh::LeanObject,
    mut v_x_3828_: *mut crate::leanh::LeanObject,
    mut v_x_3829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3830_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3828_, v_x_3829_);
    return v___x_3830_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(
    mut v_varMap_3831_: *mut crate::leanh::LeanObject,
    mut v_a_3832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3837_: u8 = 0;
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut v_e_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3832_) == 0 {
                    v_lhs_3833_ = crate::leanh::lean_ctor_get(v_a_3832_, 0);
                    v_rhs_3834_ = crate::leanh::lean_ctor_get(v_a_3832_, 1);
                    v_isSharedCheck_3843_ = (!crate::leanh::lean_is_exclusive(v_a_3832_)) as u8;
                    if v_isSharedCheck_3843_ == 0 {
                        v___x_3836_ = v_a_3832_;
                        v_isShared_3837_ = v_isSharedCheck_3843_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_rhs_3834_);
                        crate::leanh::lean_inc(v_lhs_3833_);
                        crate::leanh::lean_dec(v_a_3832_);
                        v___x_3836_ = crate::leanh::lean_box(0);
                        v_isShared_3837_ = v_isSharedCheck_3843_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_e_3844_ = crate::leanh::lean_ctor_get(v_a_3832_, 0);
                    v_isSharedCheck_3852_ = (!crate::leanh::lean_is_exclusive(v_a_3832_)) as u8;
                    if v_isSharedCheck_3852_ == 0 {
                        v___x_3846_ = v_a_3832_;
                        v_isShared_3847_ = v_isSharedCheck_3852_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_e_3844_);
                        crate::leanh::lean_dec(v_a_3832_);
                        v___x_3846_ = crate::leanh::lean_box(0);
                        v_isShared_3847_ = v_isSharedCheck_3852_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_varMap_3831_);
                v___x_3838_ =
                    l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(
                        v_varMap_3831_,
                        v_lhs_3833_,
                    );
                v___x_3839_ =
                    l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(
                        v_varMap_3831_,
                        v_rhs_3834_,
                    );
                if v_isShared_3837_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3836_, 1);
                    crate::leanh::lean_ctor_set(v___x_3836_, 1, v___x_3839_);
                    crate::leanh::lean_ctor_set(v___x_3836_, 0, v___x_3838_);
                    v___x_3841_ = v___x_3836_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3838_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 1, v___x_3839_);
                    v___x_3841_ = v_reuseFailAlloc_3842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3841_;
            }
            3 => {
                v___x_3848_ = crate::leanh::lean_apply_1(v_varMap_3831_, v_e_3844_);
                if v_isShared_3847_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3846_, 0);
                    crate::leanh::lean_ctor_set(v___x_3846_, 0, v___x_3848_);
                    v___x_3850_ = v___x_3846_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
                    v___x_3850_ = v_reuseFailAlloc_3851_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5(
    mut v_msg_3853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3854_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3855_ = lean_panic_fn_borrowed(v___x_3854_, v_msg_3853_);
    return v___x_3855_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3859_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__2;
    v___x_3860_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_3861_ = crate::leanh::lean_unsigned_to_nat(163);
    v___x_3862_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__1;
    v___x_3863_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__0;
    v___x_3864_ = l_mkPanicMessageWithDecl(
        v___x_3863_,
        v___x_3862_,
        v___x_3861_,
        v___x_3860_,
        v___x_3859_,
    );
    return v___x_3864_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(
    mut v_a_3865_: *mut crate::leanh::LeanObject,
    mut v_x_3866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3866_) == 0 {
                    v___x_3867_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___closed__3);
                    v___x_3868_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4_spec__5(v___x_3867_);
                    return v___x_3868_;
                } else {
                    v_key_3869_ = crate::leanh::lean_ctor_get(v_x_3866_, 0);
                    v_value_3870_ = crate::leanh::lean_ctor_get(v_x_3866_, 1);
                    v_tail_3871_ = crate::leanh::lean_ctor_get(v_x_3866_, 2);
                    v___x_3872_ = lean_expr_eqv(v_key_3869_, v_a_3865_);
                    if v___x_3872_ == 0 {
                        v_x_3866_ = v_tail_3871_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3870_);
                        return v_value_3870_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4___boxed(
    mut v_a_3874_: *mut crate::leanh::LeanObject,
    mut v_x_3875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3876_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(v_a_3874_, v_x_3875_);
    crate::leanh::lean_dec(v_x_3875_);
    crate::leanh::lean_dec_ref(v_a_3874_);
    return v_res_3876_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(
    mut v_m_3877_: *mut crate::leanh::LeanObject,
    mut v_a_3878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u64 = 0;
    let mut v___x_3882_: u64 = 0;
    let mut v___x_3883_: u64 = 0;
    let mut v_fold_3884_: u64 = 0;
    let mut v___x_3885_: u64 = 0;
    let mut v___x_3886_: u64 = 0;
    let mut v___x_3887_: u64 = 0;
    let mut v___x_3888_: usize = 0;
    let mut v___x_3889_: usize = 0;
    let mut v___x_3890_: usize = 0;
    let mut v___x_3891_: usize = 0;
    let mut v___x_3892_: usize = 0;
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3879_ = crate::leanh::lean_ctor_get(v_m_3877_, 1);
    v___x_3880_ = lean_array_get_size(v_buckets_3879_);
    v___x_3881_ = l_Lean_Expr_hash(v_a_3878_);
    v___x_3882_ = 32u64;
    v___x_3883_ = lean_uint64_shift_right(v___x_3881_, v___x_3882_);
    v_fold_3884_ = lean_uint64_xor(v___x_3881_, v___x_3883_);
    v___x_3885_ = 16u64;
    v___x_3886_ = lean_uint64_shift_right(v_fold_3884_, v___x_3885_);
    v___x_3887_ = lean_uint64_xor(v_fold_3884_, v___x_3886_);
    v___x_3888_ = lean_uint64_to_usize(v___x_3887_);
    v___x_3889_ = lean_usize_of_nat(v___x_3880_);
    v___x_3890_ = 1usize;
    v___x_3891_ = lean_usize_sub(v___x_3889_, v___x_3890_);
    v___x_3892_ = lean_usize_land(v___x_3888_, v___x_3891_);
    v___x_3893_ = lean_array_uget_borrowed(v_buckets_3879_, v___x_3892_);
    v___x_3894_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2_spec__4(v_a_3878_, v___x_3893_);
    return v___x_3894_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2___boxed(
    mut v_m_3895_: *mut crate::leanh::LeanObject,
    mut v_a_3896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3897_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(
            v_m_3895_, v_a_3896_,
        );
    crate::leanh::lean_dec_ref(v_a_3896_);
    crate::leanh::lean_dec_ref(v_m_3895_);
    return v_res_3897_;
}
pub unsafe fn l_Lean_Meta_AC_toACExpr___lam__0(
    mut v___y_3898_: *mut crate::leanh::LeanObject,
    mut v___y_3899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3900_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_AC_toACExpr_spec__2(
            v___y_3898_,
            v___y_3899_,
        );
    return v___x_3900_;
}
pub unsafe fn l_Lean_Meta_AC_toACExpr___lam__0___boxed(
    mut v___y_3901_: *mut crate::leanh::LeanObject,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3903_ = l_Lean_Meta_AC_toACExpr___lam__0(v___y_3901_, v___y_3902_);
    crate::leanh::lean_dec_ref(v___y_3902_);
    crate::leanh::lean_dec_ref(v___y_3901_);
    return v_res_3903_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_AC_toACExpr_spec__4(
    mut v_x_3904_: *mut crate::leanh::LeanObject,
    mut v_x_3905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3905_) == 0 {
                    return v_x_3904_;
                } else {
                    v_key_3906_ = crate::leanh::lean_ctor_get(v_x_3905_, 0);
                    crate::leanh::lean_inc(v_key_3906_);
                    v_tail_3907_ = crate::leanh::lean_ctor_get(v_x_3905_, 2);
                    crate::leanh::lean_inc(v_tail_3907_);
                    crate::leanh::lean_dec_ref_known(v_x_3905_, 3);
                    v___x_3908_ = lean_array_push(v_x_3904_, v_key_3906_);
                    v_x_3904_ = v___x_3908_;
                    v_x_3905_ = v_tail_3907_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(
    mut v_as_3910_: *mut crate::leanh::LeanObject,
    mut v_i_3911_: usize,
    mut v_stop_3912_: usize,
    mut v_b_3913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3914_: u8 = 0;
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: usize = 0;
    let mut v___x_3918_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3914_ = lean_usize_dec_eq(v_i_3911_, v_stop_3912_);
                if v___x_3914_ == 0 {
                    v___x_3915_ = lean_array_uget_borrowed(v_as_3910_, v_i_3911_);
                    crate::leanh::lean_inc(v___x_3915_);
                    v___x_3916_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_AC_toACExpr_spec__4(v_b_3913_, v___x_3915_);
                    v___x_3917_ = 1usize;
                    v___x_3918_ = lean_usize_add(v_i_3911_, v___x_3917_);
                    v_i_3911_ = v___x_3918_;
                    v_b_3913_ = v___x_3916_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3913_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5___boxed(
    mut v_as_3920_: *mut crate::leanh::LeanObject,
    mut v_i_3921_: *mut crate::leanh::LeanObject,
    mut v_stop_3922_: *mut crate::leanh::LeanObject,
    mut v_b_3923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3924_: usize = 0;
    let mut v_stop_boxed_3925_: usize = 0;
    let mut v_res_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3924_ = crate::leanh::lean_unbox_usize(v_i_3921_);
    crate::leanh::lean_dec(v_i_3921_);
    v_stop_boxed_3925_ = crate::leanh::lean_unbox_usize(v_stop_3922_);
    crate::leanh::lean_dec(v_stop_3922_);
    v_res_3926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_as_3920_, v_i_boxed_3924_, v_stop_boxed_3925_, v_b_3923_);
    crate::leanh::lean_dec_ref(v_as_3920_);
    return v_res_3926_;
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(
    mut v_xs_3927_: *mut crate::leanh::LeanObject,
    mut v_j_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3930_: u8 = 0;
    let mut v_one_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: u8 = 0;
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3929_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3930_ = lean_nat_dec_eq(v_j_3928_, v_zero_3929_);
                if v_isZero_3930_ == 1 {
                    crate::leanh::lean_dec(v_j_3928_);
                    return v_xs_3927_;
                } else {
                    v_one_3931_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3932_ = lean_nat_sub(v_j_3928_, v_one_3931_);
                    v___x_3933_ = lean_array_fget_borrowed(v_xs_3927_, v_j_3928_);
                    v___x_3934_ = lean_array_fget_borrowed(v_xs_3927_, v_n_3932_);
                    v___x_3935_ = lean_expr_lt(v___x_3933_, v___x_3934_);
                    if v___x_3935_ == 0 {
                        crate::leanh::lean_dec(v_n_3932_);
                        crate::leanh::lean_dec(v_j_3928_);
                        return v_xs_3927_;
                    } else {
                        v___x_3936_ = lean_array_fswap(v_xs_3927_, v_j_3928_, v_n_3932_);
                        crate::leanh::lean_dec(v_j_3928_);
                        v_xs_3927_ = v___x_3936_;
                        v_j_3928_ = v_n_3932_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1(
    mut v_xs_3938_: *mut crate::leanh::LeanObject,
    mut v_i_3939_: *mut crate::leanh::LeanObject,
    mut v_fuel_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3942_: u8 = 0;
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: u8 = 0;
    let mut v_one_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3941_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3942_ = lean_nat_dec_eq(v_fuel_3940_, v_zero_3941_);
                if v_isZero_3942_ == 1 {
                    crate::leanh::lean_dec(v_fuel_3940_);
                    crate::leanh::lean_dec(v_i_3939_);
                    return v_xs_3938_;
                } else {
                    v___x_3943_ = lean_array_get_size(v_xs_3938_);
                    v___x_3944_ = lean_nat_dec_lt(v_i_3939_, v___x_3943_);
                    if v___x_3944_ == 0 {
                        crate::leanh::lean_dec(v_fuel_3940_);
                        crate::leanh::lean_dec(v_i_3939_);
                        return v_xs_3938_;
                    } else {
                        v_one_3945_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_3946_ = lean_nat_sub(v_fuel_3940_, v_one_3945_);
                        crate::leanh::lean_dec(v_fuel_3940_);
                        crate::leanh::lean_inc(v_i_3939_);
                        v___x_3947_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(v_xs_3938_, v_i_3939_);
                        v___x_3948_ = lean_nat_add(v_i_3939_, v_one_3945_);
                        crate::leanh::lean_dec(v_i_3939_);
                        v_xs_3938_ = v___x_3947_;
                        v_i_3939_ = v___x_3948_;
                        v_fuel_3940_ = v_n_3946_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(
    mut v_a_3950_: *mut crate::leanh::LeanObject,
    mut v_b_3951_: *mut crate::leanh::LeanObject,
    mut v_x_3952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3958_: u8 = 0;
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3952_) == 0 {
                    crate::leanh::lean_dec(v_b_3951_);
                    crate::leanh::lean_dec_ref(v_a_3950_);
                    return v_x_3952_;
                } else {
                    v_key_3953_ = crate::leanh::lean_ctor_get(v_x_3952_, 0);
                    v_value_3954_ = crate::leanh::lean_ctor_get(v_x_3952_, 1);
                    v_tail_3955_ = crate::leanh::lean_ctor_get(v_x_3952_, 2);
                    v_isSharedCheck_3967_ = (!crate::leanh::lean_is_exclusive(v_x_3952_)) as u8;
                    if v_isSharedCheck_3967_ == 0 {
                        v___x_3957_ = v_x_3952_;
                        v_isShared_3958_ = v_isSharedCheck_3967_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3955_);
                        crate::leanh::lean_inc(v_value_3954_);
                        crate::leanh::lean_inc(v_key_3953_);
                        crate::leanh::lean_dec(v_x_3952_);
                        v___x_3957_ = crate::leanh::lean_box(0);
                        v_isShared_3958_ = v_isSharedCheck_3967_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3959_ = lean_expr_eqv(v_key_3953_, v_a_3950_);
                if v___x_3959_ == 0 {
                    v___x_3960_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_3950_, v_b_3951_, v_tail_3955_);
                    if v_isShared_3958_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3957_, 2, v___x_3960_);
                        v___x_3962_ = v___x_3957_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3963_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_key_3953_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_value_3954_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3963_, 2, v___x_3960_);
                        v___x_3962_ = v_reuseFailAlloc_3963_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3954_);
                    crate::leanh::lean_dec(v_key_3953_);
                    if v_isShared_3958_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3957_, 1, v_b_3951_);
                        crate::leanh::lean_ctor_set(v___x_3957_, 0, v_a_3950_);
                        v___x_3965_ = v___x_3957_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3966_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3950_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_b_3951_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3966_, 2, v_tail_3955_);
                        v___x_3965_ = v_reuseFailAlloc_3966_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3962_;
            }
            3 => {
                return v___x_3965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(
    mut v_m_3968_: *mut crate::leanh::LeanObject,
    mut v_a_3969_: *mut crate::leanh::LeanObject,
    mut v_b_3970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3975_: u8 = 0;
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u64 = 0;
    let mut v___x_3978_: u64 = 0;
    let mut v___x_3979_: u64 = 0;
    let mut v_fold_3980_: u64 = 0;
    let mut v___x_3981_: u64 = 0;
    let mut v___x_3982_: u64 = 0;
    let mut v___x_3983_: u64 = 0;
    let mut v___x_3984_: usize = 0;
    let mut v___x_3985_: usize = 0;
    let mut v___x_3986_: usize = 0;
    let mut v___x_3987_: usize = 0;
    let mut v___x_3988_: usize = 0;
    let mut v_bkt_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: u8 = 0;
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: u8 = 0;
    let mut v_val_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4015_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3971_ = crate::leanh::lean_ctor_get(v_m_3968_, 0);
                v_buckets_3972_ = crate::leanh::lean_ctor_get(v_m_3968_, 1);
                v_isSharedCheck_4015_ = (!crate::leanh::lean_is_exclusive(v_m_3968_)) as u8;
                if v_isSharedCheck_4015_ == 0 {
                    v___x_3974_ = v_m_3968_;
                    v_isShared_3975_ = v_isSharedCheck_4015_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3972_);
                    crate::leanh::lean_inc(v_size_3971_);
                    crate::leanh::lean_dec(v_m_3968_);
                    v___x_3974_ = crate::leanh::lean_box(0);
                    v_isShared_3975_ = v_isSharedCheck_4015_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3976_ = lean_array_get_size(v_buckets_3972_);
                v___x_3977_ = l_Lean_Expr_hash(v_a_3969_);
                v___x_3978_ = 32u64;
                v___x_3979_ = lean_uint64_shift_right(v___x_3977_, v___x_3978_);
                v_fold_3980_ = lean_uint64_xor(v___x_3977_, v___x_3979_);
                v___x_3981_ = 16u64;
                v___x_3982_ = lean_uint64_shift_right(v_fold_3980_, v___x_3981_);
                v___x_3983_ = lean_uint64_xor(v_fold_3980_, v___x_3982_);
                v___x_3984_ = lean_uint64_to_usize(v___x_3983_);
                v___x_3985_ = lean_usize_of_nat(v___x_3976_);
                v___x_3986_ = 1usize;
                v___x_3987_ = lean_usize_sub(v___x_3985_, v___x_3986_);
                v___x_3988_ = lean_usize_land(v___x_3984_, v___x_3987_);
                v_bkt_3989_ = lean_array_uget_borrowed(v_buckets_3972_, v___x_3988_);
                v___x_3990_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__0___redArg(v_a_3969_, v_bkt_3989_);
                if v___x_3990_ == 0 {
                    v___x_3991_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3992_ = lean_nat_add(v_size_3971_, v___x_3991_);
                    crate::leanh::lean_dec(v_size_3971_);
                    crate::leanh::lean_inc(v_bkt_3989_);
                    v___x_3993_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3993_, 0, v_a_3969_);
                    crate::leanh::lean_ctor_set(v___x_3993_, 1, v_b_3970_);
                    crate::leanh::lean_ctor_set(v___x_3993_, 2, v_bkt_3989_);
                    v_buckets_x27_3994_ =
                        lean_array_uset(v_buckets_3972_, v___x_3988_, v___x_3993_);
                    v___x_3995_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3996_ = lean_nat_mul(v_size_x27_3992_, v___x_3995_);
                    v___x_3997_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3998_ = lean_nat_div(v___x_3996_, v___x_3997_);
                    crate::leanh::lean_dec(v___x_3996_);
                    v___x_3999_ = lean_array_get_size(v_buckets_x27_3994_);
                    v___x_4000_ = lean_nat_dec_le(v___x_3998_, v___x_3999_);
                    crate::leanh::lean_dec(v___x_3998_);
                    if v___x_4000_ == 0 {
                        v_val_4001_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr_spec__0_spec__1___redArg(v_buckets_x27_3994_);
                        if v_isShared_3975_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3974_, 1, v_val_4001_);
                            crate::leanh::lean_ctor_set(v___x_3974_, 0, v_size_x27_3992_);
                            v___x_4003_ = v___x_3974_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4004_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4004_,
                                0,
                                v_size_x27_3992_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4004_, 1, v_val_4001_);
                            v___x_4003_ = v_reuseFailAlloc_4004_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3975_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3974_, 1, v_buckets_x27_3994_);
                            crate::leanh::lean_ctor_set(v___x_3974_, 0, v_size_x27_3992_);
                            v___x_4006_ = v___x_3974_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4007_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4007_,
                                0,
                                v_size_x27_3992_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4007_,
                                1,
                                v_buckets_x27_3994_,
                            );
                            v___x_4006_ = v_reuseFailAlloc_4007_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3989_);
                    v___x_4008_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4009_ =
                        lean_array_uset(v_buckets_3972_, v___x_3988_, v___x_4008_);
                    v___x_4010_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_3969_, v_b_3970_, v_bkt_3989_);
                    v___x_4011_ = lean_array_uset(v_buckets_x27_4009_, v___x_3988_, v___x_4010_);
                    if v_isShared_3975_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3974_, 1, v___x_4011_);
                        v___x_4013_ = v___x_3974_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4014_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_size_3971_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4014_, 1, v___x_4011_);
                        v___x_4013_ = v_reuseFailAlloc_4014_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4003_;
            }
            3 => {
                return v___x_4006_;
            }
            4 => {
                return v___x_4013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(
    mut v_as_4016_: *mut crate::leanh::LeanObject,
    mut v_i_4017_: usize,
    mut v_stop_4018_: usize,
    mut v_b_4019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4020_: u8 = 0;
    let mut v_size_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: usize = 0;
    let mut v___x_4025_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4020_ = lean_usize_dec_eq(v_i_4017_, v_stop_4018_);
                if v___x_4020_ == 0 {
                    v_size_4021_ = crate::leanh::lean_ctor_get(v_b_4019_, 0);
                    crate::leanh::lean_inc(v_size_4021_);
                    v___x_4022_ = lean_array_uget_borrowed(v_as_4016_, v_i_4017_);
                    crate::leanh::lean_inc(v___x_4022_);
                    v___x_4023_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(v_b_4019_, v___x_4022_, v_size_4021_);
                    v___x_4024_ = 1usize;
                    v___x_4025_ = lean_usize_add(v_i_4017_, v___x_4024_);
                    v_i_4017_ = v___x_4025_;
                    v_b_4019_ = v___x_4023_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4019_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3___boxed(
    mut v_as_4027_: *mut crate::leanh::LeanObject,
    mut v_i_4028_: *mut crate::leanh::LeanObject,
    mut v_stop_4029_: *mut crate::leanh::LeanObject,
    mut v_b_4030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4031_: usize = 0;
    let mut v_stop_boxed_4032_: usize = 0;
    let mut v_res_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4031_ = crate::leanh::lean_unbox_usize(v_i_4028_);
    crate::leanh::lean_dec(v_i_4028_);
    v_stop_boxed_4032_ = crate::leanh::lean_unbox_usize(v_stop_4029_);
    crate::leanh::lean_dec(v_stop_4029_);
    v_res_4033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v_as_4027_, v_i_boxed_4031_, v_stop_boxed_4032_, v_b_4030_);
    crate::leanh::lean_dec_ref(v_as_4027_);
    return v_res_4033_;
}
pub unsafe fn _init_l_Lean_Meta_AC_toACExpr___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4034_ = crate::leanh::lean_box(0);
    v___x_4035_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4036_ = lean_mk_array(v___x_4035_, v___x_4034_);
    return v___x_4036_;
}
pub unsafe fn _init_l_Lean_Meta_AC_toACExpr___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4037_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_toACExpr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_toACExpr___closed__0_once),
        _init_l_Lean_Meta_AC_toACExpr___closed__0,
    );
    v___x_4038_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4039_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4039_, 0, v___x_4038_);
    crate::leanh::lean_ctor_set(v___x_4039_, 1, v___x_4037_);
    return v___x_4039_;
}
pub unsafe fn l_Lean_Meta_AC_toACExpr(
    mut v_op_4040_: *mut crate::leanh::LeanObject,
    mut v_l_4041_: *mut crate::leanh::LeanObject,
    mut v_r_4042_: *mut crate::leanh::LeanObject,
    mut v_a_4043_: *mut crate::leanh::LeanObject,
    mut v_a_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v_a_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v_fst_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___y_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: usize = 0;
    let mut v___x_4080_: usize = 0;
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: usize = 0;
    let mut v___x_4083_: usize = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: usize = 0;
    let mut v___x_4092_: usize = 0;
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: usize = 0;
    let mut v___x_4095_: usize = 0;
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_a_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4102_: u8 = 0;
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_op_4040_);
                v___x_4048_ = l_Lean_mkAppB(v_op_4040_, v_l_4041_, v_r_4042_);
                v___x_4049_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4050_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_AC_toACExpr___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_AC_toACExpr___closed__1_once),
                    _init_l_Lean_Meta_AC_toACExpr___closed__1,
                );
                v___x_4051_ =
                    l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toPreExpr(
                        v_op_4040_,
                        v___x_4048_,
                        v___x_4050_,
                        v_a_4043_,
                        v_a_4044_,
                        v_a_4045_,
                        v_a_4046_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4051_) == 0 {
                    v_a_4052_ = crate::leanh::lean_ctor_get(v___x_4051_, 0);
                    v_isSharedCheck_4098_ = (!crate::leanh::lean_is_exclusive(v___x_4051_)) as u8;
                    if v_isSharedCheck_4098_ == 0 {
                        v___x_4054_ = v___x_4051_;
                        v_isShared_4055_ = v_isSharedCheck_4098_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4052_);
                        crate::leanh::lean_dec(v___x_4051_);
                        v___x_4054_ = crate::leanh::lean_box(0);
                        v_isShared_4055_ = v_isSharedCheck_4098_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4099_ = crate::leanh::lean_ctor_get(v___x_4051_, 0);
                    v_isSharedCheck_4106_ = (!crate::leanh::lean_is_exclusive(v___x_4051_)) as u8;
                    if v_isSharedCheck_4106_ == 0 {
                        v___x_4101_ = v___x_4051_;
                        v_isShared_4102_ = v_isSharedCheck_4106_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4099_);
                        crate::leanh::lean_dec(v___x_4051_);
                        v___x_4101_ = crate::leanh::lean_box(0);
                        v_isShared_4102_ = v_isSharedCheck_4106_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4056_ = crate::leanh::lean_ctor_get(v_a_4052_, 0);
                v_snd_4057_ = crate::leanh::lean_ctor_get(v_a_4052_, 1);
                v_isSharedCheck_4097_ = (!crate::leanh::lean_is_exclusive(v_a_4052_)) as u8;
                if v_isSharedCheck_4097_ == 0 {
                    v___x_4059_ = v_a_4052_;
                    v_isShared_4060_ = v_isSharedCheck_4097_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4057_);
                    crate::leanh::lean_inc(v_fst_4056_);
                    crate::leanh::lean_dec(v_a_4052_);
                    v___x_4059_ = crate::leanh::lean_box(0);
                    v_isShared_4060_ = v_isSharedCheck_4097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_size_4085_ = crate::leanh::lean_ctor_get(v_snd_4057_, 0);
                crate::leanh::lean_inc(v_size_4085_);
                v_buckets_4086_ = crate::leanh::lean_ctor_get(v_snd_4057_, 1);
                crate::leanh::lean_inc_ref(v_buckets_4086_);
                crate::leanh::lean_dec(v_snd_4057_);
                v___x_4087_ = lean_mk_empty_array_with_capacity(v_size_4085_);
                crate::leanh::lean_dec(v_size_4085_);
                v___x_4088_ = lean_array_get_size(v_buckets_4086_);
                v___x_4089_ = lean_nat_dec_lt(v___x_4049_, v___x_4088_);
                if v___x_4089_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_4086_);
                    v___y_4073_ = v___x_4087_;
                    state = 6;
                    continue;
                } else {
                    v___x_4090_ = lean_nat_dec_le(v___x_4088_, v___x_4088_);
                    if v___x_4090_ == 0 {
                        if v___x_4089_ == 0 {
                            crate::leanh::lean_dec_ref(v_buckets_4086_);
                            v___y_4073_ = v___x_4087_;
                            state = 6;
                            continue;
                        } else {
                            v___x_4091_ = 0usize;
                            v___x_4092_ = lean_usize_of_nat(v___x_4088_);
                            v___x_4093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_buckets_4086_, v___x_4091_, v___x_4092_, v___x_4087_);
                            crate::leanh::lean_dec_ref(v_buckets_4086_);
                            v___y_4073_ = v___x_4093_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_4094_ = 0usize;
                        v___x_4095_ = lean_usize_of_nat(v___x_4088_);
                        v___x_4096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__5(v_buckets_4086_, v___x_4094_, v___x_4095_, v___x_4087_);
                        crate::leanh::lean_dec_ref(v_buckets_4086_);
                        v___y_4073_ = v___x_4096_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___f_4064_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_AC_toACExpr___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4064_, 0, v___y_4063_);
                v___x_4065_ =
                    l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_toACExpr_toACExpr(
                        v___f_4064_,
                        v_fst_4056_,
                    );
                if v_isShared_4060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4059_, 1, v___x_4065_);
                    crate::leanh::lean_ctor_set(v___x_4059_, 0, v___y_4062_);
                    v___x_4067_ = v___x_4059_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4071_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___y_4062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4071_, 1, v___x_4065_);
                    v___x_4067_ = v_reuseFailAlloc_4071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4055_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4054_, 0, v___x_4067_);
                    v___x_4069_ = v___x_4054_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4070_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4067_);
                    v___x_4069_ = v_reuseFailAlloc_4070_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4069_;
            }
            6 => {
                v___x_4074_ = lean_array_get_size(v___y_4073_);
                v___x_4075_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1(v___y_4073_, v___x_4049_, v___x_4074_);
                v___x_4076_ = lean_array_get_size(v___x_4075_);
                v___x_4077_ = lean_nat_dec_lt(v___x_4049_, v___x_4076_);
                if v___x_4077_ == 0 {
                    v___y_4062_ = v___x_4075_;
                    v___y_4063_ = v___x_4050_;
                    state = 3;
                    continue;
                } else {
                    v___x_4078_ = lean_nat_dec_le(v___x_4076_, v___x_4076_);
                    if v___x_4078_ == 0 {
                        if v___x_4077_ == 0 {
                            v___y_4062_ = v___x_4075_;
                            v___y_4063_ = v___x_4050_;
                            state = 3;
                            continue;
                        } else {
                            v___x_4079_ = 0usize;
                            v___x_4080_ = lean_usize_of_nat(v___x_4076_);
                            v___x_4081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v___x_4075_, v___x_4079_, v___x_4080_, v___x_4050_);
                            v___y_4062_ = v___x_4075_;
                            v___y_4063_ = v___x_4081_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4082_ = 0usize;
                        v___x_4083_ = lean_usize_of_nat(v___x_4076_);
                        v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_toACExpr_spec__3(v___x_4075_, v___x_4082_, v___x_4083_, v___x_4050_);
                        v___y_4062_ = v___x_4075_;
                        v___y_4063_ = v___x_4084_;
                        state = 3;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_4102_ == 0 {
                    v___x_4104_ = v___x_4101_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
                    v___x_4104_ = v_reuseFailAlloc_4105_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_toACExpr___boxed(
    mut v_op_4107_: *mut crate::leanh::LeanObject,
    mut v_l_4108_: *mut crate::leanh::LeanObject,
    mut v_r_4109_: *mut crate::leanh::LeanObject,
    mut v_a_4110_: *mut crate::leanh::LeanObject,
    mut v_a_4111_: *mut crate::leanh::LeanObject,
    mut v_a_4112_: *mut crate::leanh::LeanObject,
    mut v_a_4113_: *mut crate::leanh::LeanObject,
    mut v_a_4114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4115_ = l_Lean_Meta_AC_toACExpr(
        v_op_4107_, v_l_4108_, v_r_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_,
    );
    crate::leanh::lean_dec(v_a_4113_);
    crate::leanh::lean_dec_ref(v_a_4112_);
    crate::leanh::lean_dec(v_a_4111_);
    crate::leanh::lean_dec_ref(v_a_4110_);
    return v_res_4115_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0(
    mut v_00_u03b2_4116_: *mut crate::leanh::LeanObject,
    mut v_m_4117_: *mut crate::leanh::LeanObject,
    mut v_a_4118_: *mut crate::leanh::LeanObject,
    mut v_b_4119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4120_ =
        l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0___redArg(
            v_m_4117_, v_a_4118_, v_b_4119_,
        );
    return v___x_4120_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0(
    mut v_00_u03b2_4121_: *mut crate::leanh::LeanObject,
    mut v_a_4122_: *mut crate::leanh::LeanObject,
    mut v_b_4123_: *mut crate::leanh::LeanObject,
    mut v_x_4124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4125_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_AC_toACExpr_spec__0_spec__0___redArg(v_a_4122_, v_b_4123_, v_x_4124_);
    return v___x_4125_;
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2(
    mut v_xs_4126_: *mut crate::leanh::LeanObject,
    mut v_j_4127_: *mut crate::leanh::LeanObject,
    mut v_h_4128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4129_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Meta_AC_toACExpr_spec__1_spec__2___redArg(v_xs_4126_, v_j_4127_);
    return v___x_4129_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0(
    mut v_k_4130_: *mut crate::leanh::LeanObject,
    mut v_b_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4135_);
    crate::leanh::lean_inc_ref(v___y_4134_);
    crate::leanh::lean_inc(v___y_4133_);
    crate::leanh::lean_inc_ref(v___y_4132_);
    v___x_4137_ = crate::leanh::lean_apply_6(
        v_k_4130_,
        v_b_4131_,
        v___y_4132_,
        v___y_4133_,
        v___y_4134_,
        v___y_4135_,
        crate::leanh::lean_box(0),
    );
    return v___x_4137_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_4138_: *mut crate::leanh::LeanObject,
    mut v_b_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
    mut v___y_4141_: *mut crate::leanh::LeanObject,
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4145_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0(v_k_4138_, v_b_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
    crate::leanh::lean_dec(v___y_4143_);
    crate::leanh::lean_dec_ref(v___y_4142_);
    crate::leanh::lean_dec(v___y_4141_);
    crate::leanh::lean_dec_ref(v___y_4140_);
    return v_res_4145_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(
    mut v_name_4146_: *mut crate::leanh::LeanObject,
    mut v_bi_4147_: u8,
    mut v_type_4148_: *mut crate::leanh::LeanObject,
    mut v_k_4149_: *mut crate::leanh::LeanObject,
    mut v_kind_4150_: u8,
    mut v___y_4151_: *mut crate::leanh::LeanObject,
    mut v___y_4152_: *mut crate::leanh::LeanObject,
    mut v___y_4153_: *mut crate::leanh::LeanObject,
    mut v___y_4154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4161_: u8 = 0;
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4165_: u8 = 0;
    let mut v_a_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4156_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_4156_, 0, v_k_4149_);
                v___x_4157_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_4146_,
                    v_bi_4147_,
                    v_type_4148_,
                    v___f_4156_,
                    v_kind_4150_,
                    v___y_4151_,
                    v___y_4152_,
                    v___y_4153_,
                    v___y_4154_,
                );
                if crate::leanh::lean_obj_tag(v___x_4157_) == 0 {
                    v_a_4158_ = crate::leanh::lean_ctor_get(v___x_4157_, 0);
                    v_isSharedCheck_4165_ = (!crate::leanh::lean_is_exclusive(v___x_4157_)) as u8;
                    if v_isSharedCheck_4165_ == 0 {
                        v___x_4160_ = v___x_4157_;
                        v_isShared_4161_ = v_isSharedCheck_4165_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4158_);
                        crate::leanh::lean_dec(v___x_4157_);
                        v___x_4160_ = crate::leanh::lean_box(0);
                        v_isShared_4161_ = v_isSharedCheck_4165_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4166_ = crate::leanh::lean_ctor_get(v___x_4157_, 0);
                    v_isSharedCheck_4173_ = (!crate::leanh::lean_is_exclusive(v___x_4157_)) as u8;
                    if v_isSharedCheck_4173_ == 0 {
                        v___x_4168_ = v___x_4157_;
                        v_isShared_4169_ = v_isSharedCheck_4173_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4166_);
                        crate::leanh::lean_dec(v___x_4157_);
                        v___x_4168_ = crate::leanh::lean_box(0);
                        v_isShared_4169_ = v_isSharedCheck_4173_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4161_ == 0 {
                    v___x_4163_ = v___x_4160_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
                    v___x_4163_ = v_reuseFailAlloc_4164_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4163_;
            }
            3 => {
                if v_isShared_4169_ == 0 {
                    v___x_4171_ = v___x_4168_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
                    v___x_4171_ = v_reuseFailAlloc_4172_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg___boxed(
    mut v_name_4174_: *mut crate::leanh::LeanObject,
    mut v_bi_4175_: *mut crate::leanh::LeanObject,
    mut v_type_4176_: *mut crate::leanh::LeanObject,
    mut v_k_4177_: *mut crate::leanh::LeanObject,
    mut v_kind_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4184_: u8 = 0;
    let mut v_kind_boxed_4185_: u8 = 0;
    let mut v_res_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4184_ = (crate::leanh::lean_unbox(v_bi_4175_) as u8);
    v_kind_boxed_4185_ = (crate::leanh::lean_unbox(v_kind_4178_) as u8);
    v_res_4186_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_4174_, v_bi_boxed_4184_, v_type_4176_, v_k_4177_, v_kind_boxed_4185_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
    crate::leanh::lean_dec(v___y_4182_);
    crate::leanh::lean_dec_ref(v___y_4181_);
    crate::leanh::lean_dec(v___y_4180_);
    crate::leanh::lean_dec_ref(v___y_4179_);
    return v_res_4186_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(
    mut v_name_4187_: *mut crate::leanh::LeanObject,
    mut v_type_4188_: *mut crate::leanh::LeanObject,
    mut v_k_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4195_: u8 = 0;
    let mut v___x_4196_: u8 = 0;
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4195_ = 0;
    v___x_4196_ = 0;
    v___x_4197_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_4187_, v___x_4195_, v_type_4188_, v_k_4189_, v___x_4196_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
    return v___x_4197_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg___boxed(
    mut v_name_4198_: *mut crate::leanh::LeanObject,
    mut v_type_4199_: *mut crate::leanh::LeanObject,
    mut v_k_4200_: *mut crate::leanh::LeanObject,
    mut v___y_4201_: *mut crate::leanh::LeanObject,
    mut v___y_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4206_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v_name_4198_, v_type_4199_, v_k_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
    crate::leanh::lean_dec(v___y_4204_);
    crate::leanh::lean_dec_ref(v___y_4203_);
    crate::leanh::lean_dec(v___y_4202_);
    crate::leanh::lean_dec_ref(v___y_4201_);
    return v_res_4206_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_4211_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_v_4212_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_acc_4213_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_4214_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_vars_4215_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_4216_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_val_4217_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_args_4218_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_preContext_4219_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_atoms_4220_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_k_4221_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_00_u03b1_4222_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_u_4223_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_iv_4224_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4225_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4226_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4227_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4228_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4229_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4230_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0(
        v_i_4211_,
        v_v_4212_,
        v_acc_4213_,
        v___x_4214_,
        v_vars_4215_,
        v___x_4216_,
        v_val_4217_,
        v_args_4218_,
        v_preContext_4219_,
        v_atoms_4220_,
        v_k_4221_,
        v_00_u03b1_4222_,
        v_u_4223_,
        v_iv_4224_,
        v___y_4225_,
        v___y_4226_,
        v___y_4227_,
        v___y_4228_,
    );
    crate::leanh::lean_dec(v___y_4228_);
    crate::leanh::lean_dec_ref(v___y_4227_);
    crate::leanh::lean_dec(v___y_4226_);
    crate::leanh::lean_dec_ref(v___y_4225_);
    crate::leanh::lean_dec(v_i_4211_);
    return v_res_4230_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1(
    mut v_preContext_4234_: *mut crate::leanh::LeanObject,
    mut v_atoms_4235_: *mut crate::leanh::LeanObject,
    mut v_i_4236_: *mut crate::leanh::LeanObject,
    mut v_acc_4237_: *mut crate::leanh::LeanObject,
    mut v_vars_4238_: *mut crate::leanh::LeanObject,
    mut v_args_4239_: *mut crate::leanh::LeanObject,
    mut v_k_4240_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4241_: *mut crate::leanh::LeanObject,
    mut v_u_4242_: *mut crate::leanh::LeanObject,
    mut v_v_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
    mut v___y_4245_: *mut crate::leanh::LeanObject,
    mut v___y_4246_: *mut crate::leanh::LeanObject,
    mut v___y_4247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_op_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4280_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_op_4249_ = crate::leanh::lean_ctor_get(v_preContext_4234_, 1);
                v___x_4250_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1;
                v___x_4251_ = lean_array_fget_borrowed(v_atoms_4235_, v_i_4236_);
                v___x_4252_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4253_ = lean_mk_empty_array_with_capacity(v___x_4252_);
                crate::leanh::lean_inc_ref(v_op_4249_);
                crate::leanh::lean_inc_ref(v___x_4253_);
                v___x_4254_ = lean_array_push(v___x_4253_, v_op_4249_);
                crate::leanh::lean_inc(v___x_4251_);
                v___x_4255_ = lean_array_push(v___x_4254_, v___x_4251_);
                v___x_4256_ = l_Lean_Meta_AC_getInstance(
                    v___x_4250_,
                    v___x_4255_,
                    v___y_4244_,
                    v___y_4245_,
                    v___y_4246_,
                    v___y_4247_,
                );
                if crate::leanh::lean_obj_tag(v___x_4256_) == 0 {
                    v_a_4257_ = crate::leanh::lean_ctor_get(v___x_4256_, 0);
                    crate::leanh::lean_inc(v_a_4257_);
                    crate::leanh::lean_dec_ref_known(v___x_4256_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4257_) == 0 {
                        crate::leanh::lean_dec_ref(v___x_4253_);
                        v___x_4258_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4259_ = lean_nat_add(v_i_4236_, v___x_4258_);
                        crate::leanh::lean_dec(v_i_4236_);
                        crate::leanh::lean_inc_ref(v_v_4243_);
                        v___x_4260_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4260_, 0, v_v_4243_);
                        crate::leanh::lean_ctor_set(v___x_4260_, 1, v_a_4257_);
                        v___x_4261_ = lean_array_push(v_acc_4237_, v___x_4260_);
                        v___x_4262_ = lean_array_push(v_vars_4238_, v_v_4243_);
                        crate::leanh::lean_inc(v___x_4251_);
                        v___x_4263_ = lean_array_push(v_args_4239_, v___x_4251_);
                        v___x_4264_ =
                            l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(
                                v_preContext_4234_,
                                v_atoms_4235_,
                                v_k_4240_,
                                v_00_u03b1_4241_,
                                v_u_4242_,
                                v___x_4259_,
                                v___x_4261_,
                                v___x_4262_,
                                v___x_4263_,
                                v___y_4244_,
                                v___y_4245_,
                                v___y_4246_,
                                v___y_4247_,
                            );
                        return v___x_4264_;
                    } else {
                        crate::leanh::lean_inc(v___x_4251_);
                        crate::leanh::lean_inc_ref(v_op_4249_);
                        v_val_4265_ = crate::leanh::lean_ctor_get(v_a_4257_, 0);
                        crate::leanh::lean_inc(v_val_4265_);
                        crate::leanh::lean_dec_ref_known(v_a_4257_, 1);
                        crate::leanh::lean_inc(v_u_4242_);
                        crate::leanh::lean_inc_ref(v_00_u03b1_4241_);
                        crate::leanh::lean_inc_ref(v_v_4243_);
                        v___f_4266_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0___boxed as *mut core::ffi::c_void, 19, 13);
                        crate::leanh::lean_closure_set(v___f_4266_, 0, v_i_4236_);
                        crate::leanh::lean_closure_set(v___f_4266_, 1, v_v_4243_);
                        crate::leanh::lean_closure_set(v___f_4266_, 2, v_acc_4237_);
                        crate::leanh::lean_closure_set(v___f_4266_, 3, v___x_4253_);
                        crate::leanh::lean_closure_set(v___f_4266_, 4, v_vars_4238_);
                        crate::leanh::lean_closure_set(v___f_4266_, 5, v___x_4251_);
                        crate::leanh::lean_closure_set(v___f_4266_, 6, v_val_4265_);
                        crate::leanh::lean_closure_set(v___f_4266_, 7, v_args_4239_);
                        crate::leanh::lean_closure_set(v___f_4266_, 8, v_preContext_4234_);
                        crate::leanh::lean_closure_set(v___f_4266_, 9, v_atoms_4235_);
                        crate::leanh::lean_closure_set(v___f_4266_, 10, v_k_4240_);
                        crate::leanh::lean_closure_set(v___f_4266_, 11, v_00_u03b1_4241_);
                        crate::leanh::lean_closure_set(v___f_4266_, 12, v_u_4242_);
                        v___x_4267_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__3;
                        v___x_4268_ = crate::leanh::lean_box(0);
                        v___x_4269_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4269_, 0, v_u_4242_);
                        crate::leanh::lean_ctor_set(v___x_4269_, 1, v___x_4268_);
                        v___x_4270_ = l_Lean_mkConst(v___x_4250_, v___x_4269_);
                        v___x_4271_ =
                            l_Lean_mkApp3(v___x_4270_, v_00_u03b1_4241_, v_op_4249_, v_v_4243_);
                        v___x_4272_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v___x_4267_, v___x_4271_, v___f_4266_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
                        return v___x_4272_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_4253_);
                    crate::leanh::lean_dec_ref(v_v_4243_);
                    crate::leanh::lean_dec(v_u_4242_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_4241_);
                    crate::leanh::lean_dec_ref(v_k_4240_);
                    crate::leanh::lean_dec_ref(v_args_4239_);
                    crate::leanh::lean_dec_ref(v_vars_4238_);
                    crate::leanh::lean_dec_ref(v_acc_4237_);
                    crate::leanh::lean_dec(v_i_4236_);
                    crate::leanh::lean_dec_ref(v_atoms_4235_);
                    crate::leanh::lean_dec_ref(v_preContext_4234_);
                    v_a_4273_ = crate::leanh::lean_ctor_get(v___x_4256_, 0);
                    v_isSharedCheck_4280_ = (!crate::leanh::lean_is_exclusive(v___x_4256_)) as u8;
                    if v_isSharedCheck_4280_ == 0 {
                        v___x_4275_ = v___x_4256_;
                        v_isShared_4276_ = v_isSharedCheck_4280_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4273_);
                        crate::leanh::lean_dec(v___x_4256_);
                        v___x_4275_ = crate::leanh::lean_box(0);
                        v_isShared_4276_ = v_isSharedCheck_4280_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4276_ == 0 {
                    v___x_4278_ = v___x_4275_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4279_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
                    v___x_4278_ = v_reuseFailAlloc_4279_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___boxed(
    mut v_preContext_4281_: *mut crate::leanh::LeanObject,
    mut v_atoms_4282_: *mut crate::leanh::LeanObject,
    mut v_i_4283_: *mut crate::leanh::LeanObject,
    mut v_acc_4284_: *mut crate::leanh::LeanObject,
    mut v_vars_4285_: *mut crate::leanh::LeanObject,
    mut v_args_4286_: *mut crate::leanh::LeanObject,
    mut v_k_4287_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4288_: *mut crate::leanh::LeanObject,
    mut v_u_4289_: *mut crate::leanh::LeanObject,
    mut v_v_4290_: *mut crate::leanh::LeanObject,
    mut v___y_4291_: *mut crate::leanh::LeanObject,
    mut v___y_4292_: *mut crate::leanh::LeanObject,
    mut v___y_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4296_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1(
        v_preContext_4281_,
        v_atoms_4282_,
        v_i_4283_,
        v_acc_4284_,
        v_vars_4285_,
        v_args_4286_,
        v_k_4287_,
        v_00_u03b1_4288_,
        v_u_4289_,
        v_v_4290_,
        v___y_4291_,
        v___y_4292_,
        v___y_4293_,
        v___y_4294_,
    );
    crate::leanh::lean_dec(v___y_4294_);
    crate::leanh::lean_dec_ref(v___y_4293_);
    crate::leanh::lean_dec(v___y_4292_);
    crate::leanh::lean_dec_ref(v___y_4291_);
    return v_res_4296_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(
    mut v_preContext_4300_: *mut crate::leanh::LeanObject,
    mut v_atoms_4301_: *mut crate::leanh::LeanObject,
    mut v_k_4302_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4303_: *mut crate::leanh::LeanObject,
    mut v_u_4304_: *mut crate::leanh::LeanObject,
    mut v_i_4305_: *mut crate::leanh::LeanObject,
    mut v_acc_4306_: *mut crate::leanh::LeanObject,
    mut v_vars_4307_: *mut crate::leanh::LeanObject,
    mut v_args_4308_: *mut crate::leanh::LeanObject,
    mut v_a_4309_: *mut crate::leanh::LeanObject,
    mut v_a_4310_: *mut crate::leanh::LeanObject,
    mut v_a_4311_: *mut crate::leanh::LeanObject,
    mut v_a_4312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: u8 = 0;
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: u8 = 0;
    let mut v___x_4319_: u8 = 0;
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4329_: u8 = 0;
    let mut v___f_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4314_ = lean_array_get_size(v_atoms_4301_);
                v___x_4315_ = lean_nat_dec_lt(v_i_4305_, v___x_4314_);
                if v___x_4315_ == 0 {
                    crate::leanh::lean_dec(v_i_4305_);
                    crate::leanh::lean_dec(v_u_4304_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_4303_);
                    crate::leanh::lean_dec_ref(v_atoms_4301_);
                    crate::leanh::lean_dec_ref(v_preContext_4300_);
                    crate::leanh::lean_inc(v_a_4312_);
                    crate::leanh::lean_inc_ref(v_a_4311_);
                    crate::leanh::lean_inc(v_a_4310_);
                    crate::leanh::lean_inc_ref(v_a_4309_);
                    v___x_4316_ = crate::leanh::lean_apply_6(
                        v_k_4302_,
                        v_acc_4306_,
                        v_a_4309_,
                        v_a_4310_,
                        v_a_4311_,
                        v_a_4312_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4316_) == 0 {
                        v_a_4317_ = crate::leanh::lean_ctor_get(v___x_4316_, 0);
                        crate::leanh::lean_inc(v_a_4317_);
                        crate::leanh::lean_dec_ref_known(v___x_4316_, 1);
                        v___x_4318_ = 1;
                        v___x_4319_ = 1;
                        v___x_4320_ = l_Lean_Meta_mkLambdaFVars(
                            v_vars_4307_,
                            v_a_4317_,
                            v___x_4315_,
                            v___x_4318_,
                            v___x_4315_,
                            v___x_4318_,
                            v___x_4319_,
                            v_a_4309_,
                            v_a_4310_,
                            v_a_4311_,
                            v_a_4312_,
                        );
                        crate::leanh::lean_dec_ref(v_vars_4307_);
                        if crate::leanh::lean_obj_tag(v___x_4320_) == 0 {
                            v_a_4321_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                            v_isSharedCheck_4329_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                            if v_isSharedCheck_4329_ == 0 {
                                v___x_4323_ = v___x_4320_;
                                v_isShared_4324_ = v_isSharedCheck_4329_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4321_);
                                crate::leanh::lean_dec(v___x_4320_);
                                v___x_4323_ = crate::leanh::lean_box(0);
                                v_isShared_4324_ = v_isSharedCheck_4329_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_args_4308_);
                            return v___x_4320_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_4308_);
                        crate::leanh::lean_dec_ref(v_vars_4307_);
                        return v___x_4316_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_00_u03b1_4303_);
                    v___f_4330_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___boxed as *mut core::ffi::c_void, 15, 9);
                    crate::leanh::lean_closure_set(v___f_4330_, 0, v_preContext_4300_);
                    crate::leanh::lean_closure_set(v___f_4330_, 1, v_atoms_4301_);
                    crate::leanh::lean_closure_set(v___f_4330_, 2, v_i_4305_);
                    crate::leanh::lean_closure_set(v___f_4330_, 3, v_acc_4306_);
                    crate::leanh::lean_closure_set(v___f_4330_, 4, v_vars_4307_);
                    crate::leanh::lean_closure_set(v___f_4330_, 5, v_args_4308_);
                    crate::leanh::lean_closure_set(v___f_4330_, 6, v_k_4302_);
                    crate::leanh::lean_closure_set(v___f_4330_, 7, v_00_u03b1_4303_);
                    crate::leanh::lean_closure_set(v___f_4330_, 8, v_u_4304_);
                    v___x_4331_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___closed__1;
                    v___x_4332_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v___x_4331_, v_00_u03b1_4303_, v___f_4330_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_);
                    return v___x_4332_;
                }
            }
            1 => {
                v___x_4325_ = l_Lean_mkAppN(v_a_4321_, v_args_4308_);
                crate::leanh::lean_dec_ref(v_args_4308_);
                if v_isShared_4324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4323_, 0, v___x_4325_);
                    v___x_4327_ = v___x_4323_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4325_);
                    v___x_4327_ = v_reuseFailAlloc_4328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__0(
    mut v_i_4333_: *mut crate::leanh::LeanObject,
    mut v_v_4334_: *mut crate::leanh::LeanObject,
    mut v_acc_4335_: *mut crate::leanh::LeanObject,
    mut v___x_4336_: *mut crate::leanh::LeanObject,
    mut v_vars_4337_: *mut crate::leanh::LeanObject,
    mut v___x_4338_: *mut crate::leanh::LeanObject,
    mut v_val_4339_: *mut crate::leanh::LeanObject,
    mut v_args_4340_: *mut crate::leanh::LeanObject,
    mut v_preContext_4341_: *mut crate::leanh::LeanObject,
    mut v_atoms_4342_: *mut crate::leanh::LeanObject,
    mut v_k_4343_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4344_: *mut crate::leanh::LeanObject,
    mut v_u_4345_: *mut crate::leanh::LeanObject,
    mut v_iv_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
    mut v___y_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
    mut v___y_4350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4352_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4353_ = lean_nat_add(v_i_4333_, v___x_4352_);
    crate::leanh::lean_inc_ref(v_iv_4346_);
    v___x_4354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4354_, 0, v_iv_4346_);
    crate::leanh::lean_inc_ref(v_v_4334_);
    v___x_4355_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4355_, 0, v_v_4334_);
    crate::leanh::lean_ctor_set(v___x_4355_, 1, v___x_4354_);
    v___x_4356_ = lean_array_push(v_acc_4335_, v___x_4355_);
    crate::leanh::lean_inc_ref(v___x_4336_);
    v___x_4357_ = lean_array_push(v___x_4336_, v_v_4334_);
    v___x_4358_ = lean_array_push(v___x_4357_, v_iv_4346_);
    v___x_4359_ = l_Array_append___redArg(v_vars_4337_, v___x_4358_);
    crate::leanh::lean_dec_ref(v___x_4358_);
    v___x_4360_ = lean_array_push(v___x_4336_, v___x_4338_);
    v___x_4361_ = lean_array_push(v___x_4360_, v_val_4339_);
    v___x_4362_ = l_Array_append___redArg(v_args_4340_, v___x_4361_);
    crate::leanh::lean_dec_ref(v___x_4361_);
    v___x_4363_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(
        v_preContext_4341_,
        v_atoms_4342_,
        v_k_4343_,
        v_00_u03b1_4344_,
        v_u_4345_,
        v___x_4353_,
        v___x_4356_,
        v___x_4359_,
        v___x_4362_,
        v___y_4347_,
        v___y_4348_,
        v___y_4349_,
        v___y_4350_,
    );
    return v___x_4363_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___boxed(
    mut v_preContext_4364_: *mut crate::leanh::LeanObject,
    mut v_atoms_4365_: *mut crate::leanh::LeanObject,
    mut v_k_4366_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4367_: *mut crate::leanh::LeanObject,
    mut v_u_4368_: *mut crate::leanh::LeanObject,
    mut v_i_4369_: *mut crate::leanh::LeanObject,
    mut v_acc_4370_: *mut crate::leanh::LeanObject,
    mut v_vars_4371_: *mut crate::leanh::LeanObject,
    mut v_args_4372_: *mut crate::leanh::LeanObject,
    mut v_a_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
    mut v_a_4375_: *mut crate::leanh::LeanObject,
    mut v_a_4376_: *mut crate::leanh::LeanObject,
    mut v_a_4377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4378_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(
        v_preContext_4364_,
        v_atoms_4365_,
        v_k_4366_,
        v_00_u03b1_4367_,
        v_u_4368_,
        v_i_4369_,
        v_acc_4370_,
        v_vars_4371_,
        v_args_4372_,
        v_a_4373_,
        v_a_4374_,
        v_a_4375_,
        v_a_4376_,
    );
    crate::leanh::lean_dec(v_a_4376_);
    crate::leanh::lean_dec_ref(v_a_4375_);
    crate::leanh::lean_dec(v_a_4374_);
    crate::leanh::lean_dec_ref(v_a_4373_);
    return v_res_4378_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0(
    mut v_00_u03b1_4379_: *mut crate::leanh::LeanObject,
    mut v_name_4380_: *mut crate::leanh::LeanObject,
    mut v_bi_4381_: u8,
    mut v_type_4382_: *mut crate::leanh::LeanObject,
    mut v_k_4383_: *mut crate::leanh::LeanObject,
    mut v_kind_4384_: u8,
    mut v___y_4385_: *mut crate::leanh::LeanObject,
    mut v___y_4386_: *mut crate::leanh::LeanObject,
    mut v___y_4387_: *mut crate::leanh::LeanObject,
    mut v___y_4388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4390_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___redArg(v_name_4380_, v_bi_4381_, v_type_4382_, v_k_4383_, v_kind_4384_, v___y_4385_, v___y_4386_, v___y_4387_, v___y_4388_);
    return v___x_4390_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0___boxed(
    mut v_00_u03b1_4391_: *mut crate::leanh::LeanObject,
    mut v_name_4392_: *mut crate::leanh::LeanObject,
    mut v_bi_4393_: *mut crate::leanh::LeanObject,
    mut v_type_4394_: *mut crate::leanh::LeanObject,
    mut v_k_4395_: *mut crate::leanh::LeanObject,
    mut v_kind_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
    mut v___y_4398_: *mut crate::leanh::LeanObject,
    mut v___y_4399_: *mut crate::leanh::LeanObject,
    mut v___y_4400_: *mut crate::leanh::LeanObject,
    mut v___y_4401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4402_: u8 = 0;
    let mut v_kind_boxed_4403_: u8 = 0;
    let mut v_res_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4402_ = (crate::leanh::lean_unbox(v_bi_4393_) as u8);
    v_kind_boxed_4403_ = (crate::leanh::lean_unbox(v_kind_4396_) as u8);
    v_res_4404_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0_spec__0(v_00_u03b1_4391_, v_name_4392_, v_bi_boxed_4402_, v_type_4394_, v_k_4395_, v_kind_boxed_4403_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
    crate::leanh::lean_dec(v___y_4400_);
    crate::leanh::lean_dec_ref(v___y_4399_);
    crate::leanh::lean_dec(v___y_4398_);
    crate::leanh::lean_dec_ref(v___y_4397_);
    return v_res_4404_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0(
    mut v_00_u03b1_4405_: *mut crate::leanh::LeanObject,
    mut v_name_4406_: *mut crate::leanh::LeanObject,
    mut v_type_4407_: *mut crate::leanh::LeanObject,
    mut v_k_4408_: *mut crate::leanh::LeanObject,
    mut v___y_4409_: *mut crate::leanh::LeanObject,
    mut v___y_4410_: *mut crate::leanh::LeanObject,
    mut v___y_4411_: *mut crate::leanh::LeanObject,
    mut v___y_4412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4414_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___redArg(v_name_4406_, v_type_4407_, v_k_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
    return v___x_4414_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0___boxed(
    mut v_00_u03b1_4415_: *mut crate::leanh::LeanObject,
    mut v_name_4416_: *mut crate::leanh::LeanObject,
    mut v_type_4417_: *mut crate::leanh::LeanObject,
    mut v_k_4418_: *mut crate::leanh::LeanObject,
    mut v___y_4419_: *mut crate::leanh::LeanObject,
    mut v___y_4420_: *mut crate::leanh::LeanObject,
    mut v___y_4421_: *mut crate::leanh::LeanObject,
    mut v___y_4422_: *mut crate::leanh::LeanObject,
    mut v___y_4423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4424_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go_spec__0(v_00_u03b1_4415_, v_name_4416_, v_type_4417_, v_k_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_);
    crate::leanh::lean_dec(v___y_4422_);
    crate::leanh::lean_dec_ref(v___y_4421_);
    crate::leanh::lean_dec(v___y_4420_);
    crate::leanh::lean_dec_ref(v___y_4419_);
    return v_res_4424_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter___redArg(
    mut v_____do__lift_4425_: *mut crate::leanh::LeanObject,
    mut v_h__1_4426_: *mut crate::leanh::LeanObject,
    mut v_h__2_4427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_4425_) == 0 {
        let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4427_);
        v___x_4428_ = crate::leanh::lean_box(0);
        v___x_4429_ = crate::leanh::lean_apply_1(v_h__1_4426_, v___x_4428_);
        return v___x_4429_;
    } else {
        let mut v_val_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4426_);
        v_val_4430_ = crate::leanh::lean_ctor_get(v_____do__lift_4425_, 0);
        crate::leanh::lean_inc(v_val_4430_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_4425_, 1);
        v___x_4431_ = crate::leanh::lean_apply_1(v_h__2_4427_, v_val_4430_);
        return v___x_4431_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_match__1_splitter(
    mut v_motive_4432_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_4433_: *mut crate::leanh::LeanObject,
    mut v_h__1_4434_: *mut crate::leanh::LeanObject,
    mut v_h__2_4435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_4433_) == 0 {
        let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4435_);
        v___x_4436_ = crate::leanh::lean_box(0);
        v___x_4437_ = crate::leanh::lean_apply_1(v_h__1_4434_, v___x_4436_);
        return v___x_4437_;
    } else {
        let mut v_val_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4434_);
        v_val_4438_ = crate::leanh::lean_ctor_get(v_____do__lift_4433_, 0);
        crate::leanh::lean_inc(v_val_4438_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_4433_, 1);
        v___x_4439_ = crate::leanh::lean_apply_1(v_h__2_4435_, v_val_4438_);
        return v___x_4439_;
    }
}
pub unsafe fn l_Lean_Meta_AC_abstractAtoms(
    mut v_preContext_4442_: *mut crate::leanh::LeanObject,
    mut v_atoms_4443_: *mut crate::leanh::LeanObject,
    mut v_k_4444_: *mut crate::leanh::LeanObject,
    mut v_a_4445_: *mut crate::leanh::LeanObject,
    mut v_a_4446_: *mut crate::leanh::LeanObject,
    mut v_a_4447_: *mut crate::leanh::LeanObject,
    mut v_a_4448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4450_ = l_Lean_instInhabitedExpr;
                v___x_4451_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4452_ = lean_array_get_borrowed(v___x_4450_, v_atoms_4443_, v___x_4451_);
                crate::leanh::lean_inc(v_a_4448_);
                crate::leanh::lean_inc_ref(v_a_4447_);
                crate::leanh::lean_inc(v_a_4446_);
                crate::leanh::lean_inc_ref(v_a_4445_);
                crate::leanh::lean_inc(v___x_4452_);
                v___x_4453_ =
                    lean_infer_type(v___x_4452_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_);
                if crate::leanh::lean_obj_tag(v___x_4453_) == 0 {
                    v_a_4454_ = crate::leanh::lean_ctor_get(v___x_4453_, 0);
                    crate::leanh::lean_inc_n(v_a_4454_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4453_, 1);
                    v___x_4455_ =
                        l_Lean_Meta_getLevel(v_a_4454_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_);
                    if crate::leanh::lean_obj_tag(v___x_4455_) == 0 {
                        v_a_4456_ = crate::leanh::lean_ctor_get(v___x_4455_, 0);
                        crate::leanh::lean_inc(v_a_4456_);
                        crate::leanh::lean_dec_ref_known(v___x_4455_, 1);
                        v___x_4457_ = l_Lean_Meta_AC_abstractAtoms___closed__0;
                        v___x_4458_ =
                            l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go(
                                v_preContext_4442_,
                                v_atoms_4443_,
                                v_k_4444_,
                                v_a_4454_,
                                v_a_4456_,
                                v___x_4451_,
                                v___x_4457_,
                                v___x_4457_,
                                v___x_4457_,
                                v_a_4445_,
                                v_a_4446_,
                                v_a_4447_,
                                v_a_4448_,
                            );
                        return v___x_4458_;
                    } else {
                        crate::leanh::lean_dec(v_a_4454_);
                        crate::leanh::lean_dec_ref(v_k_4444_);
                        crate::leanh::lean_dec_ref(v_atoms_4443_);
                        crate::leanh::lean_dec_ref(v_preContext_4442_);
                        v_a_4459_ = crate::leanh::lean_ctor_get(v___x_4455_, 0);
                        v_isSharedCheck_4466_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4455_)) as u8;
                        if v_isSharedCheck_4466_ == 0 {
                            v___x_4461_ = v___x_4455_;
                            v_isShared_4462_ = v_isSharedCheck_4466_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4459_);
                            crate::leanh::lean_dec(v___x_4455_);
                            v___x_4461_ = crate::leanh::lean_box(0);
                            v_isShared_4462_ = v_isSharedCheck_4466_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_4444_);
                    crate::leanh::lean_dec_ref(v_atoms_4443_);
                    crate::leanh::lean_dec_ref(v_preContext_4442_);
                    return v___x_4453_;
                }
            }
            1 => {
                if v_isShared_4462_ == 0 {
                    v___x_4464_ = v___x_4461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
                    v___x_4464_ = v_reuseFailAlloc_4465_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4464_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_abstractAtoms___boxed(
    mut v_preContext_4467_: *mut crate::leanh::LeanObject,
    mut v_atoms_4468_: *mut crate::leanh::LeanObject,
    mut v_k_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
    mut v_a_4472_: *mut crate::leanh::LeanObject,
    mut v_a_4473_: *mut crate::leanh::LeanObject,
    mut v_a_4474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4475_ = l_Lean_Meta_AC_abstractAtoms(
        v_preContext_4467_,
        v_atoms_4468_,
        v_k_4469_,
        v_a_4470_,
        v_a_4471_,
        v_a_4472_,
        v_a_4473_,
    );
    crate::leanh::lean_dec(v_a_4473_);
    crate::leanh::lean_dec_ref(v_a_4472_);
    crate::leanh::lean_dec(v_a_4471_);
    crate::leanh::lean_dec_ref(v_a_4470_);
    return v_res_4475_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(
    mut v___x_4481_: *mut crate::leanh::LeanObject,
    mut v___x_4482_: *mut crate::leanh::LeanObject,
    mut v_tp_4483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4484_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2;
    v___x_4485_ = l_Lean_mkConst(v___x_4484_, v___x_4481_);
    v___x_4486_ = l_Lean_Expr_app___override(v___x_4482_, v_tp_4483_);
    v___x_4487_ = l_Lean_Expr_app___override(v___x_4485_, v___x_4486_);
    return v___x_4487_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(
    mut v___x_4492_: *mut crate::leanh::LeanObject,
    mut v___x_4493_: *mut crate::leanh::LeanObject,
    mut v___x_4494_: *mut crate::leanh::LeanObject,
    mut v_tp_4495_: *mut crate::leanh::LeanObject,
    mut v_v_4496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4497_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1;
    v___x_4498_ = l_Lean_mkConst(v___x_4497_, v___x_4492_);
    crate::leanh::lean_inc_ref(v_tp_4495_);
    v___x_4499_ = l_Lean_Expr_app___override(v___x_4493_, v_tp_4495_);
    v___x_4500_ = l_Lean_mkAppB(v___x_4494_, v_tp_4495_, v_v_4496_);
    v___x_4501_ = l_Lean_mkAppB(v___x_4498_, v___x_4499_, v___x_4500_);
    return v___x_4501_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0;
    v___x_4509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__2;
    v___x_4510_ = l_Lean_mkConst(v___x_4509_, v___x_4508_);
    return v___x_4510_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0;
    v___x_4522_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0___closed__2;
    v___x_4523_ = l_Lean_mkConst(v___x_4522_, v___x_4521_);
    return v___x_4523_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0;
    v___x_4529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__11;
    v___x_4530_ = l_Lean_mkConst(v___x_4529_, v___x_4528_);
    return v___x_4530_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0;
    v___x_4532_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1___closed__1;
    v___x_4533_ = l_Lean_mkConst(v___x_4532_, v___x_4531_);
    return v___x_4533_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(
    mut v_u_4534_: *mut crate::leanh::LeanObject,
    mut v_preContext_4535_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4536_: *mut crate::leanh::LeanObject,
    mut v_sz_4537_: usize,
    mut v_i_4538_: usize,
    mut v_bs_4539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4541_: u8 = 0;
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4548_: u8 = 0;
    let mut v_op_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: usize = 0;
    let mut v___x_4563_: usize = 0;
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeutralClass_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4541_ = lean_usize_dec_lt(v_i_4538_, v_sz_4537_);
                if v___x_4541_ == 0 {
                    crate::leanh::lean_dec_ref(v_00_u03b1_4536_);
                    crate::leanh::lean_dec_ref(v_preContext_4535_);
                    crate::leanh::lean_dec(v_u_4534_);
                    v___x_4542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4542_, 0, v_bs_4539_);
                    return v___x_4542_;
                } else {
                    v_v_4543_ = lean_array_uget(v_bs_4539_, v_i_4538_);
                    v_fst_4544_ = crate::leanh::lean_ctor_get(v_v_4543_, 0);
                    v_snd_4545_ = crate::leanh::lean_ctor_get(v_v_4543_, 1);
                    v_isSharedCheck_4578_ = (!crate::leanh::lean_is_exclusive(v_v_4543_)) as u8;
                    if v_isSharedCheck_4578_ == 0 {
                        v___x_4547_ = v_v_4543_;
                        v_isShared_4548_ = v_isSharedCheck_4578_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4545_);
                        crate::leanh::lean_inc(v_fst_4544_);
                        crate::leanh::lean_dec(v_v_4543_);
                        v___x_4547_ = crate::leanh::lean_box(0);
                        v_isShared_4548_ = v_isSharedCheck_4578_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_op_4549_ = crate::leanh::lean_ctor_get(v_preContext_4535_, 1);
                v___x_4550_ = crate::leanh::lean_box(0);
                v___x_4551_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
                v___x_4552_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_4553_ = lean_array_uset(v_bs_4539_, v_i_4538_, v___x_4552_);
                v___x_4554_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1;
                crate::leanh::lean_inc(v_u_4534_);
                if v_isShared_4548_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4547_, 1);
                    crate::leanh::lean_ctor_set(v___x_4547_, 1, v___x_4550_);
                    crate::leanh::lean_ctor_set(v___x_4547_, 0, v_u_4534_);
                    v___x_4556_ = v___x_4547_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4577_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_u_4534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 1, v___x_4550_);
                    v___x_4556_ = v_reuseFailAlloc_4577_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_4556_);
                v___x_4566_ = l_Lean_mkConst(v___x_4554_, v___x_4556_);
                crate::leanh::lean_inc(v_fst_4544_);
                crate::leanh::lean_inc_ref(v_op_4549_);
                crate::leanh::lean_inc_ref(v_00_u03b1_4536_);
                v_isNeutralClass_4567_ =
                    l_Lean_mkApp3(v___x_4566_, v_00_u03b1_4536_, v_op_4549_, v_fst_4544_);
                if crate::leanh::lean_obj_tag(v_snd_4545_) == 0 {
                    v___x_4568_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9);
                    v___x_4569_ = l_Lean_Expr_app___override(v___x_4551_, v_isNeutralClass_4567_);
                    v___x_4570_ = l_Lean_Expr_app___override(v___x_4568_, v___x_4569_);
                    v___y_4558_ = v___x_4570_;
                    state = 3;
                    continue;
                } else {
                    v_val_4571_ = crate::leanh::lean_ctor_get(v_snd_4545_, 0);
                    crate::leanh::lean_inc(v_val_4571_);
                    crate::leanh::lean_dec_ref_known(v_snd_4545_, 1);
                    v___x_4572_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
                    v___x_4573_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13);
                    crate::leanh::lean_inc_ref(v_isNeutralClass_4567_);
                    v___x_4574_ = l_Lean_Expr_app___override(v___x_4551_, v_isNeutralClass_4567_);
                    v___x_4575_ = l_Lean_mkAppB(v___x_4572_, v_isNeutralClass_4567_, v_val_4571_);
                    v___x_4576_ = l_Lean_mkAppB(v___x_4573_, v___x_4574_, v___x_4575_);
                    v___y_4558_ = v___x_4576_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4559_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8;
                v___x_4560_ = l_Lean_mkConst(v___x_4559_, v___x_4556_);
                crate::leanh::lean_inc_ref(v_op_4549_);
                crate::leanh::lean_inc_ref(v_00_u03b1_4536_);
                v___x_4561_ = l_Lean_mkApp4(
                    v___x_4560_,
                    v_00_u03b1_4536_,
                    v_op_4549_,
                    v_fst_4544_,
                    v___y_4558_,
                );
                v___x_4562_ = 1usize;
                v___x_4563_ = lean_usize_add(v_i_4538_, v___x_4562_);
                v___x_4564_ = lean_array_uset(v_bs_x27_4553_, v_i_4538_, v___x_4561_);
                v_i_4538_ = v___x_4563_;
                v_bs_4539_ = v___x_4564_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___boxed(
    mut v_u_4579_: *mut crate::leanh::LeanObject,
    mut v_preContext_4580_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4581_: *mut crate::leanh::LeanObject,
    mut v_sz_4582_: *mut crate::leanh::LeanObject,
    mut v_i_4583_: *mut crate::leanh::LeanObject,
    mut v_bs_4584_: *mut crate::leanh::LeanObject,
    mut v___y_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4586_: usize = 0;
    let mut v_i_boxed_4587_: usize = 0;
    let mut v_res_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4586_ = crate::leanh::lean_unbox_usize(v_sz_4582_);
    crate::leanh::lean_dec(v_sz_4582_);
    v_i_boxed_4587_ = crate::leanh::lean_unbox_usize(v_i_4583_);
    crate::leanh::lean_dec(v_i_4583_);
    v_res_4588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_4579_, v_preContext_4580_, v_00_u03b1_4581_, v_sz_boxed_4586_, v_i_boxed_4587_, v_bs_4584_);
    return v_res_4588_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(
    mut v_u_4589_: *mut crate::leanh::LeanObject,
    mut v_preContext_4590_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4591_: *mut crate::leanh::LeanObject,
    mut v_sz_4592_: usize,
    mut v_i_4593_: usize,
    mut v_bs_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4600_: u8 = 0;
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4607_: u8 = 0;
    let mut v_op_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: usize = 0;
    let mut v___x_4622_: usize = 0;
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeutralClass_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4600_ = lean_usize_dec_lt(v_i_4593_, v_sz_4592_);
                if v___x_4600_ == 0 {
                    crate::leanh::lean_dec_ref(v_00_u03b1_4591_);
                    crate::leanh::lean_dec_ref(v_preContext_4590_);
                    crate::leanh::lean_dec(v_u_4589_);
                    v___x_4601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4601_, 0, v_bs_4594_);
                    return v___x_4601_;
                } else {
                    v_v_4602_ = lean_array_uget(v_bs_4594_, v_i_4593_);
                    v_fst_4603_ = crate::leanh::lean_ctor_get(v_v_4602_, 0);
                    v_snd_4604_ = crate::leanh::lean_ctor_get(v_v_4602_, 1);
                    v_isSharedCheck_4637_ = (!crate::leanh::lean_is_exclusive(v_v_4602_)) as u8;
                    if v_isSharedCheck_4637_ == 0 {
                        v___x_4606_ = v_v_4602_;
                        v_isShared_4607_ = v_isSharedCheck_4637_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4604_);
                        crate::leanh::lean_inc(v_fst_4603_);
                        crate::leanh::lean_dec(v_v_4602_);
                        v___x_4606_ = crate::leanh::lean_box(0);
                        v_isShared_4607_ = v_isSharedCheck_4637_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_op_4608_ = crate::leanh::lean_ctor_get(v_preContext_4590_, 1);
                v___x_4609_ = crate::leanh::lean_box(0);
                v___x_4610_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
                v___x_4611_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_4612_ = lean_array_uset(v_bs_4594_, v_i_4593_, v___x_4611_);
                v___x_4613_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_abstractAtoms_go___lam__1___closed__1;
                crate::leanh::lean_inc(v_u_4589_);
                if v_isShared_4607_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4606_, 1);
                    crate::leanh::lean_ctor_set(v___x_4606_, 1, v___x_4609_);
                    crate::leanh::lean_ctor_set(v___x_4606_, 0, v_u_4589_);
                    v___x_4615_ = v___x_4606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4636_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_u_4589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4636_, 1, v___x_4609_);
                    v___x_4615_ = v_reuseFailAlloc_4636_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___x_4615_);
                v___x_4625_ = l_Lean_mkConst(v___x_4613_, v___x_4615_);
                crate::leanh::lean_inc(v_fst_4603_);
                crate::leanh::lean_inc_ref(v_op_4608_);
                crate::leanh::lean_inc_ref(v_00_u03b1_4591_);
                v_isNeutralClass_4626_ =
                    l_Lean_mkApp3(v___x_4625_, v_00_u03b1_4591_, v_op_4608_, v_fst_4603_);
                if crate::leanh::lean_obj_tag(v_snd_4604_) == 0 {
                    v___x_4627_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__9);
                    v___x_4628_ = l_Lean_Expr_app___override(v___x_4610_, v_isNeutralClass_4626_);
                    v___x_4629_ = l_Lean_Expr_app___override(v___x_4627_, v___x_4628_);
                    v___y_4617_ = v___x_4629_;
                    state = 3;
                    continue;
                } else {
                    v_val_4630_ = crate::leanh::lean_ctor_get(v_snd_4604_, 0);
                    crate::leanh::lean_inc(v_val_4630_);
                    crate::leanh::lean_dec_ref_known(v_snd_4604_, 1);
                    v___x_4631_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
                    v___x_4632_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__13);
                    crate::leanh::lean_inc_ref(v_isNeutralClass_4626_);
                    v___x_4633_ = l_Lean_Expr_app___override(v___x_4610_, v_isNeutralClass_4626_);
                    v___x_4634_ = l_Lean_mkAppB(v___x_4631_, v_isNeutralClass_4626_, v_val_4630_);
                    v___x_4635_ = l_Lean_mkAppB(v___x_4632_, v___x_4633_, v___x_4634_);
                    v___y_4617_ = v___x_4635_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__8;
                v___x_4619_ = l_Lean_mkConst(v___x_4618_, v___x_4615_);
                crate::leanh::lean_inc_ref(v_op_4608_);
                crate::leanh::lean_inc_ref(v_00_u03b1_4591_);
                v___x_4620_ = l_Lean_mkApp4(
                    v___x_4619_,
                    v_00_u03b1_4591_,
                    v_op_4608_,
                    v_fst_4603_,
                    v___y_4617_,
                );
                v___x_4621_ = 1usize;
                v___x_4622_ = lean_usize_add(v_i_4593_, v___x_4621_);
                v___x_4623_ = lean_array_uset(v_bs_x27_4612_, v_i_4593_, v___x_4620_);
                v___x_4624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_4589_, v_preContext_4590_, v_00_u03b1_4591_, v_sz_4592_, v___x_4622_, v___x_4623_);
                return v___x_4624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0___boxed(
    mut v_u_4638_: *mut crate::leanh::LeanObject,
    mut v_preContext_4639_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4640_: *mut crate::leanh::LeanObject,
    mut v_sz_4641_: *mut crate::leanh::LeanObject,
    mut v_i_4642_: *mut crate::leanh::LeanObject,
    mut v_bs_4643_: *mut crate::leanh::LeanObject,
    mut v___y_4644_: *mut crate::leanh::LeanObject,
    mut v___y_4645_: *mut crate::leanh::LeanObject,
    mut v___y_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4649_: usize = 0;
    let mut v_i_boxed_4650_: usize = 0;
    let mut v_res_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4649_ = crate::leanh::lean_unbox_usize(v_sz_4641_);
    crate::leanh::lean_dec(v_sz_4641_);
    v_i_boxed_4650_ = crate::leanh::lean_unbox_usize(v_i_4642_);
    crate::leanh::lean_dec(v_i_4642_);
    v_res_4651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(v_u_4638_, v_preContext_4639_, v_00_u03b1_4640_, v_sz_boxed_4649_, v_i_boxed_4650_, v_bs_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
    crate::leanh::lean_dec(v___y_4647_);
    crate::leanh::lean_dec_ref(v___y_4646_);
    crate::leanh::lean_dec(v___y_4645_);
    crate::leanh::lean_dec_ref(v___y_4644_);
    return v_res_4651_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4652_ = crate::leanh::lean_box(0);
    v___x_4653_ = l_Lean_instInhabitedExpr;
    v___x_4654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4654_, 0, v___x_4653_);
    crate::leanh::lean_ctor_set(v___x_4654_, 1, v___x_4652_);
    return v___x_4654_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(
    mut v_preContext_4667_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4668_: *mut crate::leanh::LeanObject,
    mut v_u_4669_: *mut crate::leanh::LeanObject,
    mut v_vars_4670_: *mut crate::leanh::LeanObject,
    mut v_a_4671_: *mut crate::leanh::LeanObject,
    mut v_a_4672_: *mut crate::leanh::LeanObject,
    mut v_a_4673_: *mut crate::leanh::LeanObject,
    mut v_a_4674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4679_: usize = 0;
    let mut v___x_4680_: usize = 0;
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assoc_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_comm_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idem_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4698_: u8 = 0;
    let mut v_fst_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4725_: u8 = 0;
    let mut v_a_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4729_: u8 = 0;
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4676_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0_once), _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__0);
                v___x_4677_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4678_ = lean_array_get(v___x_4676_, v_vars_4670_, v___x_4677_);
                v_sz_4679_ = lean_array_size(v_vars_4670_);
                v___x_4680_ = 0usize;
                crate::leanh::lean_inc_ref(v_00_u03b1_4668_);
                crate::leanh::lean_inc_ref(v_preContext_4667_);
                crate::leanh::lean_inc(v_u_4669_);
                v___x_4681_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0(v_u_4669_, v_preContext_4667_, v_00_u03b1_4668_, v_sz_4679_, v___x_4680_, v_vars_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_);
                if crate::leanh::lean_obj_tag(v___x_4681_) == 0 {
                    v_a_4682_ = crate::leanh::lean_ctor_get(v___x_4681_, 0);
                    crate::leanh::lean_inc(v_a_4682_);
                    crate::leanh::lean_dec_ref_known(v___x_4681_, 1);
                    v_op_4683_ = crate::leanh::lean_ctor_get(v_preContext_4667_, 1);
                    crate::leanh::lean_inc_ref_n(v_op_4683_, 2);
                    v_assoc_4684_ = crate::leanh::lean_ctor_get(v_preContext_4667_, 2);
                    crate::leanh::lean_inc_ref(v_assoc_4684_);
                    v_comm_4685_ = crate::leanh::lean_ctor_get(v_preContext_4667_, 3);
                    crate::leanh::lean_inc(v_comm_4685_);
                    v_idem_4686_ = crate::leanh::lean_ctor_get(v_preContext_4667_, 4);
                    crate::leanh::lean_inc(v_idem_4686_);
                    crate::leanh::lean_dec_ref(v_preContext_4667_);
                    v___x_4687_ = crate::leanh::lean_box(0);
                    v___x_4688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__0;
                    v___x_4689_ = lean_array_to_list(v_a_4682_);
                    v___x_4690_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__1;
                    v___x_4691_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4691_, 0, v_u_4669_);
                    crate::leanh::lean_ctor_set(v___x_4691_, 1, v___x_4687_);
                    crate::leanh::lean_inc_ref(v___x_4691_);
                    v___x_4692_ = l_Lean_mkConst(v___x_4690_, v___x_4691_);
                    crate::leanh::lean_inc_ref(v_00_u03b1_4668_);
                    v___x_4693_ = l_Lean_mkAppB(v___x_4692_, v_00_u03b1_4668_, v_op_4683_);
                    v___x_4694_ = l_Lean_Meta_mkListLit(
                        v___x_4693_,
                        v___x_4689_,
                        v_a_4671_,
                        v_a_4672_,
                        v_a_4673_,
                        v_a_4674_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4694_) == 0 {
                        v_a_4695_ = crate::leanh::lean_ctor_get(v___x_4694_, 0);
                        v_isSharedCheck_4725_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4694_)) as u8;
                        if v_isSharedCheck_4725_ == 0 {
                            v___x_4697_ = v___x_4694_;
                            v_isShared_4698_ = v_isSharedCheck_4725_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4695_);
                            crate::leanh::lean_dec(v___x_4694_);
                            v___x_4697_ = crate::leanh::lean_box(0);
                            v_isShared_4698_ = v_isSharedCheck_4725_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_4691_, 2);
                        crate::leanh::lean_dec(v_idem_4686_);
                        crate::leanh::lean_dec(v_comm_4685_);
                        crate::leanh::lean_dec_ref(v_assoc_4684_);
                        crate::leanh::lean_dec_ref(v_op_4683_);
                        crate::leanh::lean_dec(v___x_4678_);
                        crate::leanh::lean_dec_ref(v_00_u03b1_4668_);
                        return v___x_4694_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4678_);
                    crate::leanh::lean_dec(v_u_4669_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_4668_);
                    crate::leanh::lean_dec_ref(v_preContext_4667_);
                    v_a_4726_ = crate::leanh::lean_ctor_get(v___x_4681_, 0);
                    v_isSharedCheck_4733_ = (!crate::leanh::lean_is_exclusive(v___x_4681_)) as u8;
                    if v_isSharedCheck_4733_ == 0 {
                        v___x_4728_ = v___x_4681_;
                        v_isShared_4729_ = v_isSharedCheck_4733_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4726_);
                        crate::leanh::lean_dec(v___x_4681_);
                        v___x_4728_ = crate::leanh::lean_box(0);
                        v_isShared_4729_ = v_isSharedCheck_4733_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4699_ = crate::leanh::lean_ctor_get(v___x_4678_, 0);
                crate::leanh::lean_inc(v_fst_4699_);
                crate::leanh::lean_dec(v___x_4678_);
                v___x_4709_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__3);
                v___x_4710_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg___closed__12);
                v___x_4719_ = l_Lean_Meta_AC_preContext___closed__4;
                crate::leanh::lean_inc_ref(v___x_4691_);
                v___x_4720_ = l_Lean_mkConst(v___x_4719_, v___x_4691_);
                crate::leanh::lean_inc_ref(v_op_4683_);
                crate::leanh::lean_inc_ref(v_00_u03b1_4668_);
                v___x_4721_ = l_Lean_mkAppB(v___x_4720_, v_00_u03b1_4668_, v_op_4683_);
                if crate::leanh::lean_obj_tag(v_comm_4685_) == 0 {
                    v___x_4722_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(v___x_4688_, v___x_4709_, v___x_4721_);
                    v___y_4712_ = v___x_4722_;
                    state = 4;
                    continue;
                } else {
                    v_val_4723_ = crate::leanh::lean_ctor_get(v_comm_4685_, 0);
                    crate::leanh::lean_inc(v_val_4723_);
                    crate::leanh::lean_dec_ref_known(v_comm_4685_, 1);
                    v___x_4724_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(v___x_4688_, v___x_4709_, v___x_4710_, v___x_4721_, v_val_4723_);
                    v___y_4712_ = v___x_4724_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_4703_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___closed__3;
                v___x_4704_ = l_Lean_mkConst(v___x_4703_, v___x_4691_);
                v___x_4705_ = l_Lean_mkApp7(
                    v___x_4704_,
                    v_00_u03b1_4668_,
                    v_op_4683_,
                    v_assoc_4684_,
                    v___y_4701_,
                    v___y_4702_,
                    v_a_4695_,
                    v_fst_4699_,
                );
                if v_isShared_4698_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4697_, 0, v___x_4705_);
                    v___x_4707_ = v___x_4697_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4708_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4705_);
                    v___x_4707_ = v_reuseFailAlloc_4708_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4707_;
            }
            4 => {
                v___x_4713_ = l_Lean_Meta_AC_preContext___closed__6;
                crate::leanh::lean_inc_ref(v___x_4691_);
                v___x_4714_ = l_Lean_mkConst(v___x_4713_, v___x_4691_);
                crate::leanh::lean_inc_ref(v_op_4683_);
                crate::leanh::lean_inc_ref(v_00_u03b1_4668_);
                v___x_4715_ = l_Lean_mkAppB(v___x_4714_, v_00_u03b1_4668_, v_op_4683_);
                if crate::leanh::lean_obj_tag(v_idem_4686_) == 0 {
                    v___x_4716_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__0(v___x_4688_, v___x_4709_, v___x_4715_);
                    v___y_4701_ = v___y_4712_;
                    v___y_4702_ = v___x_4716_;
                    state = 2;
                    continue;
                } else {
                    v_val_4717_ = crate::leanh::lean_ctor_get(v_idem_4686_, 0);
                    crate::leanh::lean_inc(v_val_4717_);
                    crate::leanh::lean_dec_ref_known(v_idem_4686_, 1);
                    v___x_4718_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___lam__1(v___x_4688_, v___x_4709_, v___x_4710_, v___x_4715_, v_val_4717_);
                    v___y_4701_ = v___y_4712_;
                    v___y_4702_ = v___x_4718_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_4729_ == 0 {
                    v___x_4731_ = v___x_4728_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4726_);
                    v___x_4731_ = v_reuseFailAlloc_4732_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext___boxed(
    mut v_preContext_4734_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4735_: *mut crate::leanh::LeanObject,
    mut v_u_4736_: *mut crate::leanh::LeanObject,
    mut v_vars_4737_: *mut crate::leanh::LeanObject,
    mut v_a_4738_: *mut crate::leanh::LeanObject,
    mut v_a_4739_: *mut crate::leanh::LeanObject,
    mut v_a_4740_: *mut crate::leanh::LeanObject,
    mut v_a_4741_: *mut crate::leanh::LeanObject,
    mut v_a_4742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4743_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(
        v_preContext_4734_,
        v_00_u03b1_4735_,
        v_u_4736_,
        v_vars_4737_,
        v_a_4738_,
        v_a_4739_,
        v_a_4740_,
        v_a_4741_,
    );
    crate::leanh::lean_dec(v_a_4741_);
    crate::leanh::lean_dec_ref(v_a_4740_);
    crate::leanh::lean_dec(v_a_4739_);
    crate::leanh::lean_dec_ref(v_a_4738_);
    return v_res_4743_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0(
    mut v_u_4744_: *mut crate::leanh::LeanObject,
    mut v_preContext_4745_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4746_: *mut crate::leanh::LeanObject,
    mut v_sz_4747_: usize,
    mut v_i_4748_: usize,
    mut v_bs_4749_: *mut crate::leanh::LeanObject,
    mut v___y_4750_: *mut crate::leanh::LeanObject,
    mut v___y_4751_: *mut crate::leanh::LeanObject,
    mut v___y_4752_: *mut crate::leanh::LeanObject,
    mut v___y_4753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___redArg(v_u_4744_, v_preContext_4745_, v_00_u03b1_4746_, v_sz_4747_, v_i_4748_, v_bs_4749_);
    return v___x_4755_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0___boxed(
    mut v_u_4756_: *mut crate::leanh::LeanObject,
    mut v_preContext_4757_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_4758_: *mut crate::leanh::LeanObject,
    mut v_sz_4759_: *mut crate::leanh::LeanObject,
    mut v_i_4760_: *mut crate::leanh::LeanObject,
    mut v_bs_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
    mut v___y_4763_: *mut crate::leanh::LeanObject,
    mut v___y_4764_: *mut crate::leanh::LeanObject,
    mut v___y_4765_: *mut crate::leanh::LeanObject,
    mut v___y_4766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4767_: usize = 0;
    let mut v_i_boxed_4768_: usize = 0;
    let mut v_res_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4767_ = crate::leanh::lean_unbox_usize(v_sz_4759_);
    crate::leanh::lean_dec(v_sz_4759_);
    v_i_boxed_4768_ = crate::leanh::lean_unbox_usize(v_i_4760_);
    crate::leanh::lean_dec(v_i_4760_);
    v_res_4769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext_spec__0_spec__0(v_u_4756_, v_preContext_4757_, v_00_u03b1_4758_, v_sz_boxed_4767_, v_i_boxed_4768_, v_bs_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
    crate::leanh::lean_dec(v___y_4765_);
    crate::leanh::lean_dec_ref(v___y_4764_);
    crate::leanh::lean_dec(v___y_4763_);
    crate::leanh::lean_dec_ref(v___y_4762_);
    return v_res_4769_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4778_ = crate::leanh::lean_box(0);
    v___x_4779_ =
        l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__2;
    v___x_4780_ = l_Lean_mkConst(v___x_4779_, v___x_4778_);
    return v___x_4780_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4788_ = crate::leanh::lean_box(0);
    v___x_4789_ =
        l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__5;
    v___x_4790_ = l_Lean_mkConst(v___x_4789_, v___x_4788_);
    return v___x_4790_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(
    mut v_a_4791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_4791_) == 0 {
        let mut v_x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_x_4792_ = crate::leanh::lean_ctor_get(v_a_4791_, 0);
        crate::leanh::lean_inc(v_x_4792_);
        crate::leanh::lean_dec_ref_known(v_a_4791_, 1);
        v___x_4793_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3_once), _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__3);
        v___x_4794_ = l_Lean_mkNatLit(v_x_4792_);
        v___x_4795_ = l_Lean_Expr_app___override(v___x_4793_, v___x_4794_);
        return v___x_4795_;
    } else {
        let mut v_lhs_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_lhs_4796_ = crate::leanh::lean_ctor_get(v_a_4791_, 0);
        crate::leanh::lean_inc_ref(v_lhs_4796_);
        v_rhs_4797_ = crate::leanh::lean_ctor_get(v_a_4791_, 1);
        crate::leanh::lean_inc_ref(v_rhs_4797_);
        crate::leanh::lean_dec_ref_known(v_a_4791_, 2);
        v___x_4798_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6_once), _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert___closed__6);
        v___x_4799_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(
            v_lhs_4796_,
        );
        v___x_4800_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(
            v_rhs_4797_,
        );
        v___x_4801_ = l_Lean_mkAppB(v___x_4798_, v___x_4799_, v___x_4800_);
        return v___x_4801_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(
    mut v_preContext_4802_: *mut crate::leanh::LeanObject,
    mut v_vars_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_4804_) == 0 {
        let mut v_x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_preContext_4802_);
        v_x_4805_ = crate::leanh::lean_ctor_get(v_a_4804_, 0);
        v___x_4806_ = l_Lean_instInhabitedExpr;
        v___x_4807_ = lean_array_get_borrowed(v___x_4806_, v_vars_4803_, v_x_4805_);
        crate::leanh::lean_inc(v___x_4807_);
        return v___x_4807_;
    } else {
        let mut v_lhs_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_op_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_lhs_4808_ = crate::leanh::lean_ctor_get(v_a_4804_, 0);
        v_rhs_4809_ = crate::leanh::lean_ctor_get(v_a_4804_, 1);
        v_op_4810_ = crate::leanh::lean_ctor_get(v_preContext_4802_, 1);
        crate::leanh::lean_inc_ref(v_op_4810_);
        crate::leanh::lean_inc_ref(v_preContext_4802_);
        v___x_4811_ =
            l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(
                v_preContext_4802_,
                v_vars_4803_,
                v_lhs_4808_,
            );
        v___x_4812_ =
            l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(
                v_preContext_4802_,
                v_vars_4803_,
                v_rhs_4809_,
            );
        v___x_4813_ = l_Lean_mkAppB(v_op_4810_, v___x_4811_, v___x_4812_);
        return v___x_4813_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget___boxed(
    mut v_preContext_4814_: *mut crate::leanh::LeanObject,
    mut v_vars_4815_: *mut crate::leanh::LeanObject,
    mut v_a_4816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4817_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(
        v_preContext_4814_,
        v_vars_4815_,
        v_a_4816_,
    );
    crate::leanh::lean_dec_ref(v_a_4816_);
    crate::leanh::lean_dec_ref(v_vars_4815_);
    return v_res_4817_;
}
pub unsafe fn l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(
    mut v_msg_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
    mut v___y_4821_: *mut crate::leanh::LeanObject,
    mut v___y_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014__overap_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4825_ = l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___closed__0;
    v___x_2014__overap_4826_ = lean_panic_fn_borrowed(v___f_4825_, v_msg_4819_);
    crate::leanh::lean_inc(v___y_4823_);
    crate::leanh::lean_inc_ref(v___y_4822_);
    crate::leanh::lean_inc(v___y_4821_);
    crate::leanh::lean_inc_ref(v___y_4820_);
    v___x_4827_ = crate::leanh::lean_apply_5(
        v___x_2014__overap_4826_,
        v___y_4820_,
        v___y_4821_,
        v___y_4822_,
        v___y_4823_,
        crate::leanh::lean_box(0),
    );
    return v___x_4827_;
}
pub unsafe fn l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4___boxed(
    mut v_msg_4828_: *mut crate::leanh::LeanObject,
    mut v___y_4829_: *mut crate::leanh::LeanObject,
    mut v___y_4830_: *mut crate::leanh::LeanObject,
    mut v___y_4831_: *mut crate::leanh::LeanObject,
    mut v___y_4832_: *mut crate::leanh::LeanObject,
    mut v___y_4833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4834_ = l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(
        v_msg_4828_,
        v___y_4829_,
        v___y_4830_,
        v___y_4831_,
        v___y_4832_,
    );
    crate::leanh::lean_dec(v___y_4832_);
    crate::leanh::lean_dec_ref(v___y_4831_);
    crate::leanh::lean_dec(v___y_4830_);
    crate::leanh::lean_dec_ref(v___y_4829_);
    return v_res_4834_;
}
pub unsafe fn l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(
    mut v_x_4835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4843_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut v_unused_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4835_) == 0 {
                    v___x_4836_ =
                        l_Lean_Meta_AC_instEvalInformationPreContextACExpr___lam__0___closed__0;
                    return v___x_4836_;
                } else {
                    v_tail_4837_ = crate::leanh::lean_ctor_get(v_x_4835_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_4837_) == 0 {
                        v_head_4838_ = crate::leanh::lean_ctor_get(v_x_4835_, 0);
                        crate::leanh::lean_inc(v_head_4838_);
                        crate::leanh::lean_dec_ref_known(v_x_4835_, 2);
                        v___x_4839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4839_, 0, v_head_4838_);
                        return v___x_4839_;
                    } else {
                        crate::leanh::lean_inc(v_tail_4837_);
                        v_head_4840_ = crate::leanh::lean_ctor_get(v_x_4835_, 0);
                        v_isSharedCheck_4849_ = (!crate::leanh::lean_is_exclusive(v_x_4835_)) as u8;
                        if v_isSharedCheck_4849_ == 0 {
                            v_unused_4850_ = crate::leanh::lean_ctor_get(v_x_4835_, 1);
                            crate::leanh::lean_dec(v_unused_4850_);
                            v___x_4842_ = v_x_4835_;
                            v_isShared_4843_ = v_isSharedCheck_4849_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_4840_);
                            crate::leanh::lean_dec(v_x_4835_);
                            v___x_4842_ = crate::leanh::lean_box(0);
                            v_isShared_4843_ = v_isSharedCheck_4849_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4844_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4844_, 0, v_head_4840_);
                v___x_4845_ =
                    l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(
                        v_tail_4837_,
                    );
                if v_isShared_4843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4842_, 1, v___x_4845_);
                    crate::leanh::lean_ctor_set(v___x_4842_, 0, v___x_4844_);
                    v___x_4847_ = v___x_4842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4848_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 1, v___x_4845_);
                    v___x_4847_ = v_reuseFailAlloc_4848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2(
    mut v_sz_4851_: usize,
    mut v_i_4852_: usize,
    mut v_bs_4853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4854_: u8 = 0;
    let mut v_v_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: usize = 0;
    let mut v___x_4860_: usize = 0;
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4854_ = lean_usize_dec_lt(v_i_4852_, v_sz_4851_);
                if v___x_4854_ == 0 {
                    return v_bs_4853_;
                } else {
                    v_v_4855_ = lean_array_uget_borrowed(v_bs_4853_, v_i_4852_);
                    v_fst_4856_ = crate::leanh::lean_ctor_get(v_v_4855_, 0);
                    crate::leanh::lean_inc(v_fst_4856_);
                    v___x_4857_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4858_ = lean_array_uset(v_bs_4853_, v_i_4852_, v___x_4857_);
                    v___x_4859_ = 1usize;
                    v___x_4860_ = lean_usize_add(v_i_4852_, v___x_4859_);
                    v___x_4861_ = lean_array_uset(v_bs_x27_4858_, v_i_4852_, v_fst_4856_);
                    v_i_4852_ = v___x_4860_;
                    v_bs_4853_ = v___x_4861_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2___boxed(
    mut v_sz_4863_: *mut crate::leanh::LeanObject,
    mut v_i_4864_: *mut crate::leanh::LeanObject,
    mut v_bs_4865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4866_: usize = 0;
    let mut v_i_boxed_4867_: usize = 0;
    let mut v_res_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4866_ = crate::leanh::lean_unbox_usize(v_sz_4863_);
    crate::leanh::lean_dec(v_sz_4863_);
    v_i_boxed_4867_ = crate::leanh::lean_unbox_usize(v_i_4864_);
    crate::leanh::lean_dec(v_i_4864_);
    v_res_4868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2(v_sz_boxed_4866_, v_i_boxed_4867_, v_bs_4865_);
    return v_res_4868_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(
    mut v_sz_4869_: usize,
    mut v_i_4870_: usize,
    mut v_bs_4871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4872_: u8 = 0;
    let mut v_v_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4878_: u8 = 0;
    let mut v___x_4879_: usize = 0;
    let mut v___x_4880_: usize = 0;
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4872_ = lean_usize_dec_lt(v_i_4870_, v_sz_4869_);
                if v___x_4872_ == 0 {
                    return v_bs_4871_;
                } else {
                    v_v_4873_ = lean_array_uget_borrowed(v_bs_4871_, v_i_4870_);
                    v_snd_4874_ = crate::leanh::lean_ctor_get(v_v_4873_, 1);
                    crate::leanh::lean_inc(v_snd_4874_);
                    v___x_4875_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4876_ = lean_array_uset(v_bs_4871_, v_i_4870_, v___x_4875_);
                    if crate::leanh::lean_obj_tag(v_snd_4874_) == 0 {
                        v___x_4884_ = 0;
                        v___y_4878_ = v___x_4884_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_snd_4874_, 1);
                        v___y_4878_ = v___x_4872_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4879_ = 1usize;
                v___x_4880_ = lean_usize_add(v_i_4870_, v___x_4879_);
                v___x_4881_ = crate::leanh::lean_box((v___y_4878_) as usize);
                v___x_4882_ = lean_array_uset(v_bs_x27_4876_, v_i_4870_, v___x_4881_);
                v_i_4870_ = v___x_4880_;
                v_bs_4871_ = v___x_4882_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0___boxed(
    mut v_sz_4885_: *mut crate::leanh::LeanObject,
    mut v_i_4886_: *mut crate::leanh::LeanObject,
    mut v_bs_4887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4888_: usize = 0;
    let mut v_i_boxed_4889_: usize = 0;
    let mut v_res_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4888_ = crate::leanh::lean_unbox_usize(v_sz_4885_);
    crate::leanh::lean_dec(v_sz_4885_);
    v_i_boxed_4889_ = crate::leanh::lean_unbox_usize(v_i_4886_);
    crate::leanh::lean_dec(v_i_4886_);
    v_res_4890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(v_sz_boxed_4888_, v_i_boxed_4889_, v_bs_4887_);
    return v_res_4890_;
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(
    mut v_ctx_4891_: *mut crate::leanh::LeanObject,
    mut v_a_4892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4897_: u8 = 0;
    let mut v_snd_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: u8 = 0;
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: u8 = 0;
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4892_) == 0 {
                    return v_a_4892_;
                } else {
                    v_head_4893_ = crate::leanh::lean_ctor_get(v_a_4892_, 0);
                    v_tail_4894_ = crate::leanh::lean_ctor_get(v_a_4892_, 1);
                    v_isSharedCheck_4908_ = (!crate::leanh::lean_is_exclusive(v_a_4892_)) as u8;
                    if v_isSharedCheck_4908_ == 0 {
                        v___x_4896_ = v_a_4892_;
                        v_isShared_4897_ = v_isSharedCheck_4908_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4894_);
                        crate::leanh::lean_inc(v_head_4893_);
                        crate::leanh::lean_dec(v_a_4892_);
                        v___x_4896_ = crate::leanh::lean_box(0);
                        v_isShared_4897_ = v_isSharedCheck_4908_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4898_ = crate::leanh::lean_ctor_get(v_ctx_4891_, 1);
                v___x_4899_ = 0;
                v___x_4900_ = crate::leanh::lean_box((v___x_4899_) as usize);
                v___x_4901_ = lean_array_get(v___x_4900_, v_snd_4898_, v_head_4893_);
                crate::leanh::lean_dec(v___x_4900_);
                v___x_4902_ = (crate::leanh::lean_unbox(v___x_4901_) as u8);
                crate::leanh::lean_dec(v___x_4901_);
                if v___x_4902_ == 0 {
                    v___x_4903_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(v_ctx_4891_, v_tail_4894_);
                    if v_isShared_4897_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4896_, 1, v___x_4903_);
                        v___x_4905_ = v___x_4896_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4906_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_head_4893_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4906_, 1, v___x_4903_);
                        v___x_4905_ = v_reuseFailAlloc_4906_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4896_);
                    crate::leanh::lean_dec(v_head_4893_);
                    v_a_4892_ = v_tail_4894_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_4905_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3___boxed(
    mut v_ctx_4909_: *mut crate::leanh::LeanObject,
    mut v_a_4910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4911_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(v_ctx_4909_, v_a_4910_);
    crate::leanh::lean_dec_ref(v_ctx_4909_);
    return v_res_4911_;
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1(
    mut v_ctx_4912_: *mut crate::leanh::LeanObject,
    mut v_x_4913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4913_) == 0 {
        return v_x_4913_;
    } else {
        let mut v_head_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_4914_ = crate::leanh::lean_ctor_get(v_x_4913_, 0);
        crate::leanh::lean_inc(v_head_4914_);
        v___x_4915_ = l_Lean_Data_AC_removeNeutrals_loop___at___00Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1_spec__3(v_ctx_4912_, v_x_4913_);
        if crate::leanh::lean_obj_tag(v___x_4915_) == 0 {
            let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4916_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4916_, 0, v_head_4914_);
            crate::leanh::lean_ctor_set(v___x_4916_, 1, v___x_4915_);
            return v___x_4916_;
        } else {
            crate::leanh::lean_dec(v_head_4914_);
            return v___x_4915_;
        }
    }
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1___boxed(
    mut v_ctx_4917_: *mut crate::leanh::LeanObject,
    mut v_x_4918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4919_ = l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1(v_ctx_4917_, v_x_4918_);
    crate::leanh::lean_dec_ref(v_ctx_4917_);
    return v_res_4919_;
}
pub unsafe fn l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1(
    mut v_ctx_4920_: *mut crate::leanh::LeanObject,
    mut v_e_4921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_comm_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idem_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4922_ = crate::leanh::lean_ctor_get(v_ctx_4920_, 0);
                v_comm_4923_ = crate::leanh::lean_ctor_get(v_fst_4922_, 3);
                v_idem_4924_ = crate::leanh::lean_ctor_get(v_fst_4922_, 4);
                v_xs_4928_ = l_Lean_Data_AC_Expr_toList(v_e_4921_);
                v_xs_4929_ = l_Lean_Data_AC_removeNeutrals___at___00Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1_spec__1(v_ctx_4920_, v_xs_4928_);
                if crate::leanh::lean_obj_tag(v_comm_4923_) == 0 {
                    v___y_4926_ = v_xs_4929_;
                    state = 1;
                    continue;
                } else {
                    v___x_4930_ = l_Lean_Data_AC_sort(v_xs_4929_);
                    v___y_4926_ = v___x_4930_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_idem_4924_) == 0 {
                    return v___y_4926_;
                } else {
                    v___x_4927_ = l_Lean_Data_AC_mergeIdem(v___y_4926_);
                    return v___x_4927_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1___boxed(
    mut v_ctx_4931_: *mut crate::leanh::LeanObject,
    mut v_e_4932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4933_ =
        l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1(v_ctx_4931_, v_e_4932_);
    crate::leanh::lean_dec_ref(v_e_4932_);
    crate::leanh::lean_dec_ref(v_ctx_4931_);
    return v_res_4933_;
}
pub unsafe fn _init_l_Lean_Meta_AC_buildNormProof___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4939_ = crate::leanh::lean_box(0);
    v___x_4940_ = l_Lean_Meta_AC_buildNormProof___lam__0___closed__2;
    v___x_4941_ = l_Lean_mkConst(v___x_4940_, v___x_4939_);
    return v___x_4941_;
}
pub unsafe fn l_Lean_Meta_AC_buildNormProof___lam__0(
    mut v___x_4949_: *mut crate::leanh::LeanObject,
    mut v_fst_4950_: *mut crate::leanh::LeanObject,
    mut v_preContext_4951_: *mut crate::leanh::LeanObject,
    mut v_snd_4952_: *mut crate::leanh::LeanObject,
    mut v_varsData_4953_: *mut crate::leanh::LeanObject,
    mut v___y_4954_: *mut crate::leanh::LeanObject,
    mut v___y_4955_: *mut crate::leanh::LeanObject,
    mut v___y_4956_: *mut crate::leanh::LeanObject,
    mut v___y_4957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4971_: usize = 0;
    let mut v___x_4972_: usize = 0;
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4984_: u8 = 0;
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5002_: u8 = 0;
    let mut v_a_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4959_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4960_ = lean_array_get_borrowed(v___x_4949_, v_fst_4950_, v___x_4959_);
                crate::leanh::lean_inc(v___y_4957_);
                crate::leanh::lean_inc_ref(v___y_4956_);
                crate::leanh::lean_inc(v___y_4955_);
                crate::leanh::lean_inc_ref(v___y_4954_);
                crate::leanh::lean_inc(v___x_4960_);
                v___x_4961_ = lean_infer_type(
                    v___x_4960_,
                    v___y_4954_,
                    v___y_4955_,
                    v___y_4956_,
                    v___y_4957_,
                );
                if crate::leanh::lean_obj_tag(v___x_4961_) == 0 {
                    v_a_4962_ = crate::leanh::lean_ctor_get(v___x_4961_, 0);
                    crate::leanh::lean_inc_n(v_a_4962_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4961_, 1);
                    v___x_4963_ = l_Lean_Meta_getLevel(
                        v_a_4962_,
                        v___y_4954_,
                        v___y_4955_,
                        v___y_4956_,
                        v___y_4957_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4963_) == 0 {
                        v_a_4964_ = crate::leanh::lean_ctor_get(v___x_4963_, 0);
                        crate::leanh::lean_inc_n(v_a_4964_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4963_, 1);
                        crate::leanh::lean_inc_ref(v_varsData_4953_);
                        crate::leanh::lean_inc(v_a_4962_);
                        crate::leanh::lean_inc_ref(v_preContext_4951_);
                        v___x_4965_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_mkContext(v_preContext_4951_, v_a_4962_, v_a_4964_, v_varsData_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_);
                        if crate::leanh::lean_obj_tag(v___x_4965_) == 0 {
                            v_a_4966_ = crate::leanh::lean_ctor_get(v___x_4965_, 0);
                            crate::leanh::lean_inc(v_a_4966_);
                            crate::leanh::lean_dec_ref_known(v___x_4965_, 1);
                            v___x_4967_ = crate::leanh::lean_box(0);
                            v___x_4968_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_AC_buildNormProof___lam__0___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_AC_buildNormProof___lam__0___closed__3_once
                                ),
                                _init_l_Lean_Meta_AC_buildNormProof___lam__0___closed__3,
                            );
                            v___x_4969_ = l_Lean_Meta_mkEqRefl(
                                v___x_4968_,
                                v___y_4954_,
                                v___y_4955_,
                                v___y_4956_,
                                v___y_4957_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4969_) == 0 {
                                v_a_4970_ = crate::leanh::lean_ctor_get(v___x_4969_, 0);
                                crate::leanh::lean_inc(v_a_4970_);
                                crate::leanh::lean_dec_ref_known(v___x_4969_, 1);
                                v_sz_4971_ = lean_array_size(v_varsData_4953_);
                                v___x_4972_ = 0usize;
                                crate::leanh::lean_inc_ref(v_varsData_4953_);
                                v___x_4973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__0(v_sz_4971_, v___x_4972_, v_varsData_4953_);
                                crate::leanh::lean_inc_ref_n(v_preContext_4951_, 2);
                                v___x_4974_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4974_, 0, v_preContext_4951_);
                                crate::leanh::lean_ctor_set(v___x_4974_, 1, v___x_4973_);
                                v___x_4975_ = l_Lean_Data_AC_norm___at___00Lean_Meta_AC_buildNormProof_spec__1(v___x_4974_, v_snd_4952_);
                                crate::leanh::lean_dec_ref_known(v___x_4974_, 2);
                                v___x_4976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_AC_buildNormProof_spec__2(v_sz_4971_, v___x_4972_, v_varsData_4953_);
                                v___x_4977_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v___x_4975_);
                                v___x_4978_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_4951_, v___x_4976_, v_snd_4952_);
                                v___x_4979_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convertTarget(v_preContext_4951_, v___x_4976_, v___x_4977_);
                                crate::leanh::lean_dec_ref(v___x_4976_);
                                v___x_4980_ = l_Lean_Meta_mkEq(
                                    v___x_4978_,
                                    v___x_4979_,
                                    v___y_4954_,
                                    v___y_4955_,
                                    v___y_4956_,
                                    v___y_4957_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4980_) == 0 {
                                    v_a_4981_ = crate::leanh::lean_ctor_get(v___x_4980_, 0);
                                    v_isSharedCheck_5002_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4980_)) as u8;
                                    if v_isSharedCheck_5002_ == 0 {
                                        v___x_4983_ = v___x_4980_;
                                        v_isShared_4984_ = v_isSharedCheck_5002_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4981_);
                                        crate::leanh::lean_dec(v___x_4980_);
                                        v___x_4983_ = crate::leanh::lean_box(0);
                                        v_isShared_4984_ = v_isSharedCheck_5002_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4977_);
                                    crate::leanh::lean_dec(v_a_4970_);
                                    crate::leanh::lean_dec(v_a_4966_);
                                    crate::leanh::lean_dec(v_a_4964_);
                                    crate::leanh::lean_dec(v_a_4962_);
                                    crate::leanh::lean_dec_ref(v_snd_4952_);
                                    return v___x_4980_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4966_);
                                crate::leanh::lean_dec(v_a_4964_);
                                crate::leanh::lean_dec(v_a_4962_);
                                crate::leanh::lean_dec_ref(v_varsData_4953_);
                                crate::leanh::lean_dec_ref(v_snd_4952_);
                                crate::leanh::lean_dec_ref(v_preContext_4951_);
                                return v___x_4969_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4964_);
                            crate::leanh::lean_dec(v_a_4962_);
                            crate::leanh::lean_dec_ref(v_varsData_4953_);
                            crate::leanh::lean_dec_ref(v_snd_4952_);
                            crate::leanh::lean_dec_ref(v_preContext_4951_);
                            return v___x_4965_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4962_);
                        crate::leanh::lean_dec_ref(v_varsData_4953_);
                        crate::leanh::lean_dec_ref(v_snd_4952_);
                        crate::leanh::lean_dec_ref(v_preContext_4951_);
                        v_a_5003_ = crate::leanh::lean_ctor_get(v___x_4963_, 0);
                        v_isSharedCheck_5010_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4963_)) as u8;
                        if v_isSharedCheck_5010_ == 0 {
                            v___x_5005_ = v___x_4963_;
                            v_isShared_5006_ = v_isSharedCheck_5010_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5003_);
                            crate::leanh::lean_dec(v___x_4963_);
                            v___x_5005_ = crate::leanh::lean_box(0);
                            v_isShared_5006_ = v_isSharedCheck_5010_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_varsData_4953_);
                    crate::leanh::lean_dec_ref(v_snd_4952_);
                    crate::leanh::lean_dec_ref(v_preContext_4951_);
                    return v___x_4961_;
                }
            }
            1 => {
                v___x_4985_ =
                    l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(
                        v_snd_4952_,
                    );
                v___x_4986_ =
                    l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_buildNormProof_convert(
                        v___x_4977_,
                    );
                v___x_4987_ = l_Lean_Meta_AC_buildNormProof___lam__0___closed__5;
                v___x_4988_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4988_, 0, v_a_4964_);
                crate::leanh::lean_ctor_set(v___x_4988_, 1, v___x_4967_);
                v___x_4989_ = l_Lean_mkConst(v___x_4987_, v___x_4988_);
                v___x_4990_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_4991_ = lean_mk_empty_array_with_capacity(v___x_4990_);
                v___x_4992_ = lean_array_push(v___x_4991_, v_a_4962_);
                v___x_4993_ = lean_array_push(v___x_4992_, v_a_4966_);
                v___x_4994_ = lean_array_push(v___x_4993_, v___x_4985_);
                v___x_4995_ = lean_array_push(v___x_4994_, v___x_4986_);
                v___x_4996_ = lean_array_push(v___x_4995_, v_a_4970_);
                v___x_4997_ = l_Lean_mkAppN(v___x_4989_, v___x_4996_);
                crate::leanh::lean_dec_ref(v___x_4996_);
                v___x_4998_ = l_Lean_Meta_mkExpectedPropHint(v___x_4997_, v_a_4981_);
                if v_isShared_4984_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4983_, 0, v___x_4998_);
                    v___x_5000_ = v___x_4983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5001_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5001_, 0, v___x_4998_);
                    v___x_5000_ = v_reuseFailAlloc_5001_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5000_;
            }
            3 => {
                if v_isShared_5006_ == 0 {
                    v___x_5008_ = v___x_5005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
                    v___x_5008_ = v_reuseFailAlloc_5009_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_buildNormProof___lam__0___boxed(
    mut v___x_5011_: *mut crate::leanh::LeanObject,
    mut v_fst_5012_: *mut crate::leanh::LeanObject,
    mut v_preContext_5013_: *mut crate::leanh::LeanObject,
    mut v_snd_5014_: *mut crate::leanh::LeanObject,
    mut v_varsData_5015_: *mut crate::leanh::LeanObject,
    mut v___y_5016_: *mut crate::leanh::LeanObject,
    mut v___y_5017_: *mut crate::leanh::LeanObject,
    mut v___y_5018_: *mut crate::leanh::LeanObject,
    mut v___y_5019_: *mut crate::leanh::LeanObject,
    mut v___y_5020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5021_ = l_Lean_Meta_AC_buildNormProof___lam__0(
        v___x_5011_,
        v_fst_5012_,
        v_preContext_5013_,
        v_snd_5014_,
        v_varsData_5015_,
        v___y_5016_,
        v___y_5017_,
        v___y_5018_,
        v___y_5019_,
    );
    crate::leanh::lean_dec(v___y_5019_);
    crate::leanh::lean_dec_ref(v___y_5018_);
    crate::leanh::lean_dec(v___y_5017_);
    crate::leanh::lean_dec_ref(v___y_5016_);
    crate::leanh::lean_dec_ref(v_fst_5012_);
    crate::leanh::lean_dec_ref(v___x_5011_);
    return v_res_5021_;
}
pub unsafe fn _init_l_Lean_Meta_AC_buildNormProof___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5028_ = l_Lean_Meta_AC_buildNormProof___closed__4;
    v___x_5029_ = crate::leanh::lean_unsigned_to_nat(52);
    v___x_5030_ = crate::leanh::lean_unsigned_to_nat(132);
    v___x_5031_ = l_Lean_Meta_AC_buildNormProof___closed__3;
    v___x_5032_ = l_Lean_Meta_AC_buildNormProof___closed__2;
    v___x_5033_ = l_mkPanicMessageWithDecl(
        v___x_5032_,
        v___x_5031_,
        v___x_5030_,
        v___x_5029_,
        v___x_5028_,
    );
    return v___x_5033_;
}
pub unsafe fn l_Lean_Meta_AC_buildNormProof(
    mut v_preContext_5034_: *mut crate::leanh::LeanObject,
    mut v_l_5035_: *mut crate::leanh::LeanObject,
    mut v_r_5036_: *mut crate::leanh::LeanObject,
    mut v_a_5037_: *mut crate::leanh::LeanObject,
    mut v_a_5038_: *mut crate::leanh::LeanObject,
    mut v_a_5039_: *mut crate::leanh::LeanObject,
    mut v_a_5040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_op_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5049_: u8 = 0;
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5058_: u8 = 0;
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: u8 = 0;
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5071_: u8 = 0;
    let mut v_a_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5075_: u8 = 0;
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5079_: u8 = 0;
    let mut v_a_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut v_isSharedCheck_5088_: u8 = 0;
    let mut v_a_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5092_: u8 = 0;
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_op_5042_ = crate::leanh::lean_ctor_get(v_preContext_5034_, 1);
                crate::leanh::lean_inc_ref(v_op_5042_);
                v___x_5043_ = l_Lean_Meta_AC_toACExpr(
                    v_op_5042_, v_l_5035_, v_r_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_,
                );
                if crate::leanh::lean_obj_tag(v___x_5043_) == 0 {
                    v_a_5044_ = crate::leanh::lean_ctor_get(v___x_5043_, 0);
                    crate::leanh::lean_inc(v_a_5044_);
                    crate::leanh::lean_dec_ref_known(v___x_5043_, 1);
                    v_fst_5045_ = crate::leanh::lean_ctor_get(v_a_5044_, 0);
                    v_snd_5046_ = crate::leanh::lean_ctor_get(v_a_5044_, 1);
                    v_isSharedCheck_5088_ = (!crate::leanh::lean_is_exclusive(v_a_5044_)) as u8;
                    if v_isSharedCheck_5088_ == 0 {
                        v___x_5048_ = v_a_5044_;
                        v_isShared_5049_ = v_isSharedCheck_5088_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5046_);
                        crate::leanh::lean_inc(v_fst_5045_);
                        crate::leanh::lean_dec(v_a_5044_);
                        v___x_5048_ = crate::leanh::lean_box(0);
                        v_isShared_5049_ = v_isSharedCheck_5088_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_preContext_5034_);
                    v_a_5089_ = crate::leanh::lean_ctor_get(v___x_5043_, 0);
                    v_isSharedCheck_5096_ = (!crate::leanh::lean_is_exclusive(v___x_5043_)) as u8;
                    if v_isSharedCheck_5096_ == 0 {
                        v___x_5091_ = v___x_5043_;
                        v_isShared_5092_ = v_isSharedCheck_5096_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5089_);
                        crate::leanh::lean_dec(v___x_5043_);
                        v___x_5091_ = crate::leanh::lean_box(0);
                        v_isShared_5092_ = v_isSharedCheck_5096_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5050_ = l_Lean_instInhabitedExpr;
                crate::leanh::lean_inc_ref(v_preContext_5034_);
                crate::leanh::lean_inc(v_fst_5045_);
                v___f_5051_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_AC_buildNormProof___lam__0___boxed as *mut core::ffi::c_void,
                    10,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_5051_, 0, v___x_5050_);
                crate::leanh::lean_closure_set(v___f_5051_, 1, v_fst_5045_);
                crate::leanh::lean_closure_set(v___f_5051_, 2, v_preContext_5034_);
                crate::leanh::lean_closure_set(v___f_5051_, 3, v_snd_5046_);
                v___x_5052_ = l_Lean_Meta_AC_abstractAtoms(
                    v_preContext_5034_,
                    v_fst_5045_,
                    v___f_5051_,
                    v_a_5037_,
                    v_a_5038_,
                    v_a_5039_,
                    v_a_5040_,
                );
                if crate::leanh::lean_obj_tag(v___x_5052_) == 0 {
                    v_a_5053_ = crate::leanh::lean_ctor_get(v___x_5052_, 0);
                    crate::leanh::lean_inc_n(v_a_5053_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5052_, 1);
                    crate::leanh::lean_inc(v_a_5040_);
                    crate::leanh::lean_inc_ref(v_a_5039_);
                    crate::leanh::lean_inc(v_a_5038_);
                    crate::leanh::lean_inc_ref(v_a_5037_);
                    v___x_5054_ =
                        lean_infer_type(v_a_5053_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
                    if crate::leanh::lean_obj_tag(v___x_5054_) == 0 {
                        v_a_5055_ = crate::leanh::lean_ctor_get(v___x_5054_, 0);
                        v_isSharedCheck_5071_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5054_)) as u8;
                        if v_isSharedCheck_5071_ == 0 {
                            v___x_5057_ = v___x_5054_;
                            v_isShared_5058_ = v_isSharedCheck_5071_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5055_);
                            crate::leanh::lean_dec(v___x_5054_);
                            v___x_5057_ = crate::leanh::lean_box(0);
                            v_isShared_5058_ = v_isSharedCheck_5071_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5053_);
                        crate::leanh::lean_del_object(v___x_5048_);
                        v_a_5072_ = crate::leanh::lean_ctor_get(v___x_5054_, 0);
                        v_isSharedCheck_5079_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5054_)) as u8;
                        if v_isSharedCheck_5079_ == 0 {
                            v___x_5074_ = v___x_5054_;
                            v_isShared_5075_ = v_isSharedCheck_5079_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5072_);
                            crate::leanh::lean_dec(v___x_5054_);
                            v___x_5074_ = crate::leanh::lean_box(0);
                            v_isShared_5075_ = v_isSharedCheck_5079_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5048_);
                    v_a_5080_ = crate::leanh::lean_ctor_get(v___x_5052_, 0);
                    v_isSharedCheck_5087_ = (!crate::leanh::lean_is_exclusive(v___x_5052_)) as u8;
                    if v_isSharedCheck_5087_ == 0 {
                        v___x_5082_ = v___x_5052_;
                        v_isShared_5083_ = v_isSharedCheck_5087_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5080_);
                        crate::leanh::lean_dec(v___x_5052_);
                        v___x_5082_ = crate::leanh::lean_box(0);
                        v_isShared_5083_ = v_isSharedCheck_5087_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5059_ = l_Lean_Meta_AC_buildNormProof___closed__1;
                v___x_5060_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_5061_ = l_Lean_Expr_isAppOfArity(v_a_5055_, v___x_5059_, v___x_5060_);
                if v___x_5061_ == 0 {
                    crate::leanh::lean_del_object(v___x_5057_);
                    crate::leanh::lean_dec(v_a_5055_);
                    crate::leanh::lean_dec(v_a_5053_);
                    crate::leanh::lean_del_object(v___x_5048_);
                    v___x_5062_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_AC_buildNormProof___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_AC_buildNormProof___closed__5_once),
                        _init_l_Lean_Meta_AC_buildNormProof___closed__5,
                    );
                    v___x_5063_ = l_panic___at___00Lean_Meta_AC_buildNormProof_spec__4(
                        v___x_5062_,
                        v_a_5037_,
                        v_a_5038_,
                        v_a_5039_,
                        v_a_5040_,
                    );
                    return v___x_5063_;
                } else {
                    v___x_5064_ = l_Lean_Expr_appArg_x21(v_a_5055_);
                    crate::leanh::lean_dec(v_a_5055_);
                    if v_isShared_5049_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5048_, 1, v___x_5064_);
                        crate::leanh::lean_ctor_set(v___x_5048_, 0, v_a_5053_);
                        v___x_5066_ = v___x_5048_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5070_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5053_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5070_, 1, v___x_5064_);
                        v___x_5066_ = v_reuseFailAlloc_5070_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5058_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5057_, 0, v___x_5066_);
                    v___x_5068_ = v___x_5057_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5069_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5066_);
                    v___x_5068_ = v_reuseFailAlloc_5069_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5068_;
            }
            5 => {
                if v_isShared_5075_ == 0 {
                    v___x_5077_ = v___x_5074_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
                    v___x_5077_ = v_reuseFailAlloc_5078_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5077_;
            }
            7 => {
                if v_isShared_5083_ == 0 {
                    v___x_5085_ = v___x_5082_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5086_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
                    v___x_5085_ = v_reuseFailAlloc_5086_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5085_;
            }
            9 => {
                if v_isShared_5092_ == 0 {
                    v___x_5094_ = v___x_5091_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5095_, 0, v_a_5089_);
                    v___x_5094_ = v_reuseFailAlloc_5095_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_buildNormProof___boxed(
    mut v_preContext_5097_: *mut crate::leanh::LeanObject,
    mut v_l_5098_: *mut crate::leanh::LeanObject,
    mut v_r_5099_: *mut crate::leanh::LeanObject,
    mut v_a_5100_: *mut crate::leanh::LeanObject,
    mut v_a_5101_: *mut crate::leanh::LeanObject,
    mut v_a_5102_: *mut crate::leanh::LeanObject,
    mut v_a_5103_: *mut crate::leanh::LeanObject,
    mut v_a_5104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5105_ = l_Lean_Meta_AC_buildNormProof(
        v_preContext_5097_,
        v_l_5098_,
        v_r_5099_,
        v_a_5100_,
        v_a_5101_,
        v_a_5102_,
        v_a_5103_,
    );
    crate::leanh::lean_dec(v_a_5103_);
    crate::leanh::lean_dec_ref(v_a_5102_);
    crate::leanh::lean_dec(v_a_5101_);
    crate::leanh::lean_dec_ref(v_a_5100_);
    return v_res_5105_;
}
pub unsafe fn l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3(
    mut v_ctx_5106_: *mut crate::leanh::LeanObject,
    mut v_x_5107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5108_ =
        l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___redArg(v_x_5107_);
    return v___x_5108_;
}
pub unsafe fn l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3___boxed(
    mut v_ctx_5109_: *mut crate::leanh::LeanObject,
    mut v_x_5110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5111_ = l_Lean_Data_AC_evalList___at___00Lean_Meta_AC_buildNormProof_spec__3(
        v_ctx_5109_,
        v_x_5110_,
    );
    crate::leanh::lean_dec_ref(v_ctx_5109_);
    return v_res_5111_;
}
pub unsafe fn l_Lean_Meta_AC_post___redArg(
    mut v_e_5112_: *mut crate::leanh::LeanObject,
    mut v_a_5113_: *mut crate::leanh::LeanObject,
    mut v_a_5114_: *mut crate::leanh::LeanObject,
    mut v_a_5115_: *mut crate::leanh::LeanObject,
    mut v_a_5116_: *mut crate::leanh::LeanObject,
    mut v_a_5117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: u8 = 0;
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5138_: u8 = 0;
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: u8 = 0;
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5149_: u8 = 0;
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5154_: u8 = 0;
    let mut v_fst_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: u8 = 0;
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5166_: u8 = 0;
    let mut v_a_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5170_: u8 = 0;
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5174_: u8 = 0;
    let mut v_isSharedCheck_5175_: u8 = 0;
    let mut v_isSharedCheck_5176_: u8 = 0;
    let mut v_a_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5180_: u8 = 0;
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5184_: u8 = 0;
    let mut v_fn_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parent_x3f_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5197_: u8 = 0;
    let mut v___x_5198_: u8 = 0;
    let mut v___x_5199_: u8 = 0;
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5204_: u8 = 0;
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5214_: u8 = 0;
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5219_: u8 = 0;
    let mut v_fst_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5230_: u8 = 0;
    let mut v_a_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5234_: u8 = 0;
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5238_: u8 = 0;
    let mut v_isSharedCheck_5239_: u8 = 0;
    let mut v_isSharedCheck_5240_: u8 = 0;
    let mut v_a_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5244_: u8 = 0;
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5248_: u8 = 0;
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v_a_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5259_: u8 = 0;
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5263_: u8 = 0;
    let mut v_arg_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_5112_) == 5 {
                    v_fn_5185_ = crate::leanh::lean_ctor_get(v_e_5112_, 0);
                    if crate::leanh::lean_obj_tag(v_fn_5185_) == 5 {
                        v_parent_x3f_5186_ = crate::leanh::lean_ctor_get(v_a_5113_, 8);
                        if crate::leanh::lean_obj_tag(v_parent_x3f_5186_) == 1 {
                            v_val_5187_ = crate::leanh::lean_ctor_get(v_parent_x3f_5186_, 0);
                            if crate::leanh::lean_obj_tag(v_val_5187_) == 5 {
                                v_fn_5188_ = crate::leanh::lean_ctor_get(v_val_5187_, 0);
                                if crate::leanh::lean_obj_tag(v_fn_5188_) == 5 {
                                    v_arg_5189_ = crate::leanh::lean_ctor_get(v_e_5112_, 1);
                                    v_fn_5190_ = crate::leanh::lean_ctor_get(v_fn_5185_, 0);
                                    v_arg_5191_ = crate::leanh::lean_ctor_get(v_fn_5185_, 1);
                                    v_fn_5192_ = crate::leanh::lean_ctor_get(v_fn_5188_, 0);
                                    crate::leanh::lean_inc_ref(v_fn_5192_);
                                    crate::leanh::lean_inc_ref(v_fn_5190_);
                                    v___x_5193_ = l_Lean_Meta_isExprDefEq(
                                        v_fn_5190_, v_fn_5192_, v_a_5114_, v_a_5115_, v_a_5116_,
                                        v_a_5117_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_5193_) == 0 {
                                        v_a_5194_ = crate::leanh::lean_ctor_get(v___x_5193_, 0);
                                        v_isSharedCheck_5255_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5193_)) as u8;
                                        if v_isSharedCheck_5255_ == 0 {
                                            v___x_5196_ = v___x_5193_;
                                            v_isShared_5197_ = v_isSharedCheck_5255_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5194_);
                                            crate::leanh::lean_dec(v___x_5193_);
                                            v___x_5196_ = crate::leanh::lean_box(0);
                                            v_isShared_5197_ = v_isSharedCheck_5255_;
                                            state = 13;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_e_5112_, 2);
                                        v_a_5256_ = crate::leanh::lean_ctor_get(v___x_5193_, 0);
                                        v_isSharedCheck_5263_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5193_)) as u8;
                                        if v_isSharedCheck_5263_ == 0 {
                                            v___x_5258_ = v___x_5193_;
                                            v_isShared_5259_ = v_isSharedCheck_5263_;
                                            state = 25;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5256_);
                                            crate::leanh::lean_dec(v___x_5193_);
                                            v___x_5258_ = crate::leanh::lean_box(0);
                                            v_isShared_5259_ = v_isSharedCheck_5263_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_arg_5264_ = crate::leanh::lean_ctor_get(v_e_5112_, 1);
                                    v_fn_5265_ = crate::leanh::lean_ctor_get(v_fn_5185_, 0);
                                    v_arg_5266_ = crate::leanh::lean_ctor_get(v_fn_5185_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_5264_);
                                    crate::leanh::lean_inc_ref(v_arg_5266_);
                                    crate::leanh::lean_inc_ref(v_fn_5265_);
                                    v_op_5127_ = v_fn_5265_;
                                    v_l_5128_ = v_arg_5266_;
                                    v_r_5129_ = v_arg_5264_;
                                    v___y_5130_ = v_a_5114_;
                                    v___y_5131_ = v_a_5115_;
                                    v___y_5132_ = v_a_5116_;
                                    v___y_5133_ = v_a_5117_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_arg_5267_ = crate::leanh::lean_ctor_get(v_e_5112_, 1);
                                v_fn_5268_ = crate::leanh::lean_ctor_get(v_fn_5185_, 0);
                                v_arg_5269_ = crate::leanh::lean_ctor_get(v_fn_5185_, 1);
                                crate::leanh::lean_inc_ref(v_arg_5267_);
                                crate::leanh::lean_inc_ref(v_arg_5269_);
                                crate::leanh::lean_inc_ref(v_fn_5268_);
                                v_op_5127_ = v_fn_5268_;
                                v_l_5128_ = v_arg_5269_;
                                v_r_5129_ = v_arg_5267_;
                                v___y_5130_ = v_a_5114_;
                                v___y_5131_ = v_a_5115_;
                                v___y_5132_ = v_a_5116_;
                                v___y_5133_ = v_a_5117_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_arg_5270_ = crate::leanh::lean_ctor_get(v_e_5112_, 1);
                            v_fn_5271_ = crate::leanh::lean_ctor_get(v_fn_5185_, 0);
                            v_arg_5272_ = crate::leanh::lean_ctor_get(v_fn_5185_, 1);
                            crate::leanh::lean_inc_ref(v_arg_5270_);
                            crate::leanh::lean_inc_ref(v_arg_5272_);
                            crate::leanh::lean_inc_ref(v_fn_5271_);
                            v_op_5127_ = v_fn_5271_;
                            v_l_5128_ = v_arg_5272_;
                            v_r_5129_ = v_arg_5270_;
                            v___y_5130_ = v_a_5114_;
                            v___y_5131_ = v_a_5115_;
                            v___y_5132_ = v_a_5116_;
                            v___y_5133_ = v_a_5117_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_e_5120_ = v_e_5112_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_e_5120_ = v_e_5112_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5121_ = crate::leanh::lean_box(0);
                v___x_5122_ = 1;
                v___x_5123_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5123_, 0, v_e_5120_);
                crate::leanh::lean_ctor_set(v___x_5123_, 1, v___x_5121_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5123_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5122_,
                );
                v___x_5124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5124_, 0, v___x_5123_);
                v___x_5125_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5125_, 0, v___x_5124_);
                return v___x_5125_;
            }
            2 => {
                v___x_5134_ = l_Lean_Meta_AC_preContext(
                    v_op_5127_,
                    v___y_5130_,
                    v___y_5131_,
                    v___y_5132_,
                    v___y_5133_,
                );
                if crate::leanh::lean_obj_tag(v___x_5134_) == 0 {
                    v_a_5135_ = crate::leanh::lean_ctor_get(v___x_5134_, 0);
                    v_isSharedCheck_5176_ = (!crate::leanh::lean_is_exclusive(v___x_5134_)) as u8;
                    if v_isSharedCheck_5176_ == 0 {
                        v___x_5137_ = v___x_5134_;
                        v_isShared_5138_ = v_isSharedCheck_5176_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5135_);
                        crate::leanh::lean_dec(v___x_5134_);
                        v___x_5137_ = crate::leanh::lean_box(0);
                        v_isShared_5138_ = v_isSharedCheck_5176_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_r_5129_);
                    crate::leanh::lean_dec_ref(v_l_5128_);
                    crate::leanh::lean_dec_ref(v_e_5112_);
                    v_a_5177_ = crate::leanh::lean_ctor_get(v___x_5134_, 0);
                    v_isSharedCheck_5184_ = (!crate::leanh::lean_is_exclusive(v___x_5134_)) as u8;
                    if v_isSharedCheck_5184_ == 0 {
                        v___x_5179_ = v___x_5134_;
                        v_isShared_5180_ = v_isSharedCheck_5184_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5177_);
                        crate::leanh::lean_dec(v___x_5134_);
                        v___x_5179_ = crate::leanh::lean_box(0);
                        v_isShared_5180_ = v_isSharedCheck_5184_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_5135_) == 0 {
                    crate::leanh::lean_dec_ref(v_r_5129_);
                    crate::leanh::lean_dec_ref(v_l_5128_);
                    v___x_5139_ = crate::leanh::lean_box(0);
                    v___x_5140_ = 1;
                    v___x_5141_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5141_, 0, v_e_5112_);
                    crate::leanh::lean_ctor_set(v___x_5141_, 1, v___x_5139_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5141_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_5140_,
                    );
                    v___x_5142_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5142_, 0, v___x_5141_);
                    if v_isShared_5138_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5137_, 0, v___x_5142_);
                        v___x_5144_ = v___x_5137_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5145_, 0, v___x_5142_);
                        v___x_5144_ = v_reuseFailAlloc_5145_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5137_);
                    crate::leanh::lean_dec_ref(v_e_5112_);
                    v_val_5146_ = crate::leanh::lean_ctor_get(v_a_5135_, 0);
                    v_isSharedCheck_5175_ = (!crate::leanh::lean_is_exclusive(v_a_5135_)) as u8;
                    if v_isSharedCheck_5175_ == 0 {
                        v___x_5148_ = v_a_5135_;
                        v_isShared_5149_ = v_isSharedCheck_5175_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5146_);
                        crate::leanh::lean_dec(v_a_5135_);
                        v___x_5148_ = crate::leanh::lean_box(0);
                        v_isShared_5149_ = v_isSharedCheck_5175_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5144_;
            }
            5 => {
                v___x_5150_ = l_Lean_Meta_AC_buildNormProof(
                    v_val_5146_,
                    v_l_5128_,
                    v_r_5129_,
                    v___y_5130_,
                    v___y_5131_,
                    v___y_5132_,
                    v___y_5133_,
                );
                if crate::leanh::lean_obj_tag(v___x_5150_) == 0 {
                    v_a_5151_ = crate::leanh::lean_ctor_get(v___x_5150_, 0);
                    v_isSharedCheck_5166_ = (!crate::leanh::lean_is_exclusive(v___x_5150_)) as u8;
                    if v_isSharedCheck_5166_ == 0 {
                        v___x_5153_ = v___x_5150_;
                        v_isShared_5154_ = v_isSharedCheck_5166_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5151_);
                        crate::leanh::lean_dec(v___x_5150_);
                        v___x_5153_ = crate::leanh::lean_box(0);
                        v_isShared_5154_ = v_isSharedCheck_5166_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5148_);
                    v_a_5167_ = crate::leanh::lean_ctor_get(v___x_5150_, 0);
                    v_isSharedCheck_5174_ = (!crate::leanh::lean_is_exclusive(v___x_5150_)) as u8;
                    if v_isSharedCheck_5174_ == 0 {
                        v___x_5169_ = v___x_5150_;
                        v_isShared_5170_ = v_isSharedCheck_5174_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5167_);
                        crate::leanh::lean_dec(v___x_5150_);
                        v___x_5169_ = crate::leanh::lean_box(0);
                        v_isShared_5170_ = v_isSharedCheck_5174_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v_fst_5155_ = crate::leanh::lean_ctor_get(v_a_5151_, 0);
                crate::leanh::lean_inc(v_fst_5155_);
                v_snd_5156_ = crate::leanh::lean_ctor_get(v_a_5151_, 1);
                crate::leanh::lean_inc(v_snd_5156_);
                crate::leanh::lean_dec(v_a_5151_);
                if v_isShared_5149_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5148_, 0, v_fst_5155_);
                    v___x_5158_ = v___x_5148_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5165_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_fst_5155_);
                    v___x_5158_ = v_reuseFailAlloc_5165_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5159_ = 1;
                v___x_5160_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5160_, 0, v_snd_5156_);
                crate::leanh::lean_ctor_set(v___x_5160_, 1, v___x_5158_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5160_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5159_,
                );
                v___x_5161_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5161_, 0, v___x_5160_);
                if v_isShared_5154_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5153_, 0, v___x_5161_);
                    v___x_5163_ = v___x_5153_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5164_, 0, v___x_5161_);
                    v___x_5163_ = v_reuseFailAlloc_5164_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5163_;
            }
            9 => {
                if v_isShared_5170_ == 0 {
                    v___x_5172_ = v___x_5169_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5173_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5167_);
                    v___x_5172_ = v_reuseFailAlloc_5173_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5172_;
            }
            11 => {
                if v_isShared_5180_ == 0 {
                    v___x_5182_ = v___x_5179_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_a_5177_);
                    v___x_5182_ = v_reuseFailAlloc_5183_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5182_;
            }
            13 => {
                v___x_5198_ = 1;
                v___x_5199_ = (crate::leanh::lean_unbox(v_a_5194_) as u8);
                crate::leanh::lean_dec(v_a_5194_);
                if v___x_5199_ == 0 {
                    crate::leanh::lean_del_object(v___x_5196_);
                    crate::leanh::lean_inc_ref(v_fn_5190_);
                    v___x_5200_ = l_Lean_Meta_AC_preContext(
                        v_fn_5190_, v_a_5114_, v_a_5115_, v_a_5116_, v_a_5117_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5200_) == 0 {
                        v_a_5201_ = crate::leanh::lean_ctor_get(v___x_5200_, 0);
                        v_isSharedCheck_5240_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5200_)) as u8;
                        if v_isSharedCheck_5240_ == 0 {
                            v___x_5203_ = v___x_5200_;
                            v_isShared_5204_ = v_isSharedCheck_5240_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5201_);
                            crate::leanh::lean_dec(v___x_5200_);
                            v___x_5203_ = crate::leanh::lean_box(0);
                            v_isShared_5204_ = v_isSharedCheck_5240_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_5112_, 2);
                        v_a_5241_ = crate::leanh::lean_ctor_get(v___x_5200_, 0);
                        v_isSharedCheck_5248_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5200_)) as u8;
                        if v_isSharedCheck_5248_ == 0 {
                            v___x_5243_ = v___x_5200_;
                            v_isShared_5244_ = v_isSharedCheck_5248_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5241_);
                            crate::leanh::lean_dec(v___x_5200_);
                            v___x_5243_ = crate::leanh::lean_box(0);
                            v_isShared_5244_ = v_isSharedCheck_5248_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    v___x_5249_ = crate::leanh::lean_box(0);
                    v___x_5250_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5250_, 0, v_e_5112_);
                    crate::leanh::lean_ctor_set(v___x_5250_, 1, v___x_5249_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5250_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_5198_,
                    );
                    v___x_5251_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5251_, 0, v___x_5250_);
                    if v_isShared_5197_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5196_, 0, v___x_5251_);
                        v___x_5253_ = v___x_5196_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_5254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5251_);
                        v___x_5253_ = v_reuseFailAlloc_5254_;
                        state = 24;
                        continue;
                    }
                }
            }
            14 => {
                if crate::leanh::lean_obj_tag(v_a_5201_) == 0 {
                    v___x_5205_ = crate::leanh::lean_box(0);
                    v___x_5206_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5206_, 0, v_e_5112_);
                    crate::leanh::lean_ctor_set(v___x_5206_, 1, v___x_5205_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5206_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_5198_,
                    );
                    v___x_5207_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5207_, 0, v___x_5206_);
                    if v_isShared_5204_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5203_, 0, v___x_5207_);
                        v___x_5209_ = v___x_5203_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_5210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5210_, 0, v___x_5207_);
                        v___x_5209_ = v_reuseFailAlloc_5210_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_arg_5191_);
                    crate::leanh::lean_inc_ref(v_arg_5189_);
                    crate::leanh::lean_del_object(v___x_5203_);
                    crate::leanh::lean_dec_ref_known(v_e_5112_, 2);
                    v_val_5211_ = crate::leanh::lean_ctor_get(v_a_5201_, 0);
                    v_isSharedCheck_5239_ = (!crate::leanh::lean_is_exclusive(v_a_5201_)) as u8;
                    if v_isSharedCheck_5239_ == 0 {
                        v___x_5213_ = v_a_5201_;
                        v_isShared_5214_ = v_isSharedCheck_5239_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5211_);
                        crate::leanh::lean_dec(v_a_5201_);
                        v___x_5213_ = crate::leanh::lean_box(0);
                        v_isShared_5214_ = v_isSharedCheck_5239_;
                        state = 16;
                        continue;
                    }
                }
            }
            15 => {
                return v___x_5209_;
            }
            16 => {
                v___x_5215_ = l_Lean_Meta_AC_buildNormProof(
                    v_val_5211_,
                    v_arg_5191_,
                    v_arg_5189_,
                    v_a_5114_,
                    v_a_5115_,
                    v_a_5116_,
                    v_a_5117_,
                );
                if crate::leanh::lean_obj_tag(v___x_5215_) == 0 {
                    v_a_5216_ = crate::leanh::lean_ctor_get(v___x_5215_, 0);
                    v_isSharedCheck_5230_ = (!crate::leanh::lean_is_exclusive(v___x_5215_)) as u8;
                    if v_isSharedCheck_5230_ == 0 {
                        v___x_5218_ = v___x_5215_;
                        v_isShared_5219_ = v_isSharedCheck_5230_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5216_);
                        crate::leanh::lean_dec(v___x_5215_);
                        v___x_5218_ = crate::leanh::lean_box(0);
                        v_isShared_5219_ = v_isSharedCheck_5230_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5213_);
                    v_a_5231_ = crate::leanh::lean_ctor_get(v___x_5215_, 0);
                    v_isSharedCheck_5238_ = (!crate::leanh::lean_is_exclusive(v___x_5215_)) as u8;
                    if v_isSharedCheck_5238_ == 0 {
                        v___x_5233_ = v___x_5215_;
                        v_isShared_5234_ = v_isSharedCheck_5238_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5231_);
                        crate::leanh::lean_dec(v___x_5215_);
                        v___x_5233_ = crate::leanh::lean_box(0);
                        v_isShared_5234_ = v_isSharedCheck_5238_;
                        state = 20;
                        continue;
                    }
                }
            }
            17 => {
                v_fst_5220_ = crate::leanh::lean_ctor_get(v_a_5216_, 0);
                crate::leanh::lean_inc(v_fst_5220_);
                v_snd_5221_ = crate::leanh::lean_ctor_get(v_a_5216_, 1);
                crate::leanh::lean_inc(v_snd_5221_);
                crate::leanh::lean_dec(v_a_5216_);
                if v_isShared_5214_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5213_, 0, v_fst_5220_);
                    v___x_5223_ = v___x_5213_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5229_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_fst_5220_);
                    v___x_5223_ = v_reuseFailAlloc_5229_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_5224_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5224_, 0, v_snd_5221_);
                crate::leanh::lean_ctor_set(v___x_5224_, 1, v___x_5223_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5224_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5198_,
                );
                v___x_5225_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5225_, 0, v___x_5224_);
                if v_isShared_5219_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5218_, 0, v___x_5225_);
                    v___x_5227_ = v___x_5218_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5228_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5228_, 0, v___x_5225_);
                    v___x_5227_ = v_reuseFailAlloc_5228_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5227_;
            }
            20 => {
                if v_isShared_5234_ == 0 {
                    v___x_5236_ = v___x_5233_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5237_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_a_5231_);
                    v___x_5236_ = v_reuseFailAlloc_5237_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5236_;
            }
            22 => {
                if v_isShared_5244_ == 0 {
                    v___x_5246_ = v___x_5243_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5247_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5247_, 0, v_a_5241_);
                    v___x_5246_ = v_reuseFailAlloc_5247_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5246_;
            }
            24 => {
                return v___x_5253_;
            }
            25 => {
                if v_isShared_5259_ == 0 {
                    v___x_5261_ = v___x_5258_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
                    v___x_5261_ = v_reuseFailAlloc_5262_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_post___redArg___boxed(
    mut v_e_5273_: *mut crate::leanh::LeanObject,
    mut v_a_5274_: *mut crate::leanh::LeanObject,
    mut v_a_5275_: *mut crate::leanh::LeanObject,
    mut v_a_5276_: *mut crate::leanh::LeanObject,
    mut v_a_5277_: *mut crate::leanh::LeanObject,
    mut v_a_5278_: *mut crate::leanh::LeanObject,
    mut v_a_5279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5280_ = l_Lean_Meta_AC_post___redArg(
        v_e_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_,
    );
    crate::leanh::lean_dec(v_a_5278_);
    crate::leanh::lean_dec_ref(v_a_5277_);
    crate::leanh::lean_dec(v_a_5276_);
    crate::leanh::lean_dec_ref(v_a_5275_);
    crate::leanh::lean_dec_ref(v_a_5274_);
    return v_res_5280_;
}
pub unsafe fn l_Lean_Meta_AC_post(
    mut v_e_5281_: *mut crate::leanh::LeanObject,
    mut v_a_5282_: *mut crate::leanh::LeanObject,
    mut v_a_5283_: *mut crate::leanh::LeanObject,
    mut v_a_5284_: *mut crate::leanh::LeanObject,
    mut v_a_5285_: *mut crate::leanh::LeanObject,
    mut v_a_5286_: *mut crate::leanh::LeanObject,
    mut v_a_5287_: *mut crate::leanh::LeanObject,
    mut v_a_5288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5290_ = l_Lean_Meta_AC_post___redArg(
        v_e_5281_, v_a_5283_, v_a_5285_, v_a_5286_, v_a_5287_, v_a_5288_,
    );
    return v___x_5290_;
}
pub unsafe fn l_Lean_Meta_AC_post___boxed(
    mut v_e_5291_: *mut crate::leanh::LeanObject,
    mut v_a_5292_: *mut crate::leanh::LeanObject,
    mut v_a_5293_: *mut crate::leanh::LeanObject,
    mut v_a_5294_: *mut crate::leanh::LeanObject,
    mut v_a_5295_: *mut crate::leanh::LeanObject,
    mut v_a_5296_: *mut crate::leanh::LeanObject,
    mut v_a_5297_: *mut crate::leanh::LeanObject,
    mut v_a_5298_: *mut crate::leanh::LeanObject,
    mut v_a_5299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5300_ = l_Lean_Meta_AC_post(
        v_e_5291_, v_a_5292_, v_a_5293_, v_a_5294_, v_a_5295_, v_a_5296_, v_a_5297_, v_a_5298_,
    );
    crate::leanh::lean_dec(v_a_5298_);
    crate::leanh::lean_dec_ref(v_a_5297_);
    crate::leanh::lean_dec(v_a_5296_);
    crate::leanh::lean_dec_ref(v_a_5295_);
    crate::leanh::lean_dec(v_a_5294_);
    crate::leanh::lean_dec_ref(v_a_5293_);
    crate::leanh::lean_dec(v_a_5292_);
    return v_res_5300_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(
    mut v_e_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5304_: u8 = 0;
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5318_: u8 = 0;
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5324_: u8 = 0;
    let mut v_unused_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5304_ = l_Lean_Expr_hasMVar(v_e_5301_);
                if v___x_5304_ == 0 {
                    v___x_5305_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5305_, 0, v_e_5301_);
                    return v___x_5305_;
                } else {
                    v___x_5306_ = lean_st_ref_get(v___y_5302_);
                    v_mctx_5307_ = crate::leanh::lean_ctor_get(v___x_5306_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5307_);
                    crate::leanh::lean_dec(v___x_5306_);
                    v___x_5308_ = l_Lean_instantiateMVarsCore(v_mctx_5307_, v_e_5301_);
                    v_fst_5309_ = crate::leanh::lean_ctor_get(v___x_5308_, 0);
                    crate::leanh::lean_inc(v_fst_5309_);
                    v_snd_5310_ = crate::leanh::lean_ctor_get(v___x_5308_, 1);
                    crate::leanh::lean_inc(v_snd_5310_);
                    crate::leanh::lean_dec_ref(v___x_5308_);
                    v___x_5311_ = lean_st_ref_take(v___y_5302_);
                    v_cache_5312_ = crate::leanh::lean_ctor_get(v___x_5311_, 1);
                    v_zetaDeltaFVarIds_5313_ = crate::leanh::lean_ctor_get(v___x_5311_, 2);
                    v_postponed_5314_ = crate::leanh::lean_ctor_get(v___x_5311_, 3);
                    v_diag_5315_ = crate::leanh::lean_ctor_get(v___x_5311_, 4);
                    v_isSharedCheck_5324_ = (!crate::leanh::lean_is_exclusive(v___x_5311_)) as u8;
                    if v_isSharedCheck_5324_ == 0 {
                        v_unused_5325_ = crate::leanh::lean_ctor_get(v___x_5311_, 0);
                        crate::leanh::lean_dec(v_unused_5325_);
                        v___x_5317_ = v___x_5311_;
                        v_isShared_5318_ = v_isSharedCheck_5324_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5315_);
                        crate::leanh::lean_inc(v_postponed_5314_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5313_);
                        crate::leanh::lean_inc(v_cache_5312_);
                        crate::leanh::lean_dec(v___x_5311_);
                        v___x_5317_ = crate::leanh::lean_box(0);
                        v_isShared_5318_ = v_isSharedCheck_5324_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5318_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5317_, 0, v_snd_5310_);
                    v___x_5320_ = v___x_5317_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5323_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5323_, 0, v_snd_5310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5323_, 1, v_cache_5312_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5323_,
                        2,
                        v_zetaDeltaFVarIds_5313_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5323_, 3, v_postponed_5314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5323_, 4, v_diag_5315_);
                    v___x_5320_ = v_reuseFailAlloc_5323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5321_ = lean_st_ref_set(v___y_5302_, v___x_5320_);
                v___x_5322_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5322_, 0, v_fst_5309_);
                return v___x_5322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg___boxed(
    mut v_e_5326_: *mut crate::leanh::LeanObject,
    mut v___y_5327_: *mut crate::leanh::LeanObject,
    mut v___y_5328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5329_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(
            v_e_5326_,
            v___y_5327_,
        );
    crate::leanh::lean_dec(v___y_5327_);
    return v_res_5329_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0(
    mut v_e_5330_: *mut crate::leanh::LeanObject,
    mut v___y_5331_: *mut crate::leanh::LeanObject,
    mut v___y_5332_: *mut crate::leanh::LeanObject,
    mut v___y_5333_: *mut crate::leanh::LeanObject,
    mut v___y_5334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5336_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(
            v_e_5330_,
            v___y_5332_,
        );
    return v___x_5336_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___boxed(
    mut v_e_5337_: *mut crate::leanh::LeanObject,
    mut v___y_5338_: *mut crate::leanh::LeanObject,
    mut v___y_5339_: *mut crate::leanh::LeanObject,
    mut v___y_5340_: *mut crate::leanh::LeanObject,
    mut v___y_5341_: *mut crate::leanh::LeanObject,
    mut v___y_5342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5343_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0(
        v_e_5337_,
        v___y_5338_,
        v___y_5339_,
        v___y_5340_,
        v___y_5341_,
    );
    crate::leanh::lean_dec(v___y_5341_);
    crate::leanh::lean_dec_ref(v___y_5340_);
    crate::leanh::lean_dec(v___y_5339_);
    crate::leanh::lean_dec_ref(v___y_5338_);
    return v_res_5343_;
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalized___lam__0(
    mut v_x_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
    mut v___y_5349_: *mut crate::leanh::LeanObject,
    mut v___y_5350_: *mut crate::leanh::LeanObject,
    mut v___y_5351_: *mut crate::leanh::LeanObject,
    mut v___y_5352_: *mut crate::leanh::LeanObject,
    mut v___y_5353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5355_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__0___closed__0;
    v___x_5356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5356_, 0, v___x_5355_);
    return v___x_5356_;
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalized___lam__0___boxed(
    mut v_x_5357_: *mut crate::leanh::LeanObject,
    mut v___y_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
    mut v___y_5363_: *mut crate::leanh::LeanObject,
    mut v___y_5364_: *mut crate::leanh::LeanObject,
    mut v___y_5365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5366_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__0(
        v_x_5357_,
        v___y_5358_,
        v___y_5359_,
        v___y_5360_,
        v___y_5361_,
        v___y_5362_,
        v___y_5363_,
        v___y_5364_,
    );
    crate::leanh::lean_dec(v___y_5364_);
    crate::leanh::lean_dec_ref(v___y_5363_);
    crate::leanh::lean_dec(v___y_5362_);
    crate::leanh::lean_dec_ref(v___y_5361_);
    crate::leanh::lean_dec(v___y_5360_);
    crate::leanh::lean_dec_ref(v___y_5359_);
    crate::leanh::lean_dec(v___y_5358_);
    crate::leanh::lean_dec_ref(v_x_5357_);
    return v_res_5366_;
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalized___lam__1(
    mut v_x_5369_: *mut crate::leanh::LeanObject,
    mut v___y_5370_: *mut crate::leanh::LeanObject,
    mut v___y_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
    mut v___y_5375_: *mut crate::leanh::LeanObject,
    mut v___y_5376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5378_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__1___closed__0;
    v___x_5379_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5379_, 0, v___x_5378_);
    return v___x_5379_;
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalized___lam__1___boxed(
    mut v_x_5380_: *mut crate::leanh::LeanObject,
    mut v___y_5381_: *mut crate::leanh::LeanObject,
    mut v___y_5382_: *mut crate::leanh::LeanObject,
    mut v___y_5383_: *mut crate::leanh::LeanObject,
    mut v___y_5384_: *mut crate::leanh::LeanObject,
    mut v___y_5385_: *mut crate::leanh::LeanObject,
    mut v___y_5386_: *mut crate::leanh::LeanObject,
    mut v___y_5387_: *mut crate::leanh::LeanObject,
    mut v___y_5388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5389_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__1(
        v_x_5380_,
        v___y_5381_,
        v___y_5382_,
        v___y_5383_,
        v___y_5384_,
        v___y_5385_,
        v___y_5386_,
        v___y_5387_,
    );
    crate::leanh::lean_dec(v___y_5387_);
    crate::leanh::lean_dec_ref(v___y_5386_);
    crate::leanh::lean_dec(v___y_5385_);
    crate::leanh::lean_dec_ref(v___y_5384_);
    crate::leanh::lean_dec(v___y_5383_);
    crate::leanh::lean_dec_ref(v___y_5382_);
    crate::leanh::lean_dec(v___y_5381_);
    crate::leanh::lean_dec_ref(v_x_5380_);
    return v_res_5389_;
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalized___lam__2(
    mut v_e_5390_: *mut crate::leanh::LeanObject,
    mut v___y_5391_: *mut crate::leanh::LeanObject,
    mut v___y_5392_: *mut crate::leanh::LeanObject,
    mut v___y_5393_: *mut crate::leanh::LeanObject,
    mut v___y_5394_: *mut crate::leanh::LeanObject,
    mut v___y_5395_: *mut crate::leanh::LeanObject,
    mut v___y_5396_: *mut crate::leanh::LeanObject,
    mut v___y_5397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5399_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5399_, 0, v_e_5390_);
    v___x_5400_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5400_, 0, v___x_5399_);
    return v___x_5400_;
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalized___lam__2___boxed(
    mut v_e_5401_: *mut crate::leanh::LeanObject,
    mut v___y_5402_: *mut crate::leanh::LeanObject,
    mut v___y_5403_: *mut crate::leanh::LeanObject,
    mut v___y_5404_: *mut crate::leanh::LeanObject,
    mut v___y_5405_: *mut crate::leanh::LeanObject,
    mut v___y_5406_: *mut crate::leanh::LeanObject,
    mut v___y_5407_: *mut crate::leanh::LeanObject,
    mut v___y_5408_: *mut crate::leanh::LeanObject,
    mut v___y_5409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5410_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__2(
        v_e_5401_,
        v___y_5402_,
        v___y_5403_,
        v___y_5404_,
        v___y_5405_,
        v___y_5406_,
        v___y_5407_,
        v___y_5408_,
    );
    crate::leanh::lean_dec(v___y_5408_);
    crate::leanh::lean_dec_ref(v___y_5407_);
    crate::leanh::lean_dec(v___y_5406_);
    crate::leanh::lean_dec_ref(v___y_5405_);
    crate::leanh::lean_dec(v___y_5404_);
    crate::leanh::lean_dec_ref(v___y_5403_);
    crate::leanh::lean_dec(v___y_5402_);
    return v_res_5410_;
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalized___lam__3(
    mut v_x_5411_: *mut crate::leanh::LeanObject,
    mut v___y_5412_: *mut crate::leanh::LeanObject,
    mut v___y_5413_: *mut crate::leanh::LeanObject,
    mut v___y_5414_: *mut crate::leanh::LeanObject,
    mut v___y_5415_: *mut crate::leanh::LeanObject,
    mut v___y_5416_: *mut crate::leanh::LeanObject,
    mut v___y_5417_: *mut crate::leanh::LeanObject,
    mut v___y_5418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5420_ = crate::leanh::lean_box(0);
    v___x_5421_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5421_, 0, v___x_5420_);
    return v___x_5421_;
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalized___lam__3___boxed(
    mut v_x_5422_: *mut crate::leanh::LeanObject,
    mut v___y_5423_: *mut crate::leanh::LeanObject,
    mut v___y_5424_: *mut crate::leanh::LeanObject,
    mut v___y_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
    mut v___y_5427_: *mut crate::leanh::LeanObject,
    mut v___y_5428_: *mut crate::leanh::LeanObject,
    mut v___y_5429_: *mut crate::leanh::LeanObject,
    mut v___y_5430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5431_ = l_Lean_Meta_AC_rewriteUnnormalized___lam__3(
        v_x_5422_,
        v___y_5423_,
        v___y_5424_,
        v___y_5425_,
        v___y_5426_,
        v___y_5427_,
        v___y_5428_,
        v___y_5429_,
    );
    crate::leanh::lean_dec(v___y_5429_);
    crate::leanh::lean_dec_ref(v___y_5428_);
    crate::leanh::lean_dec(v___y_5427_);
    crate::leanh::lean_dec_ref(v___y_5426_);
    crate::leanh::lean_dec(v___y_5425_);
    crate::leanh::lean_dec_ref(v___y_5424_);
    crate::leanh::lean_dec(v___y_5423_);
    crate::leanh::lean_dec_ref(v_x_5422_);
    return v_res_5431_;
}
pub unsafe fn _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__5() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5438_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5438_;
}
pub unsafe fn _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5439_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__5_once),
        _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__5,
    );
    v___x_5440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5440_, 0, v___x_5439_);
    return v___x_5440_;
}
pub unsafe fn _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5441_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5442_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__6_once),
        _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6,
    );
    v___x_5443_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5443_, 0, v___x_5442_);
    crate::leanh::lean_ctor_set(v___x_5443_, 1, v___x_5441_);
    return v___x_5443_;
}
pub unsafe fn _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5444_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5445_ = lean_mk_empty_array_with_capacity(v___x_5444_);
    v___x_5446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5446_, 0, v___x_5445_);
    return v___x_5446_;
}
pub unsafe fn _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__9() -> *mut crate::leanh::LeanObject
{
    let mut v___x_5447_: usize = 0;
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5447_ = 5usize;
    v___x_5448_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5449_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5450_ = lean_mk_empty_array_with_capacity(v___x_5449_);
    v___x_5451_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__8_once),
        _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__8,
    );
    v___x_5452_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5452_, 0, v___x_5451_);
    crate::leanh::lean_ctor_set(v___x_5452_, 1, v___x_5450_);
    crate::leanh::lean_ctor_set(v___x_5452_, 2, v___x_5448_);
    crate::leanh::lean_ctor_set(v___x_5452_, 3, v___x_5448_);
    crate::leanh::lean_ctor_set_usize(v___x_5452_, 4, v___x_5447_);
    return v___x_5452_;
}
pub unsafe fn _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5453_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__9_once),
        _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__9,
    );
    v___x_5454_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__6_once),
        _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__6,
    );
    v___x_5455_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5455_, 0, v___x_5454_);
    crate::leanh::lean_ctor_set(v___x_5455_, 1, v___x_5454_);
    crate::leanh::lean_ctor_set(v___x_5455_, 2, v___x_5454_);
    crate::leanh::lean_ctor_set(v___x_5455_, 3, v___x_5453_);
    return v___x_5455_;
}
pub unsafe fn _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5456_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__10_once),
        _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__10,
    );
    v___x_5457_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_AC_rewriteUnnormalized___closed__7_once),
        _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__7,
    );
    v___x_5458_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5458_, 0, v___x_5457_);
    crate::leanh::lean_ctor_set(v___x_5458_, 1, v___x_5456_);
    return v___x_5458_;
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalized(
    mut v_mvarId_5467_: *mut crate::leanh::LeanObject,
    mut v_a_5468_: *mut crate::leanh::LeanObject,
    mut v_a_5469_: *mut crate::leanh::LeanObject,
    mut v_a_5470_: *mut crate::leanh::LeanObject,
    mut v_a_5471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5493_: u8 = 0;
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5497_: u8 = 0;
    let mut v_a_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5501_: u8 = 0;
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5505_: u8 = 0;
    let mut v_a_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5509_: u8 = 0;
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5513_: u8 = 0;
    let mut v_a_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5517_: u8 = 0;
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5473_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5471_);
                if crate::leanh::lean_obj_tag(v___x_5473_) == 0 {
                    v_a_5474_ = crate::leanh::lean_ctor_get(v___x_5473_, 0);
                    crate::leanh::lean_inc(v_a_5474_);
                    crate::leanh::lean_dec_ref_known(v___x_5473_, 1);
                    v___x_5475_ = l_Lean_Meta_Simp_neutralConfig;
                    v___x_5476_ = l_Lean_Meta_AC_rewriteUnnormalized___closed__0;
                    v___x_5477_ = l_Lean_Options_empty;
                    v___x_5478_ = l_Lean_Meta_Simp_mkContext___redArg(
                        v___x_5475_,
                        v___x_5476_,
                        v_a_5474_,
                        v___x_5477_,
                        v_a_5468_,
                        v_a_5470_,
                        v_a_5471_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5478_) == 0 {
                        v_a_5479_ = crate::leanh::lean_ctor_get(v___x_5478_, 0);
                        crate::leanh::lean_inc(v_a_5479_);
                        crate::leanh::lean_dec_ref_known(v___x_5478_, 1);
                        crate::leanh::lean_inc(v_mvarId_5467_);
                        v___x_5480_ = l_Lean_MVarId_getType(
                            v_mvarId_5467_,
                            v_a_5468_,
                            v_a_5469_,
                            v_a_5470_,
                            v_a_5471_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5480_) == 0 {
                            v_a_5481_ = crate::leanh::lean_ctor_get(v___x_5480_, 0);
                            crate::leanh::lean_inc(v_a_5481_);
                            crate::leanh::lean_dec_ref_known(v___x_5480_, 1);
                            v___x_5482_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_a_5481_, v_a_5469_);
                            v_a_5483_ = crate::leanh::lean_ctor_get(v___x_5482_, 0);
                            crate::leanh::lean_inc_n(v_a_5483_, 2);
                            crate::leanh::lean_dec_ref(v___x_5482_);
                            v___x_5484_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_AC_rewriteUnnormalized___closed__11
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_AC_rewriteUnnormalized___closed__11_once
                                ),
                                _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11,
                            );
                            v___x_5485_ = l_Lean_Meta_AC_rewriteUnnormalized___closed__13;
                            v___x_5486_ = l_Lean_Meta_Simp_main(
                                v_a_5483_,
                                v_a_5479_,
                                v___x_5484_,
                                v___x_5485_,
                                v_a_5468_,
                                v_a_5469_,
                                v_a_5470_,
                                v_a_5471_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5486_) == 0 {
                                v_a_5487_ = crate::leanh::lean_ctor_get(v___x_5486_, 0);
                                crate::leanh::lean_inc(v_a_5487_);
                                crate::leanh::lean_dec_ref_known(v___x_5486_, 1);
                                v_fst_5488_ = crate::leanh::lean_ctor_get(v_a_5487_, 0);
                                crate::leanh::lean_inc(v_fst_5488_);
                                crate::leanh::lean_dec(v_a_5487_);
                                v___x_5489_ = l_Lean_Meta_applySimpResultToTarget(
                                    v_mvarId_5467_,
                                    v_a_5483_,
                                    v_fst_5488_,
                                    v_a_5468_,
                                    v_a_5469_,
                                    v_a_5470_,
                                    v_a_5471_,
                                );
                                crate::leanh::lean_dec(v_a_5483_);
                                return v___x_5489_;
                            } else {
                                crate::leanh::lean_dec(v_a_5483_);
                                crate::leanh::lean_dec(v_mvarId_5467_);
                                v_a_5490_ = crate::leanh::lean_ctor_get(v___x_5486_, 0);
                                v_isSharedCheck_5497_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5486_)) as u8;
                                if v_isSharedCheck_5497_ == 0 {
                                    v___x_5492_ = v___x_5486_;
                                    v_isShared_5493_ = v_isSharedCheck_5497_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5490_);
                                    crate::leanh::lean_dec(v___x_5486_);
                                    v___x_5492_ = crate::leanh::lean_box(0);
                                    v_isShared_5493_ = v_isSharedCheck_5497_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5479_);
                            crate::leanh::lean_dec(v_mvarId_5467_);
                            v_a_5498_ = crate::leanh::lean_ctor_get(v___x_5480_, 0);
                            v_isSharedCheck_5505_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5480_)) as u8;
                            if v_isSharedCheck_5505_ == 0 {
                                v___x_5500_ = v___x_5480_;
                                v_isShared_5501_ = v_isSharedCheck_5505_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5498_);
                                crate::leanh::lean_dec(v___x_5480_);
                                v___x_5500_ = crate::leanh::lean_box(0);
                                v_isShared_5501_ = v_isSharedCheck_5505_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_5467_);
                        v_a_5506_ = crate::leanh::lean_ctor_get(v___x_5478_, 0);
                        v_isSharedCheck_5513_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5478_)) as u8;
                        if v_isSharedCheck_5513_ == 0 {
                            v___x_5508_ = v___x_5478_;
                            v_isShared_5509_ = v_isSharedCheck_5513_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5506_);
                            crate::leanh::lean_dec(v___x_5478_);
                            v___x_5508_ = crate::leanh::lean_box(0);
                            v_isShared_5509_ = v_isSharedCheck_5513_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_5467_);
                    v_a_5514_ = crate::leanh::lean_ctor_get(v___x_5473_, 0);
                    v_isSharedCheck_5521_ = (!crate::leanh::lean_is_exclusive(v___x_5473_)) as u8;
                    if v_isSharedCheck_5521_ == 0 {
                        v___x_5516_ = v___x_5473_;
                        v_isShared_5517_ = v_isSharedCheck_5521_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5514_);
                        crate::leanh::lean_dec(v___x_5473_);
                        v___x_5516_ = crate::leanh::lean_box(0);
                        v_isShared_5517_ = v_isSharedCheck_5521_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5493_ == 0 {
                    v___x_5495_ = v___x_5492_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5496_, 0, v_a_5490_);
                    v___x_5495_ = v_reuseFailAlloc_5496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5495_;
            }
            3 => {
                if v_isShared_5501_ == 0 {
                    v___x_5503_ = v___x_5500_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_a_5498_);
                    v___x_5503_ = v_reuseFailAlloc_5504_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5503_;
            }
            5 => {
                if v_isShared_5509_ == 0 {
                    v___x_5511_ = v___x_5508_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_a_5506_);
                    v___x_5511_ = v_reuseFailAlloc_5512_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5511_;
            }
            7 => {
                if v_isShared_5517_ == 0 {
                    v___x_5519_ = v___x_5516_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5520_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_a_5514_);
                    v___x_5519_ = v_reuseFailAlloc_5520_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalized___boxed(
    mut v_mvarId_5522_: *mut crate::leanh::LeanObject,
    mut v_a_5523_: *mut crate::leanh::LeanObject,
    mut v_a_5524_: *mut crate::leanh::LeanObject,
    mut v_a_5525_: *mut crate::leanh::LeanObject,
    mut v_a_5526_: *mut crate::leanh::LeanObject,
    mut v_a_5527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5528_ = l_Lean_Meta_AC_rewriteUnnormalized(
        v_mvarId_5522_,
        v_a_5523_,
        v_a_5524_,
        v_a_5525_,
        v_a_5526_,
    );
    crate::leanh::lean_dec(v_a_5526_);
    crate::leanh::lean_dec_ref(v_a_5525_);
    crate::leanh::lean_dec(v_a_5524_);
    crate::leanh::lean_dec_ref(v_a_5523_);
    return v_res_5528_;
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalizedRefl(
    mut v_goal_5529_: *mut crate::leanh::LeanObject,
    mut v_a_5530_: *mut crate::leanh::LeanObject,
    mut v_a_5531_: *mut crate::leanh::LeanObject,
    mut v_a_5532_: *mut crate::leanh::LeanObject,
    mut v_a_5533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: u8 = 0;
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5542_: u8 = 0;
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5535_ = l_Lean_Meta_AC_rewriteUnnormalized(
                    v_goal_5529_,
                    v_a_5530_,
                    v_a_5531_,
                    v_a_5532_,
                    v_a_5533_,
                );
                if crate::leanh::lean_obj_tag(v___x_5535_) == 0 {
                    v_a_5536_ = crate::leanh::lean_ctor_get(v___x_5535_, 0);
                    crate::leanh::lean_inc(v_a_5536_);
                    crate::leanh::lean_dec_ref_known(v___x_5535_, 1);
                    v___x_5537_ = 1;
                    v___x_5538_ = l_Lean_MVarId_refl(
                        v_a_5536_,
                        v___x_5537_,
                        v_a_5530_,
                        v_a_5531_,
                        v_a_5532_,
                        v_a_5533_,
                    );
                    return v___x_5538_;
                } else {
                    v_a_5539_ = crate::leanh::lean_ctor_get(v___x_5535_, 0);
                    v_isSharedCheck_5546_ = (!crate::leanh::lean_is_exclusive(v___x_5535_)) as u8;
                    if v_isSharedCheck_5546_ == 0 {
                        v___x_5541_ = v___x_5535_;
                        v_isShared_5542_ = v_isSharedCheck_5546_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5539_);
                        crate::leanh::lean_dec(v___x_5535_);
                        v___x_5541_ = crate::leanh::lean_box(0);
                        v_isShared_5542_ = v_isSharedCheck_5546_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5542_ == 0 {
                    v___x_5544_ = v___x_5541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5545_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_a_5539_);
                    v___x_5544_ = v_reuseFailAlloc_5545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_rewriteUnnormalizedRefl___boxed(
    mut v_goal_5547_: *mut crate::leanh::LeanObject,
    mut v_a_5548_: *mut crate::leanh::LeanObject,
    mut v_a_5549_: *mut crate::leanh::LeanObject,
    mut v_a_5550_: *mut crate::leanh::LeanObject,
    mut v_a_5551_: *mut crate::leanh::LeanObject,
    mut v_a_5552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5553_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(
        v_goal_5547_,
        v_a_5548_,
        v_a_5549_,
        v_a_5550_,
        v_a_5551_,
    );
    crate::leanh::lean_dec(v_a_5551_);
    crate::leanh::lean_dec_ref(v_a_5550_);
    crate::leanh::lean_dec(v_a_5549_);
    crate::leanh::lean_dec_ref(v_a_5548_);
    return v_res_5553_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0(
    mut v_x_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
    mut v___y_5558_: *mut crate::leanh::LeanObject,
    mut v___y_5559_: *mut crate::leanh::LeanObject,
    mut v___y_5560_: *mut crate::leanh::LeanObject,
    mut v___y_5561_: *mut crate::leanh::LeanObject,
    mut v___y_5562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5558_);
    crate::leanh::lean_inc_ref(v___y_5557_);
    crate::leanh::lean_inc(v___y_5556_);
    crate::leanh::lean_inc_ref(v___y_5555_);
    v___x_5564_ = crate::leanh::lean_apply_9(
        v_x_5554_,
        v___y_5555_,
        v___y_5556_,
        v___y_5557_,
        v___y_5558_,
        v___y_5559_,
        v___y_5560_,
        v___y_5561_,
        v___y_5562_,
        crate::leanh::lean_box(0),
    );
    return v___x_5564_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0___boxed(
    mut v_x_5565_: *mut crate::leanh::LeanObject,
    mut v___y_5566_: *mut crate::leanh::LeanObject,
    mut v___y_5567_: *mut crate::leanh::LeanObject,
    mut v___y_5568_: *mut crate::leanh::LeanObject,
    mut v___y_5569_: *mut crate::leanh::LeanObject,
    mut v___y_5570_: *mut crate::leanh::LeanObject,
    mut v___y_5571_: *mut crate::leanh::LeanObject,
    mut v___y_5572_: *mut crate::leanh::LeanObject,
    mut v___y_5573_: *mut crate::leanh::LeanObject,
    mut v___y_5574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5575_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0(
            v_x_5565_,
            v___y_5566_,
            v___y_5567_,
            v___y_5568_,
            v___y_5569_,
            v___y_5570_,
            v___y_5571_,
            v___y_5572_,
            v___y_5573_,
        );
    crate::leanh::lean_dec(v___y_5569_);
    crate::leanh::lean_dec_ref(v___y_5568_);
    crate::leanh::lean_dec(v___y_5567_);
    crate::leanh::lean_dec_ref(v___y_5566_);
    return v_res_5575_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(
    mut v_mvarId_5576_: *mut crate::leanh::LeanObject,
    mut v_x_5577_: *mut crate::leanh::LeanObject,
    mut v___y_5578_: *mut crate::leanh::LeanObject,
    mut v___y_5579_: *mut crate::leanh::LeanObject,
    mut v___y_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
    mut v___y_5583_: *mut crate::leanh::LeanObject,
    mut v___y_5584_: *mut crate::leanh::LeanObject,
    mut v___y_5585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5592_: u8 = 0;
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5596_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5581_);
                crate::leanh::lean_inc_ref(v___y_5580_);
                crate::leanh::lean_inc(v___y_5579_);
                crate::leanh::lean_inc_ref(v___y_5578_);
                v___f_5587_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_5587_, 0, v_x_5577_);
                crate::leanh::lean_closure_set(v___f_5587_, 1, v___y_5578_);
                crate::leanh::lean_closure_set(v___f_5587_, 2, v___y_5579_);
                crate::leanh::lean_closure_set(v___f_5587_, 3, v___y_5580_);
                crate::leanh::lean_closure_set(v___f_5587_, 4, v___y_5581_);
                v___x_5588_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_5576_,
                    v___f_5587_,
                    v___y_5582_,
                    v___y_5583_,
                    v___y_5584_,
                    v___y_5585_,
                );
                if crate::leanh::lean_obj_tag(v___x_5588_) == 0 {
                    return v___x_5588_;
                } else {
                    v_a_5589_ = crate::leanh::lean_ctor_get(v___x_5588_, 0);
                    v_isSharedCheck_5596_ = (!crate::leanh::lean_is_exclusive(v___x_5588_)) as u8;
                    if v_isSharedCheck_5596_ == 0 {
                        v___x_5591_ = v___x_5588_;
                        v_isShared_5592_ = v_isSharedCheck_5596_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5589_);
                        crate::leanh::lean_dec(v___x_5588_);
                        v___x_5591_ = crate::leanh::lean_box(0);
                        v_isShared_5592_ = v_isSharedCheck_5596_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5592_ == 0 {
                    v___x_5594_ = v___x_5591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5595_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_a_5589_);
                    v___x_5594_ = v_reuseFailAlloc_5595_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5594_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg___boxed(
    mut v_mvarId_5597_: *mut crate::leanh::LeanObject,
    mut v_x_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
    mut v___y_5600_: *mut crate::leanh::LeanObject,
    mut v___y_5601_: *mut crate::leanh::LeanObject,
    mut v___y_5602_: *mut crate::leanh::LeanObject,
    mut v___y_5603_: *mut crate::leanh::LeanObject,
    mut v___y_5604_: *mut crate::leanh::LeanObject,
    mut v___y_5605_: *mut crate::leanh::LeanObject,
    mut v___y_5606_: *mut crate::leanh::LeanObject,
    mut v___y_5607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5608_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(
        v_mvarId_5597_,
        v_x_5598_,
        v___y_5599_,
        v___y_5600_,
        v___y_5601_,
        v___y_5602_,
        v___y_5603_,
        v___y_5604_,
        v___y_5605_,
        v___y_5606_,
    );
    crate::leanh::lean_dec(v___y_5606_);
    crate::leanh::lean_dec_ref(v___y_5605_);
    crate::leanh::lean_dec(v___y_5604_);
    crate::leanh::lean_dec_ref(v___y_5603_);
    crate::leanh::lean_dec(v___y_5602_);
    crate::leanh::lean_dec_ref(v___y_5601_);
    crate::leanh::lean_dec(v___y_5600_);
    crate::leanh::lean_dec_ref(v___y_5599_);
    return v_res_5608_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0(
    mut v_00_u03b1_5609_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5610_: *mut crate::leanh::LeanObject,
    mut v_x_5611_: *mut crate::leanh::LeanObject,
    mut v___y_5612_: *mut crate::leanh::LeanObject,
    mut v___y_5613_: *mut crate::leanh::LeanObject,
    mut v___y_5614_: *mut crate::leanh::LeanObject,
    mut v___y_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
    mut v___y_5617_: *mut crate::leanh::LeanObject,
    mut v___y_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5621_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(
        v_mvarId_5610_,
        v_x_5611_,
        v___y_5612_,
        v___y_5613_,
        v___y_5614_,
        v___y_5615_,
        v___y_5616_,
        v___y_5617_,
        v___y_5618_,
        v___y_5619_,
    );
    return v___x_5621_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___boxed(
    mut v_00_u03b1_5622_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5623_: *mut crate::leanh::LeanObject,
    mut v_x_5624_: *mut crate::leanh::LeanObject,
    mut v___y_5625_: *mut crate::leanh::LeanObject,
    mut v___y_5626_: *mut crate::leanh::LeanObject,
    mut v___y_5627_: *mut crate::leanh::LeanObject,
    mut v___y_5628_: *mut crate::leanh::LeanObject,
    mut v___y_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
    mut v___y_5631_: *mut crate::leanh::LeanObject,
    mut v___y_5632_: *mut crate::leanh::LeanObject,
    mut v___y_5633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5634_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0(
        v_00_u03b1_5622_,
        v_mvarId_5623_,
        v_x_5624_,
        v___y_5625_,
        v___y_5626_,
        v___y_5627_,
        v___y_5628_,
        v___y_5629_,
        v___y_5630_,
        v___y_5631_,
        v___y_5632_,
    );
    crate::leanh::lean_dec(v___y_5632_);
    crate::leanh::lean_dec_ref(v___y_5631_);
    crate::leanh::lean_dec(v___y_5630_);
    crate::leanh::lean_dec_ref(v___y_5629_);
    crate::leanh::lean_dec(v___y_5628_);
    crate::leanh::lean_dec_ref(v___y_5627_);
    crate::leanh::lean_dec(v___y_5626_);
    crate::leanh::lean_dec_ref(v___y_5625_);
    return v_res_5634_;
}
pub unsafe fn l_Lean_Meta_AC_acRflTactic___redArg___lam__0(
    mut v_a_5635_: *mut crate::leanh::LeanObject,
    mut v___y_5636_: *mut crate::leanh::LeanObject,
    mut v___y_5637_: *mut crate::leanh::LeanObject,
    mut v___y_5638_: *mut crate::leanh::LeanObject,
    mut v___y_5639_: *mut crate::leanh::LeanObject,
    mut v___y_5640_: *mut crate::leanh::LeanObject,
    mut v___y_5641_: *mut crate::leanh::LeanObject,
    mut v___y_5642_: *mut crate::leanh::LeanObject,
    mut v___y_5643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5645_ = l_Lean_Meta_AC_rewriteUnnormalizedRefl(
        v_a_5635_,
        v___y_5640_,
        v___y_5641_,
        v___y_5642_,
        v___y_5643_,
    );
    return v___x_5645_;
}
pub unsafe fn l_Lean_Meta_AC_acRflTactic___redArg___lam__0___boxed(
    mut v_a_5646_: *mut crate::leanh::LeanObject,
    mut v___y_5647_: *mut crate::leanh::LeanObject,
    mut v___y_5648_: *mut crate::leanh::LeanObject,
    mut v___y_5649_: *mut crate::leanh::LeanObject,
    mut v___y_5650_: *mut crate::leanh::LeanObject,
    mut v___y_5651_: *mut crate::leanh::LeanObject,
    mut v___y_5652_: *mut crate::leanh::LeanObject,
    mut v___y_5653_: *mut crate::leanh::LeanObject,
    mut v___y_5654_: *mut crate::leanh::LeanObject,
    mut v___y_5655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5656_ = l_Lean_Meta_AC_acRflTactic___redArg___lam__0(
        v_a_5646_,
        v___y_5647_,
        v___y_5648_,
        v___y_5649_,
        v___y_5650_,
        v___y_5651_,
        v___y_5652_,
        v___y_5653_,
        v___y_5654_,
    );
    crate::leanh::lean_dec(v___y_5654_);
    crate::leanh::lean_dec_ref(v___y_5653_);
    crate::leanh::lean_dec(v___y_5652_);
    crate::leanh::lean_dec_ref(v___y_5651_);
    crate::leanh::lean_dec(v___y_5650_);
    crate::leanh::lean_dec_ref(v___y_5649_);
    crate::leanh::lean_dec(v___y_5648_);
    crate::leanh::lean_dec_ref(v___y_5647_);
    return v_res_5656_;
}
pub unsafe fn l_Lean_Meta_AC_acRflTactic___redArg(
    mut v_a_5657_: *mut crate::leanh::LeanObject,
    mut v_a_5658_: *mut crate::leanh::LeanObject,
    mut v_a_5659_: *mut crate::leanh::LeanObject,
    mut v_a_5660_: *mut crate::leanh::LeanObject,
    mut v_a_5661_: *mut crate::leanh::LeanObject,
    mut v_a_5662_: *mut crate::leanh::LeanObject,
    mut v_a_5663_: *mut crate::leanh::LeanObject,
    mut v_a_5664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5673_: u8 = 0;
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5666_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_5658_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_,
                );
                if crate::leanh::lean_obj_tag(v___x_5666_) == 0 {
                    v_a_5667_ = crate::leanh::lean_ctor_get(v___x_5666_, 0);
                    crate::leanh::lean_inc_n(v_a_5667_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5666_, 1);
                    v___f_5668_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_AC_acRflTactic___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5668_, 0, v_a_5667_);
                    v___x_5669_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acRflTactic_spec__0___redArg(v_a_5667_, v___f_5668_, v_a_5657_, v_a_5658_, v_a_5659_, v_a_5660_, v_a_5661_, v_a_5662_, v_a_5663_, v_a_5664_);
                    return v___x_5669_;
                } else {
                    v_a_5670_ = crate::leanh::lean_ctor_get(v___x_5666_, 0);
                    v_isSharedCheck_5677_ = (!crate::leanh::lean_is_exclusive(v___x_5666_)) as u8;
                    if v_isSharedCheck_5677_ == 0 {
                        v___x_5672_ = v___x_5666_;
                        v_isShared_5673_ = v_isSharedCheck_5677_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5670_);
                        crate::leanh::lean_dec(v___x_5666_);
                        v___x_5672_ = crate::leanh::lean_box(0);
                        v_isShared_5673_ = v_isSharedCheck_5677_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5673_ == 0 {
                    v___x_5675_ = v___x_5672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5676_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_a_5670_);
                    v___x_5675_ = v_reuseFailAlloc_5676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_acRflTactic___redArg___boxed(
    mut v_a_5678_: *mut crate::leanh::LeanObject,
    mut v_a_5679_: *mut crate::leanh::LeanObject,
    mut v_a_5680_: *mut crate::leanh::LeanObject,
    mut v_a_5681_: *mut crate::leanh::LeanObject,
    mut v_a_5682_: *mut crate::leanh::LeanObject,
    mut v_a_5683_: *mut crate::leanh::LeanObject,
    mut v_a_5684_: *mut crate::leanh::LeanObject,
    mut v_a_5685_: *mut crate::leanh::LeanObject,
    mut v_a_5686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5687_ = l_Lean_Meta_AC_acRflTactic___redArg(
        v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_, v_a_5683_, v_a_5684_, v_a_5685_,
    );
    crate::leanh::lean_dec(v_a_5685_);
    crate::leanh::lean_dec_ref(v_a_5684_);
    crate::leanh::lean_dec(v_a_5683_);
    crate::leanh::lean_dec_ref(v_a_5682_);
    crate::leanh::lean_dec(v_a_5681_);
    crate::leanh::lean_dec_ref(v_a_5680_);
    crate::leanh::lean_dec(v_a_5679_);
    crate::leanh::lean_dec_ref(v_a_5678_);
    return v_res_5687_;
}
pub unsafe fn l_Lean_Meta_AC_acRflTactic(
    mut v_x_5688_: *mut crate::leanh::LeanObject,
    mut v_a_5689_: *mut crate::leanh::LeanObject,
    mut v_a_5690_: *mut crate::leanh::LeanObject,
    mut v_a_5691_: *mut crate::leanh::LeanObject,
    mut v_a_5692_: *mut crate::leanh::LeanObject,
    mut v_a_5693_: *mut crate::leanh::LeanObject,
    mut v_a_5694_: *mut crate::leanh::LeanObject,
    mut v_a_5695_: *mut crate::leanh::LeanObject,
    mut v_a_5696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5698_ = l_Lean_Meta_AC_acRflTactic___redArg(
        v_a_5689_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_,
    );
    return v___x_5698_;
}
pub unsafe fn l_Lean_Meta_AC_acRflTactic___boxed(
    mut v_x_5699_: *mut crate::leanh::LeanObject,
    mut v_a_5700_: *mut crate::leanh::LeanObject,
    mut v_a_5701_: *mut crate::leanh::LeanObject,
    mut v_a_5702_: *mut crate::leanh::LeanObject,
    mut v_a_5703_: *mut crate::leanh::LeanObject,
    mut v_a_5704_: *mut crate::leanh::LeanObject,
    mut v_a_5705_: *mut crate::leanh::LeanObject,
    mut v_a_5706_: *mut crate::leanh::LeanObject,
    mut v_a_5707_: *mut crate::leanh::LeanObject,
    mut v_a_5708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5709_ = l_Lean_Meta_AC_acRflTactic(
        v_x_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_,
        v_a_5707_,
    );
    crate::leanh::lean_dec(v_a_5707_);
    crate::leanh::lean_dec_ref(v_a_5706_);
    crate::leanh::lean_dec(v_a_5705_);
    crate::leanh::lean_dec_ref(v_a_5704_);
    crate::leanh::lean_dec(v_a_5703_);
    crate::leanh::lean_dec_ref(v_a_5702_);
    crate::leanh::lean_dec(v_a_5701_);
    crate::leanh::lean_dec_ref(v_a_5700_);
    crate::leanh::lean_dec(v_x_5699_);
    return v_res_5709_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5725_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5726_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__3;
    v___x_5727_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5;
    v___x_5728_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_AC_acRflTactic___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5729_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5725_,
        v___x_5726_,
        v___x_5727_,
        v___x_5728_,
    );
    return v___x_5729_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___boxed(
    mut v_a_5730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5731_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1();
    return v_res_5731_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5758_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1___closed__5;
    v___x_5759_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___closed__6;
    v___x_5760_ = l_Lean_addBuiltinDeclarationRanges(v___x_5758_, v___x_5759_);
    return v___x_5760_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3___boxed(
    mut v_a_5761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5762_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3();
    return v_res_5762_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(
    mut v_mvarId_5763_: *mut crate::leanh::LeanObject,
    mut v_x_5764_: *mut crate::leanh::LeanObject,
    mut v___y_5765_: *mut crate::leanh::LeanObject,
    mut v___y_5766_: *mut crate::leanh::LeanObject,
    mut v___y_5767_: *mut crate::leanh::LeanObject,
    mut v___y_5768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5774_: u8 = 0;
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5778_: u8 = 0;
    let mut v_a_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5782_: u8 = 0;
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5770_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_5763_,
                    v_x_5764_,
                    v___y_5765_,
                    v___y_5766_,
                    v___y_5767_,
                    v___y_5768_,
                );
                if crate::leanh::lean_obj_tag(v___x_5770_) == 0 {
                    v_a_5771_ = crate::leanh::lean_ctor_get(v___x_5770_, 0);
                    v_isSharedCheck_5778_ = (!crate::leanh::lean_is_exclusive(v___x_5770_)) as u8;
                    if v_isSharedCheck_5778_ == 0 {
                        v___x_5773_ = v___x_5770_;
                        v_isShared_5774_ = v_isSharedCheck_5778_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5771_);
                        crate::leanh::lean_dec(v___x_5770_);
                        v___x_5773_ = crate::leanh::lean_box(0);
                        v_isShared_5774_ = v_isSharedCheck_5778_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5779_ = crate::leanh::lean_ctor_get(v___x_5770_, 0);
                    v_isSharedCheck_5786_ = (!crate::leanh::lean_is_exclusive(v___x_5770_)) as u8;
                    if v_isSharedCheck_5786_ == 0 {
                        v___x_5781_ = v___x_5770_;
                        v_isShared_5782_ = v_isSharedCheck_5786_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5779_);
                        crate::leanh::lean_dec(v___x_5770_);
                        v___x_5781_ = crate::leanh::lean_box(0);
                        v_isShared_5782_ = v_isSharedCheck_5786_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5774_ == 0 {
                    v___x_5776_ = v___x_5773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5777_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_a_5771_);
                    v___x_5776_ = v_reuseFailAlloc_5777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5776_;
            }
            3 => {
                if v_isShared_5782_ == 0 {
                    v___x_5784_ = v___x_5781_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5785_, 0, v_a_5779_);
                    v___x_5784_ = v_reuseFailAlloc_5785_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg___boxed(
    mut v_mvarId_5787_: *mut crate::leanh::LeanObject,
    mut v_x_5788_: *mut crate::leanh::LeanObject,
    mut v___y_5789_: *mut crate::leanh::LeanObject,
    mut v___y_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
    mut v___y_5792_: *mut crate::leanh::LeanObject,
    mut v___y_5793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5794_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(
        v_mvarId_5787_,
        v_x_5788_,
        v___y_5789_,
        v___y_5790_,
        v___y_5791_,
        v___y_5792_,
    );
    crate::leanh::lean_dec(v___y_5792_);
    crate::leanh::lean_dec_ref(v___y_5791_);
    crate::leanh::lean_dec(v___y_5790_);
    crate::leanh::lean_dec_ref(v___y_5789_);
    return v_res_5794_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0(
    mut v_00_u03b1_5795_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5796_: *mut crate::leanh::LeanObject,
    mut v_x_5797_: *mut crate::leanh::LeanObject,
    mut v___y_5798_: *mut crate::leanh::LeanObject,
    mut v___y_5799_: *mut crate::leanh::LeanObject,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
    mut v___y_5801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5803_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(
        v_mvarId_5796_,
        v_x_5797_,
        v___y_5798_,
        v___y_5799_,
        v___y_5800_,
        v___y_5801_,
    );
    return v___x_5803_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___boxed(
    mut v_00_u03b1_5804_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5805_: *mut crate::leanh::LeanObject,
    mut v_x_5806_: *mut crate::leanh::LeanObject,
    mut v___y_5807_: *mut crate::leanh::LeanObject,
    mut v___y_5808_: *mut crate::leanh::LeanObject,
    mut v___y_5809_: *mut crate::leanh::LeanObject,
    mut v___y_5810_: *mut crate::leanh::LeanObject,
    mut v___y_5811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5812_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0(
        v_00_u03b1_5804_,
        v_mvarId_5805_,
        v_x_5806_,
        v___y_5807_,
        v___y_5808_,
        v___y_5809_,
        v___y_5810_,
    );
    crate::leanh::lean_dec(v___y_5810_);
    crate::leanh::lean_dec_ref(v___y_5809_);
    crate::leanh::lean_dec(v___y_5808_);
    crate::leanh::lean_dec_ref(v___y_5807_);
    return v_res_5812_;
}
pub unsafe fn l_Lean_Meta_AC_acNfHypMeta___lam__4(
    mut v_fvarId_5813_: *mut crate::leanh::LeanObject,
    mut v___f_5814_: *mut crate::leanh::LeanObject,
    mut v___f_5815_: *mut crate::leanh::LeanObject,
    mut v___f_5816_: *mut crate::leanh::LeanObject,
    mut v___f_5817_: *mut crate::leanh::LeanObject,
    mut v_goal_5818_: *mut crate::leanh::LeanObject,
    mut v___y_5819_: *mut crate::leanh::LeanObject,
    mut v___y_5820_: *mut crate::leanh::LeanObject,
    mut v___y_5821_: *mut crate::leanh::LeanObject,
    mut v___y_5822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: u8 = 0;
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: u8 = 0;
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5849_: u8 = 0;
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5857_: u8 = 0;
    let mut v_snd_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5865_: u8 = 0;
    let mut v_isSharedCheck_5866_: u8 = 0;
    let mut v_a_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5870_: u8 = 0;
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5874_: u8 = 0;
    let mut v_a_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5878_: u8 = 0;
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5882_: u8 = 0;
    let mut v_a_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5886_: u8 = 0;
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5890_: u8 = 0;
    let mut v_a_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5894_: u8 = 0;
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5898_: u8 = 0;
    let mut v_a_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5902_: u8 = 0;
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5824_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_5822_);
                if crate::leanh::lean_obj_tag(v___x_5824_) == 0 {
                    v_a_5825_ = crate::leanh::lean_ctor_get(v___x_5824_, 0);
                    crate::leanh::lean_inc(v_a_5825_);
                    crate::leanh::lean_dec_ref_known(v___x_5824_, 1);
                    v___x_5826_ = l_Lean_Meta_Simp_neutralConfig;
                    v___x_5827_ = l_Lean_Meta_AC_rewriteUnnormalized___closed__0;
                    v___x_5828_ = l_Lean_Options_empty;
                    v___x_5829_ = l_Lean_Meta_Simp_mkContext___redArg(
                        v___x_5826_,
                        v___x_5827_,
                        v_a_5825_,
                        v___x_5828_,
                        v___y_5819_,
                        v___y_5821_,
                        v___y_5822_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5829_) == 0 {
                        v_a_5830_ = crate::leanh::lean_ctor_get(v___x_5829_, 0);
                        crate::leanh::lean_inc(v_a_5830_);
                        crate::leanh::lean_dec_ref_known(v___x_5829_, 1);
                        crate::leanh::lean_inc(v_fvarId_5813_);
                        v___x_5831_ = l_Lean_FVarId_getType___redArg(
                            v_fvarId_5813_,
                            v___y_5819_,
                            v___y_5821_,
                            v___y_5822_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5831_) == 0 {
                            v_a_5832_ = crate::leanh::lean_ctor_get(v___x_5831_, 0);
                            crate::leanh::lean_inc(v_a_5832_);
                            crate::leanh::lean_dec_ref_known(v___x_5831_, 1);
                            v___x_5833_ = l_Lean_instantiateMVars___at___00Lean_Meta_AC_rewriteUnnormalized_spec__0___redArg(v_a_5832_, v___y_5820_);
                            v_a_5834_ = crate::leanh::lean_ctor_get(v___x_5833_, 0);
                            crate::leanh::lean_inc(v_a_5834_);
                            crate::leanh::lean_dec_ref(v___x_5833_);
                            v___x_5835_ = crate::leanh::lean_unsigned_to_nat(32);
                            v___x_5836_ = lean_mk_empty_array_with_capacity(v___x_5835_);
                            crate::leanh::lean_dec_ref(v___x_5836_);
                            v___x_5837_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_AC_rewriteUnnormalized___closed__11
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_AC_rewriteUnnormalized___closed__11_once
                                ),
                                _init_l_Lean_Meta_AC_rewriteUnnormalized___closed__11,
                            );
                            v___x_5838_ = l_Lean_Meta_AC_rewriteUnnormalized___closed__12;
                            v___x_5839_ = 1;
                            v___x_5840_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_5840_, 0, v___f_5814_);
                            crate::leanh::lean_ctor_set(v___x_5840_, 1, v___x_5838_);
                            crate::leanh::lean_ctor_set(v___x_5840_, 2, v___f_5815_);
                            crate::leanh::lean_ctor_set(v___x_5840_, 3, v___f_5816_);
                            crate::leanh::lean_ctor_set(v___x_5840_, 4, v___f_5817_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_5840_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                                v___x_5839_,
                            );
                            v___x_5841_ = l_Lean_Meta_Simp_main(
                                v_a_5834_,
                                v_a_5830_,
                                v___x_5837_,
                                v___x_5840_,
                                v___y_5819_,
                                v___y_5820_,
                                v___y_5821_,
                                v___y_5822_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5841_) == 0 {
                                v_a_5842_ = crate::leanh::lean_ctor_get(v___x_5841_, 0);
                                crate::leanh::lean_inc(v_a_5842_);
                                crate::leanh::lean_dec_ref_known(v___x_5841_, 1);
                                v_fst_5843_ = crate::leanh::lean_ctor_get(v_a_5842_, 0);
                                crate::leanh::lean_inc(v_fst_5843_);
                                crate::leanh::lean_dec(v_a_5842_);
                                v___x_5844_ = 0;
                                v___x_5845_ = l_Lean_Meta_applySimpResultToLocalDecl(
                                    v_goal_5818_,
                                    v_fvarId_5813_,
                                    v_fst_5843_,
                                    v___x_5844_,
                                    v___y_5819_,
                                    v___y_5820_,
                                    v___y_5821_,
                                    v___y_5822_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5845_) == 0 {
                                    v_a_5846_ = crate::leanh::lean_ctor_get(v___x_5845_, 0);
                                    v_isSharedCheck_5866_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5845_)) as u8;
                                    if v_isSharedCheck_5866_ == 0 {
                                        v___x_5848_ = v___x_5845_;
                                        v_isShared_5849_ = v_isSharedCheck_5866_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5846_);
                                        crate::leanh::lean_dec(v___x_5845_);
                                        v___x_5848_ = crate::leanh::lean_box(0);
                                        v_isShared_5849_ = v_isSharedCheck_5866_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_5867_ = crate::leanh::lean_ctor_get(v___x_5845_, 0);
                                    v_isSharedCheck_5874_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5845_)) as u8;
                                    if v_isSharedCheck_5874_ == 0 {
                                        v___x_5869_ = v___x_5845_;
                                        v_isShared_5870_ = v_isSharedCheck_5874_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5867_);
                                        crate::leanh::lean_dec(v___x_5845_);
                                        v___x_5869_ = crate::leanh::lean_box(0);
                                        v_isShared_5870_ = v_isSharedCheck_5874_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_goal_5818_);
                                crate::leanh::lean_dec(v_fvarId_5813_);
                                v_a_5875_ = crate::leanh::lean_ctor_get(v___x_5841_, 0);
                                v_isSharedCheck_5882_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5841_)) as u8;
                                if v_isSharedCheck_5882_ == 0 {
                                    v___x_5877_ = v___x_5841_;
                                    v_isShared_5878_ = v_isSharedCheck_5882_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5875_);
                                    crate::leanh::lean_dec(v___x_5841_);
                                    v___x_5877_ = crate::leanh::lean_box(0);
                                    v_isShared_5878_ = v_isSharedCheck_5882_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5830_);
                            crate::leanh::lean_dec(v_goal_5818_);
                            crate::leanh::lean_dec_ref(v___f_5817_);
                            crate::leanh::lean_dec_ref(v___f_5816_);
                            crate::leanh::lean_dec_ref(v___f_5815_);
                            crate::leanh::lean_dec_ref(v___f_5814_);
                            crate::leanh::lean_dec(v_fvarId_5813_);
                            v_a_5883_ = crate::leanh::lean_ctor_get(v___x_5831_, 0);
                            v_isSharedCheck_5890_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5831_)) as u8;
                            if v_isSharedCheck_5890_ == 0 {
                                v___x_5885_ = v___x_5831_;
                                v_isShared_5886_ = v_isSharedCheck_5890_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5883_);
                                crate::leanh::lean_dec(v___x_5831_);
                                v___x_5885_ = crate::leanh::lean_box(0);
                                v_isShared_5886_ = v_isSharedCheck_5890_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_goal_5818_);
                        crate::leanh::lean_dec_ref(v___f_5817_);
                        crate::leanh::lean_dec_ref(v___f_5816_);
                        crate::leanh::lean_dec_ref(v___f_5815_);
                        crate::leanh::lean_dec_ref(v___f_5814_);
                        crate::leanh::lean_dec(v_fvarId_5813_);
                        v_a_5891_ = crate::leanh::lean_ctor_get(v___x_5829_, 0);
                        v_isSharedCheck_5898_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5829_)) as u8;
                        if v_isSharedCheck_5898_ == 0 {
                            v___x_5893_ = v___x_5829_;
                            v_isShared_5894_ = v_isSharedCheck_5898_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5891_);
                            crate::leanh::lean_dec(v___x_5829_);
                            v___x_5893_ = crate::leanh::lean_box(0);
                            v_isShared_5894_ = v_isSharedCheck_5898_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_5818_);
                    crate::leanh::lean_dec_ref(v___f_5817_);
                    crate::leanh::lean_dec_ref(v___f_5816_);
                    crate::leanh::lean_dec_ref(v___f_5815_);
                    crate::leanh::lean_dec_ref(v___f_5814_);
                    crate::leanh::lean_dec(v_fvarId_5813_);
                    v_a_5899_ = crate::leanh::lean_ctor_get(v___x_5824_, 0);
                    v_isSharedCheck_5906_ = (!crate::leanh::lean_is_exclusive(v___x_5824_)) as u8;
                    if v_isSharedCheck_5906_ == 0 {
                        v___x_5901_ = v___x_5824_;
                        v_isShared_5902_ = v_isSharedCheck_5906_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5899_);
                        crate::leanh::lean_dec(v___x_5824_);
                        v___x_5901_ = crate::leanh::lean_box(0);
                        v_isShared_5902_ = v_isSharedCheck_5906_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5846_) == 0 {
                    v___x_5850_ = crate::leanh::lean_box(0);
                    if v_isShared_5849_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5848_, 0, v___x_5850_);
                        v___x_5852_ = v___x_5848_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5853_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5853_, 0, v___x_5850_);
                        v___x_5852_ = v_reuseFailAlloc_5853_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5854_ = crate::leanh::lean_ctor_get(v_a_5846_, 0);
                    v_isSharedCheck_5865_ = (!crate::leanh::lean_is_exclusive(v_a_5846_)) as u8;
                    if v_isSharedCheck_5865_ == 0 {
                        v___x_5856_ = v_a_5846_;
                        v_isShared_5857_ = v_isSharedCheck_5865_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5854_);
                        crate::leanh::lean_dec(v_a_5846_);
                        v___x_5856_ = crate::leanh::lean_box(0);
                        v_isShared_5857_ = v_isSharedCheck_5865_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5852_;
            }
            3 => {
                v_snd_5858_ = crate::leanh::lean_ctor_get(v_val_5854_, 1);
                crate::leanh::lean_inc(v_snd_5858_);
                crate::leanh::lean_dec(v_val_5854_);
                if v_isShared_5857_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5856_, 0, v_snd_5858_);
                    v___x_5860_ = v___x_5856_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5864_, 0, v_snd_5858_);
                    v___x_5860_ = v_reuseFailAlloc_5864_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5849_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5848_, 0, v___x_5860_);
                    v___x_5862_ = v___x_5848_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5863_, 0, v___x_5860_);
                    v___x_5862_ = v_reuseFailAlloc_5863_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5862_;
            }
            6 => {
                if v_isShared_5870_ == 0 {
                    v___x_5872_ = v___x_5869_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5867_);
                    v___x_5872_ = v_reuseFailAlloc_5873_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5872_;
            }
            8 => {
                if v_isShared_5878_ == 0 {
                    v___x_5880_ = v___x_5877_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_a_5875_);
                    v___x_5880_ = v_reuseFailAlloc_5881_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5880_;
            }
            10 => {
                if v_isShared_5886_ == 0 {
                    v___x_5888_ = v___x_5885_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5889_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5889_, 0, v_a_5883_);
                    v___x_5888_ = v_reuseFailAlloc_5889_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5888_;
            }
            12 => {
                if v_isShared_5894_ == 0 {
                    v___x_5896_ = v___x_5893_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5897_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_a_5891_);
                    v___x_5896_ = v_reuseFailAlloc_5897_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5896_;
            }
            14 => {
                if v_isShared_5902_ == 0 {
                    v___x_5904_ = v___x_5901_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5905_, 0, v_a_5899_);
                    v___x_5904_ = v_reuseFailAlloc_5905_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5904_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_acNfHypMeta___lam__4___boxed(
    mut v_fvarId_5907_: *mut crate::leanh::LeanObject,
    mut v___f_5908_: *mut crate::leanh::LeanObject,
    mut v___f_5909_: *mut crate::leanh::LeanObject,
    mut v___f_5910_: *mut crate::leanh::LeanObject,
    mut v___f_5911_: *mut crate::leanh::LeanObject,
    mut v_goal_5912_: *mut crate::leanh::LeanObject,
    mut v___y_5913_: *mut crate::leanh::LeanObject,
    mut v___y_5914_: *mut crate::leanh::LeanObject,
    mut v___y_5915_: *mut crate::leanh::LeanObject,
    mut v___y_5916_: *mut crate::leanh::LeanObject,
    mut v___y_5917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5918_ = l_Lean_Meta_AC_acNfHypMeta___lam__4(
        v_fvarId_5907_,
        v___f_5908_,
        v___f_5909_,
        v___f_5910_,
        v___f_5911_,
        v_goal_5912_,
        v___y_5913_,
        v___y_5914_,
        v___y_5915_,
        v___y_5916_,
    );
    crate::leanh::lean_dec(v___y_5916_);
    crate::leanh::lean_dec_ref(v___y_5915_);
    crate::leanh::lean_dec(v___y_5914_);
    crate::leanh::lean_dec_ref(v___y_5913_);
    return v_res_5918_;
}
pub unsafe fn l_Lean_Meta_AC_acNfHypMeta(
    mut v_goal_5919_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5920_: *mut crate::leanh::LeanObject,
    mut v_a_5921_: *mut crate::leanh::LeanObject,
    mut v_a_5922_: *mut crate::leanh::LeanObject,
    mut v_a_5923_: *mut crate::leanh::LeanObject,
    mut v_a_5924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5926_ = l_Lean_Meta_AC_rewriteUnnormalized___closed__4;
    v___f_5927_ = l_Lean_Meta_AC_rewriteUnnormalized___closed__3;
    v___f_5928_ = l_Lean_Meta_AC_rewriteUnnormalized___closed__2;
    v___f_5929_ = l_Lean_Meta_AC_rewriteUnnormalized___closed__1;
    crate::leanh::lean_inc(v_goal_5919_);
    v___f_5930_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_AC_acNfHypMeta___lam__4___boxed as *mut core::ffi::c_void,
        11,
        6,
    );
    crate::leanh::lean_closure_set(v___f_5930_, 0, v_fvarId_5920_);
    crate::leanh::lean_closure_set(v___f_5930_, 1, v___f_5929_);
    crate::leanh::lean_closure_set(v___f_5930_, 2, v___f_5928_);
    crate::leanh::lean_closure_set(v___f_5930_, 3, v___f_5927_);
    crate::leanh::lean_closure_set(v___f_5930_, 4, v___f_5926_);
    crate::leanh::lean_closure_set(v___f_5930_, 5, v_goal_5919_);
    v___x_5931_ = l_Lean_MVarId_withContext___at___00Lean_Meta_AC_acNfHypMeta_spec__0___redArg(
        v_goal_5919_,
        v___f_5930_,
        v_a_5921_,
        v_a_5922_,
        v_a_5923_,
        v_a_5924_,
    );
    return v___x_5931_;
}
pub unsafe fn l_Lean_Meta_AC_acNfHypMeta___boxed(
    mut v_goal_5932_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5933_: *mut crate::leanh::LeanObject,
    mut v_a_5934_: *mut crate::leanh::LeanObject,
    mut v_a_5935_: *mut crate::leanh::LeanObject,
    mut v_a_5936_: *mut crate::leanh::LeanObject,
    mut v_a_5937_: *mut crate::leanh::LeanObject,
    mut v_a_5938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5939_ = l_Lean_Meta_AC_acNfHypMeta(
        v_goal_5932_,
        v_fvarId_5933_,
        v_a_5934_,
        v_a_5935_,
        v_a_5936_,
        v_a_5937_,
    );
    crate::leanh::lean_dec(v_a_5937_);
    crate::leanh::lean_dec_ref(v_a_5936_);
    crate::leanh::lean_dec(v_a_5935_);
    crate::leanh::lean_dec_ref(v_a_5934_);
    return v_res_5939_;
}
pub unsafe fn l_Lean_Meta_AC_acNfTargetTactic___lam__0(
    mut v___y_5940_: *mut crate::leanh::LeanObject,
    mut v___y_5941_: *mut crate::leanh::LeanObject,
    mut v___y_5942_: *mut crate::leanh::LeanObject,
    mut v___y_5943_: *mut crate::leanh::LeanObject,
    mut v___y_5944_: *mut crate::leanh::LeanObject,
    mut v___y_5945_: *mut crate::leanh::LeanObject,
    mut v___y_5946_: *mut crate::leanh::LeanObject,
    mut v___y_5947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5959_: u8 = 0;
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5963_: u8 = 0;
    let mut v_a_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5967_: u8 = 0;
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5949_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_5941_,
                    v___y_5944_,
                    v___y_5945_,
                    v___y_5946_,
                    v___y_5947_,
                );
                if crate::leanh::lean_obj_tag(v___x_5949_) == 0 {
                    v_a_5950_ = crate::leanh::lean_ctor_get(v___x_5949_, 0);
                    crate::leanh::lean_inc(v_a_5950_);
                    crate::leanh::lean_dec_ref_known(v___x_5949_, 1);
                    v___x_5951_ = l_Lean_Meta_AC_rewriteUnnormalized(
                        v_a_5950_,
                        v___y_5944_,
                        v___y_5945_,
                        v___y_5946_,
                        v___y_5947_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5951_) == 0 {
                        v_a_5952_ = crate::leanh::lean_ctor_get(v___x_5951_, 0);
                        crate::leanh::lean_inc(v_a_5952_);
                        crate::leanh::lean_dec_ref_known(v___x_5951_, 1);
                        v___x_5953_ = crate::leanh::lean_box(0);
                        v___x_5954_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5954_, 0, v_a_5952_);
                        crate::leanh::lean_ctor_set(v___x_5954_, 1, v___x_5953_);
                        v___x_5955_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                            v___x_5954_,
                            v___y_5941_,
                            v___y_5944_,
                            v___y_5945_,
                            v___y_5946_,
                            v___y_5947_,
                        );
                        return v___x_5955_;
                    } else {
                        v_a_5956_ = crate::leanh::lean_ctor_get(v___x_5951_, 0);
                        v_isSharedCheck_5963_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5951_)) as u8;
                        if v_isSharedCheck_5963_ == 0 {
                            v___x_5958_ = v___x_5951_;
                            v_isShared_5959_ = v_isSharedCheck_5963_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5956_);
                            crate::leanh::lean_dec(v___x_5951_);
                            v___x_5958_ = crate::leanh::lean_box(0);
                            v_isShared_5959_ = v_isSharedCheck_5963_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_5964_ = crate::leanh::lean_ctor_get(v___x_5949_, 0);
                    v_isSharedCheck_5971_ = (!crate::leanh::lean_is_exclusive(v___x_5949_)) as u8;
                    if v_isSharedCheck_5971_ == 0 {
                        v___x_5966_ = v___x_5949_;
                        v_isShared_5967_ = v_isSharedCheck_5971_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5964_);
                        crate::leanh::lean_dec(v___x_5949_);
                        v___x_5966_ = crate::leanh::lean_box(0);
                        v_isShared_5967_ = v_isSharedCheck_5971_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5959_ == 0 {
                    v___x_5961_ = v___x_5958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5962_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_a_5956_);
                    v___x_5961_ = v_reuseFailAlloc_5962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5961_;
            }
            3 => {
                if v_isShared_5967_ == 0 {
                    v___x_5969_ = v___x_5966_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5970_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_a_5964_);
                    v___x_5969_ = v_reuseFailAlloc_5970_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_acNfTargetTactic___lam__0___boxed(
    mut v___y_5972_: *mut crate::leanh::LeanObject,
    mut v___y_5973_: *mut crate::leanh::LeanObject,
    mut v___y_5974_: *mut crate::leanh::LeanObject,
    mut v___y_5975_: *mut crate::leanh::LeanObject,
    mut v___y_5976_: *mut crate::leanh::LeanObject,
    mut v___y_5977_: *mut crate::leanh::LeanObject,
    mut v___y_5978_: *mut crate::leanh::LeanObject,
    mut v___y_5979_: *mut crate::leanh::LeanObject,
    mut v___y_5980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5981_ = l_Lean_Meta_AC_acNfTargetTactic___lam__0(
        v___y_5972_,
        v___y_5973_,
        v___y_5974_,
        v___y_5975_,
        v___y_5976_,
        v___y_5977_,
        v___y_5978_,
        v___y_5979_,
    );
    crate::leanh::lean_dec(v___y_5979_);
    crate::leanh::lean_dec_ref(v___y_5978_);
    crate::leanh::lean_dec(v___y_5977_);
    crate::leanh::lean_dec_ref(v___y_5976_);
    crate::leanh::lean_dec(v___y_5975_);
    crate::leanh::lean_dec_ref(v___y_5974_);
    crate::leanh::lean_dec(v___y_5973_);
    crate::leanh::lean_dec_ref(v___y_5972_);
    return v_res_5981_;
}
pub unsafe fn l_Lean_Meta_AC_acNfTargetTactic(
    mut v_a_5983_: *mut crate::leanh::LeanObject,
    mut v_a_5984_: *mut crate::leanh::LeanObject,
    mut v_a_5985_: *mut crate::leanh::LeanObject,
    mut v_a_5986_: *mut crate::leanh::LeanObject,
    mut v_a_5987_: *mut crate::leanh::LeanObject,
    mut v_a_5988_: *mut crate::leanh::LeanObject,
    mut v_a_5989_: *mut crate::leanh::LeanObject,
    mut v_a_5990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5992_ = l_Lean_Meta_AC_acNfTargetTactic___closed__0;
    v___x_5993_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_5992_,
        v_a_5983_,
        v_a_5984_,
        v_a_5985_,
        v_a_5986_,
        v_a_5987_,
        v_a_5988_,
        v_a_5989_,
        v_a_5990_,
    );
    return v___x_5993_;
}
pub unsafe fn l_Lean_Meta_AC_acNfTargetTactic___boxed(
    mut v_a_5994_: *mut crate::leanh::LeanObject,
    mut v_a_5995_: *mut crate::leanh::LeanObject,
    mut v_a_5996_: *mut crate::leanh::LeanObject,
    mut v_a_5997_: *mut crate::leanh::LeanObject,
    mut v_a_5998_: *mut crate::leanh::LeanObject,
    mut v_a_5999_: *mut crate::leanh::LeanObject,
    mut v_a_6000_: *mut crate::leanh::LeanObject,
    mut v_a_6001_: *mut crate::leanh::LeanObject,
    mut v_a_6002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6003_ = l_Lean_Meta_AC_acNfTargetTactic(
        v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_, v_a_6000_, v_a_6001_,
    );
    crate::leanh::lean_dec(v_a_6001_);
    crate::leanh::lean_dec_ref(v_a_6000_);
    crate::leanh::lean_dec(v_a_5999_);
    crate::leanh::lean_dec_ref(v_a_5998_);
    crate::leanh::lean_dec(v_a_5997_);
    crate::leanh::lean_dec_ref(v_a_5996_);
    crate::leanh::lean_dec(v_a_5995_);
    crate::leanh::lean_dec_ref(v_a_5994_);
    return v_res_6003_;
}
pub unsafe fn l_Lean_Meta_AC_acNfHypTactic___lam__0(
    mut v_fvarId_6004_: *mut crate::leanh::LeanObject,
    mut v___y_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
    mut v___y_6009_: *mut crate::leanh::LeanObject,
    mut v___y_6010_: *mut crate::leanh::LeanObject,
    mut v___y_6011_: *mut crate::leanh::LeanObject,
    mut v___y_6012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6027_: u8 = 0;
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6031_: u8 = 0;
    let mut v_a_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6035_: u8 = 0;
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6014_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_6006_,
                    v___y_6009_,
                    v___y_6010_,
                    v___y_6011_,
                    v___y_6012_,
                );
                if crate::leanh::lean_obj_tag(v___x_6014_) == 0 {
                    v_a_6015_ = crate::leanh::lean_ctor_get(v___x_6014_, 0);
                    crate::leanh::lean_inc(v_a_6015_);
                    crate::leanh::lean_dec_ref_known(v___x_6014_, 1);
                    v___x_6016_ = l_Lean_Meta_AC_acNfHypMeta(
                        v_a_6015_,
                        v_fvarId_6004_,
                        v___y_6009_,
                        v___y_6010_,
                        v___y_6011_,
                        v___y_6012_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6016_) == 0 {
                        v_a_6017_ = crate::leanh::lean_ctor_get(v___x_6016_, 0);
                        crate::leanh::lean_inc(v_a_6017_);
                        crate::leanh::lean_dec_ref_known(v___x_6016_, 1);
                        if crate::leanh::lean_obj_tag(v_a_6017_) == 1 {
                            v_val_6018_ = crate::leanh::lean_ctor_get(v_a_6017_, 0);
                            crate::leanh::lean_inc(v_val_6018_);
                            crate::leanh::lean_dec_ref_known(v_a_6017_, 1);
                            v___x_6019_ = crate::leanh::lean_box(0);
                            v___x_6020_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6020_, 0, v_val_6018_);
                            crate::leanh::lean_ctor_set(v___x_6020_, 1, v___x_6019_);
                            v___x_6021_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v___x_6020_,
                                v___y_6006_,
                                v___y_6009_,
                                v___y_6010_,
                                v___y_6011_,
                                v___y_6012_,
                            );
                            return v___x_6021_;
                        } else {
                            crate::leanh::lean_dec(v_a_6017_);
                            v___x_6022_ = crate::leanh::lean_box(0);
                            v___x_6023_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v___x_6022_,
                                v___y_6006_,
                                v___y_6009_,
                                v___y_6010_,
                                v___y_6011_,
                                v___y_6012_,
                            );
                            return v___x_6023_;
                        }
                    } else {
                        v_a_6024_ = crate::leanh::lean_ctor_get(v___x_6016_, 0);
                        v_isSharedCheck_6031_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6016_)) as u8;
                        if v_isSharedCheck_6031_ == 0 {
                            v___x_6026_ = v___x_6016_;
                            v_isShared_6027_ = v_isSharedCheck_6031_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6024_);
                            crate::leanh::lean_dec(v___x_6016_);
                            v___x_6026_ = crate::leanh::lean_box(0);
                            v_isShared_6027_ = v_isSharedCheck_6031_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_6004_);
                    v_a_6032_ = crate::leanh::lean_ctor_get(v___x_6014_, 0);
                    v_isSharedCheck_6039_ = (!crate::leanh::lean_is_exclusive(v___x_6014_)) as u8;
                    if v_isSharedCheck_6039_ == 0 {
                        v___x_6034_ = v___x_6014_;
                        v_isShared_6035_ = v_isSharedCheck_6039_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6032_);
                        crate::leanh::lean_dec(v___x_6014_);
                        v___x_6034_ = crate::leanh::lean_box(0);
                        v_isShared_6035_ = v_isSharedCheck_6039_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6027_ == 0 {
                    v___x_6029_ = v___x_6026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6024_);
                    v___x_6029_ = v_reuseFailAlloc_6030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6029_;
            }
            3 => {
                if v_isShared_6035_ == 0 {
                    v___x_6037_ = v___x_6034_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_a_6032_);
                    v___x_6037_ = v_reuseFailAlloc_6038_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_acNfHypTactic___lam__0___boxed(
    mut v_fvarId_6040_: *mut crate::leanh::LeanObject,
    mut v___y_6041_: *mut crate::leanh::LeanObject,
    mut v___y_6042_: *mut crate::leanh::LeanObject,
    mut v___y_6043_: *mut crate::leanh::LeanObject,
    mut v___y_6044_: *mut crate::leanh::LeanObject,
    mut v___y_6045_: *mut crate::leanh::LeanObject,
    mut v___y_6046_: *mut crate::leanh::LeanObject,
    mut v___y_6047_: *mut crate::leanh::LeanObject,
    mut v___y_6048_: *mut crate::leanh::LeanObject,
    mut v___y_6049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6050_ = l_Lean_Meta_AC_acNfHypTactic___lam__0(
        v_fvarId_6040_,
        v___y_6041_,
        v___y_6042_,
        v___y_6043_,
        v___y_6044_,
        v___y_6045_,
        v___y_6046_,
        v___y_6047_,
        v___y_6048_,
    );
    crate::leanh::lean_dec(v___y_6048_);
    crate::leanh::lean_dec_ref(v___y_6047_);
    crate::leanh::lean_dec(v___y_6046_);
    crate::leanh::lean_dec_ref(v___y_6045_);
    crate::leanh::lean_dec(v___y_6044_);
    crate::leanh::lean_dec_ref(v___y_6043_);
    crate::leanh::lean_dec(v___y_6042_);
    crate::leanh::lean_dec_ref(v___y_6041_);
    return v_res_6050_;
}
pub unsafe fn l_Lean_Meta_AC_acNfHypTactic(
    mut v_fvarId_6051_: *mut crate::leanh::LeanObject,
    mut v_a_6052_: *mut crate::leanh::LeanObject,
    mut v_a_6053_: *mut crate::leanh::LeanObject,
    mut v_a_6054_: *mut crate::leanh::LeanObject,
    mut v_a_6055_: *mut crate::leanh::LeanObject,
    mut v_a_6056_: *mut crate::leanh::LeanObject,
    mut v_a_6057_: *mut crate::leanh::LeanObject,
    mut v_a_6058_: *mut crate::leanh::LeanObject,
    mut v_a_6059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6061_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_AC_acNfHypTactic___lam__0___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6061_, 0, v_fvarId_6051_);
    v___x_6062_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_6061_,
        v_a_6052_,
        v_a_6053_,
        v_a_6054_,
        v_a_6055_,
        v_a_6056_,
        v_a_6057_,
        v_a_6058_,
        v_a_6059_,
    );
    return v___x_6062_;
}
pub unsafe fn l_Lean_Meta_AC_acNfHypTactic___boxed(
    mut v_fvarId_6063_: *mut crate::leanh::LeanObject,
    mut v_a_6064_: *mut crate::leanh::LeanObject,
    mut v_a_6065_: *mut crate::leanh::LeanObject,
    mut v_a_6066_: *mut crate::leanh::LeanObject,
    mut v_a_6067_: *mut crate::leanh::LeanObject,
    mut v_a_6068_: *mut crate::leanh::LeanObject,
    mut v_a_6069_: *mut crate::leanh::LeanObject,
    mut v_a_6070_: *mut crate::leanh::LeanObject,
    mut v_a_6071_: *mut crate::leanh::LeanObject,
    mut v_a_6072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6073_ = l_Lean_Meta_AC_acNfHypTactic(
        v_fvarId_6063_,
        v_a_6064_,
        v_a_6065_,
        v_a_6066_,
        v_a_6067_,
        v_a_6068_,
        v_a_6069_,
        v_a_6070_,
        v_a_6071_,
    );
    crate::leanh::lean_dec(v_a_6071_);
    crate::leanh::lean_dec_ref(v_a_6070_);
    crate::leanh::lean_dec(v_a_6069_);
    crate::leanh::lean_dec_ref(v_a_6068_);
    crate::leanh::lean_dec(v_a_6067_);
    crate::leanh::lean_dec_ref(v_a_6066_);
    crate::leanh::lean_dec(v_a_6065_);
    crate::leanh::lean_dec_ref(v_a_6064_);
    return v_res_6073_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6074_ = crate::leanh::lean_box(0);
    v___x_6075_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_6076_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6076_, 0, v___x_6075_);
    crate::leanh::lean_ctor_set(v___x_6076_, 1, v___x_6074_);
    return v___x_6076_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6078_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___closed__0);
    v___x_6079_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6079_, 0, v___x_6078_);
    return v___x_6079_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg___boxed(
    mut v___y_6080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6081_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
    return v_res_6081_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0(
    mut v_00_u03b1_6082_: *mut crate::leanh::LeanObject,
    mut v___y_6083_: *mut crate::leanh::LeanObject,
    mut v___y_6084_: *mut crate::leanh::LeanObject,
    mut v___y_6085_: *mut crate::leanh::LeanObject,
    mut v___y_6086_: *mut crate::leanh::LeanObject,
    mut v___y_6087_: *mut crate::leanh::LeanObject,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
    mut v___y_6089_: *mut crate::leanh::LeanObject,
    mut v___y_6090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6092_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
    return v___x_6092_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___boxed(
    mut v_00_u03b1_6093_: *mut crate::leanh::LeanObject,
    mut v___y_6094_: *mut crate::leanh::LeanObject,
    mut v___y_6095_: *mut crate::leanh::LeanObject,
    mut v___y_6096_: *mut crate::leanh::LeanObject,
    mut v___y_6097_: *mut crate::leanh::LeanObject,
    mut v___y_6098_: *mut crate::leanh::LeanObject,
    mut v___y_6099_: *mut crate::leanh::LeanObject,
    mut v___y_6100_: *mut crate::leanh::LeanObject,
    mut v___y_6101_: *mut crate::leanh::LeanObject,
    mut v___y_6102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0(
        v_00_u03b1_6093_,
        v___y_6094_,
        v___y_6095_,
        v___y_6096_,
        v___y_6097_,
        v___y_6098_,
        v___y_6099_,
        v___y_6100_,
        v___y_6101_,
    );
    crate::leanh::lean_dec(v___y_6101_);
    crate::leanh::lean_dec_ref(v___y_6100_);
    crate::leanh::lean_dec(v___y_6099_);
    crate::leanh::lean_dec_ref(v___y_6098_);
    crate::leanh::lean_dec(v___y_6097_);
    crate::leanh::lean_dec_ref(v___y_6096_);
    crate::leanh::lean_dec(v___y_6095_);
    crate::leanh::lean_dec_ref(v___y_6094_);
    return v_res_6103_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(
    mut v_as_6104_: *mut crate::leanh::LeanObject,
    mut v_i_6105_: usize,
    mut v_stop_6106_: usize,
    mut v_b_6107_: *mut crate::leanh::LeanObject,
    mut v___y_6108_: *mut crate::leanh::LeanObject,
    mut v___y_6109_: *mut crate::leanh::LeanObject,
    mut v___y_6110_: *mut crate::leanh::LeanObject,
    mut v___y_6111_: *mut crate::leanh::LeanObject,
    mut v___y_6112_: *mut crate::leanh::LeanObject,
    mut v___y_6113_: *mut crate::leanh::LeanObject,
    mut v___y_6114_: *mut crate::leanh::LeanObject,
    mut v___y_6115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6117_: u8 = 0;
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: usize = 0;
    let mut v___x_6122_: usize = 0;
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6117_ = lean_usize_dec_eq(v_i_6105_, v_stop_6106_);
                if v___x_6117_ == 0 {
                    v___x_6118_ = lean_array_uget_borrowed(v_as_6104_, v_i_6105_);
                    crate::leanh::lean_inc(v___x_6118_);
                    v___x_6119_ = l_Lean_Meta_AC_acNfHypTactic(
                        v___x_6118_,
                        v___y_6108_,
                        v___y_6109_,
                        v___y_6110_,
                        v___y_6111_,
                        v___y_6112_,
                        v___y_6113_,
                        v___y_6114_,
                        v___y_6115_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6119_) == 0 {
                        v_a_6120_ = crate::leanh::lean_ctor_get(v___x_6119_, 0);
                        crate::leanh::lean_inc(v_a_6120_);
                        crate::leanh::lean_dec_ref_known(v___x_6119_, 1);
                        v___x_6121_ = 1usize;
                        v___x_6122_ = lean_usize_add(v_i_6105_, v___x_6121_);
                        v_i_6105_ = v___x_6122_;
                        v_b_6107_ = v_a_6120_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6119_;
                    }
                } else {
                    v___x_6124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6124_, 0, v_b_6107_);
                    return v___x_6124_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1___boxed(
    mut v_as_6125_: *mut crate::leanh::LeanObject,
    mut v_i_6126_: *mut crate::leanh::LeanObject,
    mut v_stop_6127_: *mut crate::leanh::LeanObject,
    mut v_b_6128_: *mut crate::leanh::LeanObject,
    mut v___y_6129_: *mut crate::leanh::LeanObject,
    mut v___y_6130_: *mut crate::leanh::LeanObject,
    mut v___y_6131_: *mut crate::leanh::LeanObject,
    mut v___y_6132_: *mut crate::leanh::LeanObject,
    mut v___y_6133_: *mut crate::leanh::LeanObject,
    mut v___y_6134_: *mut crate::leanh::LeanObject,
    mut v___y_6135_: *mut crate::leanh::LeanObject,
    mut v___y_6136_: *mut crate::leanh::LeanObject,
    mut v___y_6137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6138_: usize = 0;
    let mut v_stop_boxed_6139_: usize = 0;
    let mut v_res_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6138_ = crate::leanh::lean_unbox_usize(v_i_6126_);
    crate::leanh::lean_dec(v_i_6126_);
    v_stop_boxed_6139_ = crate::leanh::lean_unbox_usize(v_stop_6127_);
    crate::leanh::lean_dec(v_stop_6127_);
    v_res_6140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_as_6125_, v_i_boxed_6138_, v_stop_boxed_6139_, v_b_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_, v___y_6136_);
    crate::leanh::lean_dec(v___y_6136_);
    crate::leanh::lean_dec_ref(v___y_6135_);
    crate::leanh::lean_dec(v___y_6134_);
    crate::leanh::lean_dec_ref(v___y_6133_);
    crate::leanh::lean_dec(v___y_6132_);
    crate::leanh::lean_dec_ref(v___y_6131_);
    crate::leanh::lean_dec(v___y_6130_);
    crate::leanh::lean_dec_ref(v___y_6129_);
    crate::leanh::lean_dec_ref(v_as_6125_);
    return v_res_6140_;
}
pub unsafe fn l_Lean_Meta_AC_evalNf0___lam__0(
    mut v___y_6141_: *mut crate::leanh::LeanObject,
    mut v___x_6142_: *mut crate::leanh::LeanObject,
    mut v___y_6143_: *mut crate::leanh::LeanObject,
    mut v___y_6144_: *mut crate::leanh::LeanObject,
    mut v___y_6145_: *mut crate::leanh::LeanObject,
    mut v___y_6146_: *mut crate::leanh::LeanObject,
    mut v___y_6147_: *mut crate::leanh::LeanObject,
    mut v___y_6148_: *mut crate::leanh::LeanObject,
    mut v___y_6149_: *mut crate::leanh::LeanObject,
    mut v___y_6150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6159_: u8 = 0;
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: u8 = 0;
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: u8 = 0;
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: usize = 0;
    let mut v___x_6171_: usize = 0;
    let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: usize = 0;
    let mut v___x_6174_: usize = 0;
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6176_: u8 = 0;
    let mut v_a_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6180_: u8 = 0;
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6184_: u8 = 0;
    let mut v_a_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6188_: u8 = 0;
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6192_: u8 = 0;
    let mut v_hypotheses_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6194_: u8 = 0;
    let mut v___y_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6208_: u8 = 0;
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: u8 = 0;
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: u8 = 0;
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: usize = 0;
    let mut v___x_6220_: usize = 0;
    let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: usize = 0;
    let mut v___x_6223_: usize = 0;
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6225_: u8 = 0;
    let mut v_a_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6229_: u8 = 0;
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6233_: u8 = 0;
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___y_6141_) == 0 {
                    v___x_6152_ = l_Lean_Meta_AC_acNfTargetTactic(
                        v___y_6143_,
                        v___y_6144_,
                        v___y_6145_,
                        v___y_6146_,
                        v___y_6147_,
                        v___y_6148_,
                        v___y_6149_,
                        v___y_6150_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6152_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6152_, 1);
                        v___x_6153_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                            v___y_6144_,
                            v___y_6147_,
                            v___y_6148_,
                            v___y_6149_,
                            v___y_6150_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6153_) == 0 {
                            v_a_6154_ = crate::leanh::lean_ctor_get(v___x_6153_, 0);
                            crate::leanh::lean_inc(v_a_6154_);
                            crate::leanh::lean_dec_ref_known(v___x_6153_, 1);
                            v___x_6155_ = l_Lean_MVarId_getNondepPropHyps(
                                v_a_6154_,
                                v___y_6147_,
                                v___y_6148_,
                                v___y_6149_,
                                v___y_6150_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6155_) == 0 {
                                v_a_6156_ = crate::leanh::lean_ctor_get(v___x_6155_, 0);
                                v_isSharedCheck_6176_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6155_)) as u8;
                                if v_isSharedCheck_6176_ == 0 {
                                    v___x_6158_ = v___x_6155_;
                                    v_isShared_6159_ = v_isSharedCheck_6176_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6156_);
                                    crate::leanh::lean_dec(v___x_6155_);
                                    v___x_6158_ = crate::leanh::lean_box(0);
                                    v_isShared_6159_ = v_isSharedCheck_6176_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_6177_ = crate::leanh::lean_ctor_get(v___x_6155_, 0);
                                v_isSharedCheck_6184_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6155_)) as u8;
                                if v_isSharedCheck_6184_ == 0 {
                                    v___x_6179_ = v___x_6155_;
                                    v_isShared_6180_ = v_isSharedCheck_6184_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6177_);
                                    crate::leanh::lean_dec(v___x_6155_);
                                    v___x_6179_ = crate::leanh::lean_box(0);
                                    v_isShared_6180_ = v_isSharedCheck_6184_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            v_a_6185_ = crate::leanh::lean_ctor_get(v___x_6153_, 0);
                            v_isSharedCheck_6192_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6153_)) as u8;
                            if v_isSharedCheck_6192_ == 0 {
                                v___x_6187_ = v___x_6153_;
                                v_isShared_6188_ = v_isSharedCheck_6192_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6185_);
                                crate::leanh::lean_dec(v___x_6153_);
                                v___x_6187_ = crate::leanh::lean_box(0);
                                v_isShared_6188_ = v_isSharedCheck_6192_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        return v___x_6152_;
                    }
                } else {
                    v_hypotheses_6193_ = crate::leanh::lean_ctor_get(v___y_6141_, 0);
                    crate::leanh::lean_inc_ref(v_hypotheses_6193_);
                    v_type_6194_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6141_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v___y_6141_, 1);
                    if v_type_6194_ == 0 {
                        v___y_6196_ = v___y_6143_;
                        v___y_6197_ = v___y_6144_;
                        v___y_6198_ = v___y_6145_;
                        v___y_6199_ = v___y_6146_;
                        v___y_6200_ = v___y_6147_;
                        v___y_6201_ = v___y_6148_;
                        v___y_6202_ = v___y_6149_;
                        v___y_6203_ = v___y_6150_;
                        state = 8;
                        continue;
                    } else {
                        v___x_6234_ = l_Lean_Meta_AC_acNfTargetTactic(
                            v___y_6143_,
                            v___y_6144_,
                            v___y_6145_,
                            v___y_6146_,
                            v___y_6147_,
                            v___y_6148_,
                            v___y_6149_,
                            v___y_6150_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6234_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6234_, 1);
                            v___y_6196_ = v___y_6143_;
                            v___y_6197_ = v___y_6144_;
                            v___y_6198_ = v___y_6145_;
                            v___y_6199_ = v___y_6146_;
                            v___y_6200_ = v___y_6147_;
                            v___y_6201_ = v___y_6148_;
                            v___y_6202_ = v___y_6149_;
                            v___y_6203_ = v___y_6150_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_hypotheses_6193_);
                            return v___x_6234_;
                        }
                    }
                }
            }
            1 => {
                v___x_6160_ = lean_array_get_size(v_a_6156_);
                v___x_6161_ = crate::leanh::lean_box(0);
                v___x_6162_ = lean_nat_dec_lt(v___x_6142_, v___x_6160_);
                if v___x_6162_ == 0 {
                    crate::leanh::lean_dec(v_a_6156_);
                    if v_isShared_6159_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6158_, 0, v___x_6161_);
                        v___x_6164_ = v___x_6158_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6165_, 0, v___x_6161_);
                        v___x_6164_ = v_reuseFailAlloc_6165_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6166_ = lean_nat_dec_le(v___x_6160_, v___x_6160_);
                    if v___x_6166_ == 0 {
                        if v___x_6162_ == 0 {
                            crate::leanh::lean_dec(v_a_6156_);
                            if v_isShared_6159_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6158_, 0, v___x_6161_);
                                v___x_6168_ = v___x_6158_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6169_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6161_);
                                v___x_6168_ = v_reuseFailAlloc_6169_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6158_);
                            v___x_6170_ = 0usize;
                            v___x_6171_ = lean_usize_of_nat(v___x_6160_);
                            v___x_6172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_6156_, v___x_6170_, v___x_6171_, v___x_6161_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_);
                            crate::leanh::lean_dec(v_a_6156_);
                            return v___x_6172_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6158_);
                        v___x_6173_ = 0usize;
                        v___x_6174_ = lean_usize_of_nat(v___x_6160_);
                        v___x_6175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_6156_, v___x_6173_, v___x_6174_, v___x_6161_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_);
                        crate::leanh::lean_dec(v_a_6156_);
                        return v___x_6175_;
                    }
                }
            }
            2 => {
                return v___x_6164_;
            }
            3 => {
                return v___x_6168_;
            }
            4 => {
                if v_isShared_6180_ == 0 {
                    v___x_6182_ = v___x_6179_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6183_, 0, v_a_6177_);
                    v___x_6182_ = v_reuseFailAlloc_6183_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6182_;
            }
            6 => {
                if v_isShared_6188_ == 0 {
                    v___x_6190_ = v___x_6187_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6191_, 0, v_a_6185_);
                    v___x_6190_ = v_reuseFailAlloc_6191_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6190_;
            }
            8 => {
                v___x_6204_ = l_Lean_Elab_Tactic_getFVarIds(
                    v_hypotheses_6193_,
                    v___y_6196_,
                    v___y_6197_,
                    v___y_6198_,
                    v___y_6199_,
                    v___y_6200_,
                    v___y_6201_,
                    v___y_6202_,
                    v___y_6203_,
                );
                if crate::leanh::lean_obj_tag(v___x_6204_) == 0 {
                    v_a_6205_ = crate::leanh::lean_ctor_get(v___x_6204_, 0);
                    v_isSharedCheck_6225_ = (!crate::leanh::lean_is_exclusive(v___x_6204_)) as u8;
                    if v_isSharedCheck_6225_ == 0 {
                        v___x_6207_ = v___x_6204_;
                        v_isShared_6208_ = v_isSharedCheck_6225_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6205_);
                        crate::leanh::lean_dec(v___x_6204_);
                        v___x_6207_ = crate::leanh::lean_box(0);
                        v_isShared_6208_ = v_isSharedCheck_6225_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_a_6226_ = crate::leanh::lean_ctor_get(v___x_6204_, 0);
                    v_isSharedCheck_6233_ = (!crate::leanh::lean_is_exclusive(v___x_6204_)) as u8;
                    if v_isSharedCheck_6233_ == 0 {
                        v___x_6228_ = v___x_6204_;
                        v_isShared_6229_ = v_isSharedCheck_6233_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6226_);
                        crate::leanh::lean_dec(v___x_6204_);
                        v___x_6228_ = crate::leanh::lean_box(0);
                        v_isShared_6229_ = v_isSharedCheck_6233_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                v___x_6209_ = lean_array_get_size(v_a_6205_);
                v___x_6210_ = crate::leanh::lean_box(0);
                v___x_6211_ = lean_nat_dec_lt(v___x_6142_, v___x_6209_);
                if v___x_6211_ == 0 {
                    crate::leanh::lean_dec(v_a_6205_);
                    if v_isShared_6208_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6207_, 0, v___x_6210_);
                        v___x_6213_ = v___x_6207_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6214_, 0, v___x_6210_);
                        v___x_6213_ = v_reuseFailAlloc_6214_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___x_6215_ = lean_nat_dec_le(v___x_6209_, v___x_6209_);
                    if v___x_6215_ == 0 {
                        if v___x_6211_ == 0 {
                            crate::leanh::lean_dec(v_a_6205_);
                            if v_isShared_6208_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6207_, 0, v___x_6210_);
                                v___x_6217_ = v___x_6207_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_6218_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6218_, 0, v___x_6210_);
                                v___x_6217_ = v_reuseFailAlloc_6218_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6207_);
                            v___x_6219_ = 0usize;
                            v___x_6220_ = lean_usize_of_nat(v___x_6209_);
                            v___x_6221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_6205_, v___x_6219_, v___x_6220_, v___x_6210_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_);
                            crate::leanh::lean_dec(v_a_6205_);
                            return v___x_6221_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6207_);
                        v___x_6222_ = 0usize;
                        v___x_6223_ = lean_usize_of_nat(v___x_6209_);
                        v___x_6224_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_AC_evalNf0_spec__1(v_a_6205_, v___x_6222_, v___x_6223_, v___x_6210_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_, v___y_6202_, v___y_6203_);
                        crate::leanh::lean_dec(v_a_6205_);
                        return v___x_6224_;
                    }
                }
            }
            10 => {
                return v___x_6213_;
            }
            11 => {
                return v___x_6217_;
            }
            12 => {
                if v_isShared_6229_ == 0 {
                    v___x_6231_ = v___x_6228_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6232_, 0, v_a_6226_);
                    v___x_6231_ = v_reuseFailAlloc_6232_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_evalNf0___lam__0___boxed(
    mut v___y_6235_: *mut crate::leanh::LeanObject,
    mut v___x_6236_: *mut crate::leanh::LeanObject,
    mut v___y_6237_: *mut crate::leanh::LeanObject,
    mut v___y_6238_: *mut crate::leanh::LeanObject,
    mut v___y_6239_: *mut crate::leanh::LeanObject,
    mut v___y_6240_: *mut crate::leanh::LeanObject,
    mut v___y_6241_: *mut crate::leanh::LeanObject,
    mut v___y_6242_: *mut crate::leanh::LeanObject,
    mut v___y_6243_: *mut crate::leanh::LeanObject,
    mut v___y_6244_: *mut crate::leanh::LeanObject,
    mut v___y_6245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6246_ = l_Lean_Meta_AC_evalNf0___lam__0(
        v___y_6235_,
        v___x_6236_,
        v___y_6237_,
        v___y_6238_,
        v___y_6239_,
        v___y_6240_,
        v___y_6241_,
        v___y_6242_,
        v___y_6243_,
        v___y_6244_,
    );
    crate::leanh::lean_dec(v___y_6244_);
    crate::leanh::lean_dec_ref(v___y_6243_);
    crate::leanh::lean_dec(v___y_6242_);
    crate::leanh::lean_dec_ref(v___y_6241_);
    crate::leanh::lean_dec(v___y_6240_);
    crate::leanh::lean_dec_ref(v___y_6239_);
    crate::leanh::lean_dec(v___y_6238_);
    crate::leanh::lean_dec_ref(v___y_6237_);
    crate::leanh::lean_dec(v___x_6236_);
    return v_res_6246_;
}
pub unsafe fn l_Lean_Meta_AC_evalNf0(
    mut v_stx_6255_: *mut crate::leanh::LeanObject,
    mut v_a_6256_: *mut crate::leanh::LeanObject,
    mut v_a_6257_: *mut crate::leanh::LeanObject,
    mut v_a_6258_: *mut crate::leanh::LeanObject,
    mut v_a_6259_: *mut crate::leanh::LeanObject,
    mut v_a_6260_: *mut crate::leanh::LeanObject,
    mut v_a_6261_: *mut crate::leanh::LeanObject,
    mut v_a_6262_: *mut crate::leanh::LeanObject,
    mut v_a_6263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: u8 = 0;
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: u8 = 0;
    let mut v___x_6284_: u8 = 0;
    let mut v___x_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_loc_x3f_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6265_ = l_Lean_Meta_AC_evalNf0___closed__1;
                crate::leanh::lean_inc(v_stx_6255_);
                v___x_6266_ = l_Lean_Syntax_isOfKind(v_stx_6255_, v___x_6265_);
                if v___x_6266_ == 0 {
                    crate::leanh::lean_dec(v_stx_6255_);
                    v___x_6267_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
                    return v___x_6267_;
                } else {
                    v___x_6268_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6281_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6282_ = l_Lean_Syntax_getArg(v_stx_6255_, v___x_6281_);
                    crate::leanh::lean_dec(v_stx_6255_);
                    v___x_6283_ = l_Lean_Syntax_isNone(v___x_6282_);
                    if v___x_6283_ == 0 {
                        crate::leanh::lean_inc(v___x_6282_);
                        v___x_6284_ = l_Lean_Syntax_matchesNull(v___x_6282_, v___x_6281_);
                        if v___x_6284_ == 0 {
                            crate::leanh::lean_dec(v___x_6282_);
                            v___x_6285_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Meta_AC_evalNf0_spec__0___redArg();
                            return v___x_6285_;
                        } else {
                            v_loc_x3f_6286_ = l_Lean_Syntax_getArg(v___x_6282_, v___x_6268_);
                            crate::leanh::lean_dec(v___x_6282_);
                            v___x_6287_ = l_Lean_Elab_Tactic_expandLocation(v_loc_x3f_6286_);
                            crate::leanh::lean_dec(v_loc_x3f_6286_);
                            v___y_6270_ = v_a_6256_;
                            v___y_6271_ = v_a_6263_;
                            v___y_6272_ = v_a_6259_;
                            v___y_6273_ = v_a_6258_;
                            v___y_6274_ = v_a_6260_;
                            v___y_6275_ = v_a_6262_;
                            v___y_6276_ = v_a_6257_;
                            v___y_6277_ = v_a_6261_;
                            v___y_6278_ = v___x_6287_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6282_);
                        v___x_6288_ = l_Lean_Meta_AC_evalNf0___closed__2;
                        v___x_6289_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_6289_, 0, v___x_6288_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6289_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_6266_,
                        );
                        v___y_6270_ = v_a_6256_;
                        v___y_6271_ = v_a_6263_;
                        v___y_6272_ = v_a_6259_;
                        v___y_6273_ = v_a_6258_;
                        v___y_6274_ = v_a_6260_;
                        v___y_6275_ = v_a_6262_;
                        v___y_6276_ = v_a_6257_;
                        v___y_6277_ = v_a_6261_;
                        v___y_6278_ = v___x_6289_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___y_6279_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_AC_evalNf0___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    2,
                );
                crate::leanh::lean_closure_set(v___y_6279_, 0, v___y_6278_);
                crate::leanh::lean_closure_set(v___y_6279_, 1, v___x_6268_);
                v___x_6280_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___y_6279_,
                    v___y_6270_,
                    v___y_6276_,
                    v___y_6273_,
                    v___y_6272_,
                    v___y_6274_,
                    v___y_6277_,
                    v___y_6275_,
                    v___y_6271_,
                );
                return v___x_6280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_AC_evalNf0___boxed(
    mut v_stx_6290_: *mut crate::leanh::LeanObject,
    mut v_a_6291_: *mut crate::leanh::LeanObject,
    mut v_a_6292_: *mut crate::leanh::LeanObject,
    mut v_a_6293_: *mut crate::leanh::LeanObject,
    mut v_a_6294_: *mut crate::leanh::LeanObject,
    mut v_a_6295_: *mut crate::leanh::LeanObject,
    mut v_a_6296_: *mut crate::leanh::LeanObject,
    mut v_a_6297_: *mut crate::leanh::LeanObject,
    mut v_a_6298_: *mut crate::leanh::LeanObject,
    mut v_a_6299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6300_ = l_Lean_Meta_AC_evalNf0(
        v_stx_6290_,
        v_a_6291_,
        v_a_6292_,
        v_a_6293_,
        v_a_6294_,
        v_a_6295_,
        v_a_6296_,
        v_a_6297_,
        v_a_6298_,
    );
    crate::leanh::lean_dec(v_a_6298_);
    crate::leanh::lean_dec_ref(v_a_6297_);
    crate::leanh::lean_dec(v_a_6296_);
    crate::leanh::lean_dec_ref(v_a_6295_);
    crate::leanh::lean_dec(v_a_6294_);
    crate::leanh::lean_dec_ref(v_a_6293_);
    crate::leanh::lean_dec(v_a_6292_);
    crate::leanh::lean_dec_ref(v_a_6291_);
    return v_res_6300_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6308_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_6309_ = l_Lean_Meta_AC_evalNf0___closed__1;
    v___x_6310_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___closed__1;
    v___x_6311_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_AC_evalNf0___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_6312_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6308_,
        v___x_6309_,
        v___x_6310_,
        v___x_6311_,
    );
    return v___x_6312_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1___boxed(
    mut v_a_6313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6314_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1();
    return v_res_6314_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6370_ = crate::leanh::lean_unsigned_to_nat(4236260923);
    v___x_6371_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__20_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_;
    v___x_6372_ = l_Lean_Name_num___override(v___x_6371_, v___x_6370_);
    return v___x_6372_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6374_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__22_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_;
    v___x_6375_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__21_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
    v___x_6376_ = l_Lean_Name_str___override(v___x_6375_, v___x_6374_);
    return v___x_6376_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6378_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__24_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_;
    v___x_6379_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__23_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
    v___x_6380_ = l_Lean_Name_str___override(v___x_6379_, v___x_6378_);
    return v___x_6380_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6381_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_6382_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__25_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
    v___x_6383_ = l_Lean_Name_num___override(v___x_6382_, v___x_6381_);
    return v___x_6383_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: u8 = 0;
    let mut v___x_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6385_ = l_Lean_Meta_AC_getInstance___closed__2;
    v___x_6386_ = 0;
    v___x_6387_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn___closed__26_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_);
    v___x_6388_ = l_Lean_registerTraceClass(v___x_6385_, v___x_6386_, v___x_6387_);
    return v___x_6388_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2____boxed(
    mut v_a_6389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6390_ = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_();
    return v_res_6390_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_AC_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_AC_instInhabitedPreContext_default =
        _init_l_Lean_Meta_AC_instInhabitedPreContext_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_AC_instInhabitedPreContext_default);
    l_Lean_Meta_AC_instInhabitedPreContext = _init_l_Lean_Meta_AC_instInhabitedPreContext();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_AC_instInhabitedPreContext);
    res = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_acRflTactic___regBuiltin_Lean_Meta_AC_acRflTactic_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_evalNf0___regBuiltin_Lean_Meta_AC_evalNf0__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_AC_Main_0__Lean_Meta_AC_initFn_00___x40_Lean_Meta_Tactic_AC_Main_4236260923____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_AC_Main(
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
pub unsafe fn initialize_Lean_Meta_Tactic_AC_Main(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_AC_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_AC_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_AC_Main(builtin);
}
