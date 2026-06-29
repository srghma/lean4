// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MatchCond
// Imports: Init.Grind Lean.Meta.Tactic.Contradiction Lean.Meta.Tactic.Grind.ProveEq Lean.Meta.Tactic.Grind.PropagatorAttr
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_set, lean_array_size, lean_array_uget_borrowed, lean_expr_eqv,
    lean_grind_mk_eq_proof, lean_grind_mk_heq_proof, lean_infer_type, lean_mk_array, lean_name_eq,
    lean_nat_add, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_ptr_addr,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_Expr_sort___override, l_Lean_instBEqBinderInfo_beq, l_Lean_instInhabitedExpr,
    l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkAppN, l_Lean_mkNot,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkDecideProof, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqOfHEq, l_Lean_Meta_mkEqTrans,
    l_Lean_Meta_mkEqTrueCore, l_Lean_Meta_mkHEqTrans, l_Lean_Meta_mkNoConfusion,
    l_Lean_Meta_mkOfEqTrueCore,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_Meta_forallMetaTelescope,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isDefEqD, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp_x3f;
use crate::r#gen::Lean::Meta::HasAssignableMVar::l_Lean_Meta_hasAssignableMVar;
use crate::r#gen::Lean::Meta::LitValues::{l_Lean_Meta_isLitValue, l_Lean_Meta_normLitValue};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
    l_Lean_Meta_Sym_shareCommon___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Contradiction::{
    initialize_Lean_Meta_Tactic_Contradiction, l_Lean_Meta_mkGenDiseqMask,
    runtime_initialize_Lean_Meta_Tactic_Contradiction,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::PropagatorAttr::{
    initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
    l_Lean_Meta_Grind_registerBuiltinDownwardPropagator,
    l_Lean_Meta_Grind_registerBuiltinUpwardPropagator,
    runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::ProveEq::{
    initialize_Lean_Meta_Tactic_Grind_ProveEq, l_Lean_Meta_Grind_proveEq_x3f,
    l_Lean_Meta_Grind_proveHEq_x3f, runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_closeGoal, l_Lean_Meta_Grind_getRootENode___redArg,
    l_Lean_Meta_Grind_getRootENode_x3f___redArg, l_Lean_Meta_Grind_hasSameType,
    l_Lean_Meta_Grind_isEqTrue___redArg, l_Lean_Meta_Grind_mkEqTrueProof,
    l_Lean_Meta_Grind_pushEqTrue___redArg, l_Lean_Meta_Grind_updateLastTag,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [72, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value) as *mut crate::leanh::LeanObject,13589827700912665667 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,13655884332201764339 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [116, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0_value) as *mut crate::leanh::LeanObject,6786334389890653769 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0_value:
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
static mut l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1_value:
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
static mut l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [77, 97, 116, 99, 104, 67, 111, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_1:
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
            l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value:
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
            l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3_value)
            as *mut crate::leanh::LeanObject,
        16774854854508800365 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 97, 116, 99, 104, 67, 111, 110, 100, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject,3290229967450319541 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 97, 116, 105, 102, 105, 115, 101, 100, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [10, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 101, 113, 117, 97, 108, 105, 116, 121, 32, 105, 115, 32, 102, 97, 108, 115, 101, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [102, 111, 117, 110, 100, 32, 116, 101, 114, 109, 32, 116, 104, 97, 116, 32, 104, 97, 115, 32, 110, 111, 116, 32, 98, 101, 101, 110, 32, 105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2_value: crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [10, 119, 104, 105, 108, 101, 32, 116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 32, 97, 32, 112, 114, 111, 111, 102, 32, 102, 111, 114, 32, 96, 77, 97, 116, 99, 104, 67, 111, 110, 100, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 111, 63, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [62, 62, 62, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [112, 114, 111, 118, 101, 70, 97, 108, 115, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15947788021050471391 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,5637236024813792860 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject,3290229967450319541 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,9871136077191002602 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [32, 61, 63, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0_value:
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
    m_data: [32, 58, 32, 0],
};
static mut l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_tryToProveFalse___closed__0_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed as *const core::ffi::c_void, m_arity: 13, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_tryToProveFalse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_tryToProveFalse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateMatchCondUp___closed__0_value:
    crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
        32, 112, 114, 111, 111, 102, 32, 102, 111, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_propagateMatchCondUp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateMatchCondUp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateMatchCondUp___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [118, 105, 115, 105, 116, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_propagateMatchCondUp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateMatchCondUp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(
    mut v_e_3560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: u8 = 0;
    v___x_3561_ = l_Lean_Expr_cleanupAnnotations(v_e_3560_);
    v___x_3562_ = l_Lean_Expr_isApp(v___x_3561_);
    if v___x_3562_ == 0 {
        let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_3561_);
        v___x_3563_ = crate::leanh::lean_box(0);
        return v___x_3563_;
    } else {
        let mut v_arg_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3566_: u8 = 0;
        v_arg_3564_ = crate::leanh::lean_ctor_get(v___x_3561_, 1);
        crate::leanh::lean_inc_ref(v_arg_3564_);
        v___x_3565_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3561_);
        v___x_3566_ = l_Lean_Expr_isApp(v___x_3565_);
        if v___x_3566_ == 0 {
            let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_3565_);
            crate::leanh::lean_dec_ref(v_arg_3564_);
            v___x_3567_ = crate::leanh::lean_box(0);
            return v___x_3567_;
        } else {
            let mut v_arg_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3570_: u8 = 0;
            v_arg_3568_ = crate::leanh::lean_ctor_get(v___x_3565_, 1);
            crate::leanh::lean_inc_ref(v_arg_3568_);
            v___x_3569_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3565_);
            v___x_3570_ = l_Lean_Expr_isApp(v___x_3569_);
            if v___x_3570_ == 0 {
                let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_3569_);
                crate::leanh::lean_dec_ref(v_arg_3568_);
                crate::leanh::lean_dec_ref(v_arg_3564_);
                v___x_3571_ = crate::leanh::lean_box(0);
                return v___x_3571_;
            } else {
                let mut v_arg_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3575_: u8 = 0;
                v_arg_3572_ = crate::leanh::lean_ctor_get(v___x_3569_, 1);
                crate::leanh::lean_inc_ref(v_arg_3572_);
                v___x_3573_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3569_);
                v___x_3574_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1;
                v___x_3575_ = l_Lean_Expr_isConstOf(v___x_3573_, v___x_3574_);
                if v___x_3575_ == 0 {
                    let mut v___x_3576_: u8 = 0;
                    crate::leanh::lean_dec_ref(v_arg_3568_);
                    v___x_3576_ = l_Lean_Expr_isApp(v___x_3573_);
                    if v___x_3576_ == 0 {
                        let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref(v___x_3573_);
                        crate::leanh::lean_dec_ref(v_arg_3572_);
                        crate::leanh::lean_dec_ref(v_arg_3564_);
                        v___x_3577_ = crate::leanh::lean_box(0);
                        return v___x_3577_;
                    } else {
                        let mut v_arg_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3581_: u8 = 0;
                        v_arg_3578_ = crate::leanh::lean_ctor_get(v___x_3573_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3578_);
                        v___x_3579_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3573_);
                        v___x_3580_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3;
                        v___x_3581_ = l_Lean_Expr_isConstOf(v___x_3579_, v___x_3580_);
                        crate::leanh::lean_dec_ref(v___x_3579_);
                        if v___x_3581_ == 0 {
                            let mut v___x_3582_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref(v_arg_3578_);
                            crate::leanh::lean_dec_ref(v_arg_3572_);
                            crate::leanh::lean_dec_ref(v_arg_3564_);
                            v___x_3582_ = crate::leanh::lean_box(0);
                            return v___x_3582_;
                        } else {
                            let mut v___x_3583_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3584_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3585_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3586_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_3583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3583_, 0, v_arg_3578_);
                            v___x_3584_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3584_, 0, v_arg_3572_);
                            crate::leanh::lean_ctor_set(v___x_3584_, 1, v_arg_3564_);
                            v___x_3585_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3585_, 0, v___x_3583_);
                            crate::leanh::lean_ctor_set(v___x_3585_, 1, v___x_3584_);
                            v___x_3586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3586_, 0, v___x_3585_);
                            return v___x_3586_;
                        }
                    }
                } else {
                    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v___x_3573_);
                    crate::leanh::lean_dec_ref(v_arg_3572_);
                    v___x_3587_ = crate::leanh::lean_box(0);
                    v___x_3588_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3588_, 0, v_arg_3568_);
                    crate::leanh::lean_ctor_set(v___x_3588_, 1, v_arg_3564_);
                    v___x_3589_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3589_, 0, v___x_3587_);
                    crate::leanh::lean_ctor_set(v___x_3589_, 1, v___x_3588_);
                    v___x_3590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3590_, 0, v___x_3589_);
                    return v___x_3590_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(
    mut v_body_3591_: *mut crate::leanh::LeanObject,
    mut v___x_3592_: *mut crate::leanh::LeanObject,
    mut v_____r_3593_: *mut crate::leanh::LeanObject,
    mut v_r_3594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3595_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3595_, 0, v_r_3594_);
    crate::leanh::lean_ctor_set(v___x_3595_, 1, v_body_3591_);
    v___x_3596_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3596_, 0, v___x_3592_);
    crate::leanh::lean_ctor_set(v___x_3596_, 1, v___x_3595_);
    v___x_3597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3597_, 0, v___x_3596_);
    return v___x_3597_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg(
    mut v_a_3598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3607_: u8 = 0;
    let mut v_snd_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3621_: u8 = 0;
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3630_: u8 = 0;
    let mut v_unused_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut v_unused_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut v_unused_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3604_ = crate::leanh::lean_ctor_get(v_a_3598_, 1);
                v_isSharedCheck_3647_ = (!crate::leanh::lean_is_exclusive(v_a_3598_)) as u8;
                if v_isSharedCheck_3647_ == 0 {
                    v_unused_3648_ = crate::leanh::lean_ctor_get(v_a_3598_, 0);
                    crate::leanh::lean_dec(v_unused_3648_);
                    v___x_3606_ = v_a_3598_;
                    v_isShared_3607_ = v_isSharedCheck_3647_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3604_);
                    crate::leanh::lean_dec(v_a_3598_);
                    v___x_3606_ = crate::leanh::lean_box(0);
                    v_isShared_3607_ = v_isSharedCheck_3647_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3600_) == 0 {
                    v_a_3601_ = crate::leanh::lean_ctor_get(v___y_3600_, 0);
                    crate::leanh::lean_inc(v_a_3601_);
                    crate::leanh::lean_dec_ref_known(v___y_3600_, 1);
                    return v_a_3601_;
                } else {
                    v_a_3602_ = crate::leanh::lean_ctor_get(v___y_3600_, 0);
                    crate::leanh::lean_inc(v_a_3602_);
                    crate::leanh::lean_dec_ref_known(v___y_3600_, 1);
                    v_a_3598_ = v_a_3602_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_snd_3608_ = crate::leanh::lean_ctor_get(v_snd_3604_, 1);
                crate::leanh::lean_inc(v_snd_3608_);
                if crate::leanh::lean_obj_tag(v_snd_3608_) == 7 {
                    crate::leanh::lean_del_object(v___x_3606_);
                    v_fst_3609_ = crate::leanh::lean_ctor_get(v_snd_3604_, 0);
                    crate::leanh::lean_inc(v_fst_3609_);
                    crate::leanh::lean_dec(v_snd_3604_);
                    v_binderType_3610_ = crate::leanh::lean_ctor_get(v_snd_3608_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_3610_);
                    v_body_3611_ = crate::leanh::lean_ctor_get(v_snd_3608_, 2);
                    crate::leanh::lean_inc_ref(v_body_3611_);
                    crate::leanh::lean_dec_ref_known(v_snd_3608_, 3);
                    v___x_3612_ = crate::leanh::lean_box(0);
                    v___x_3613_ =
                        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(
                            v_binderType_3610_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3613_) == 1 {
                        v_val_3614_ = crate::leanh::lean_ctor_get(v___x_3613_, 0);
                        crate::leanh::lean_inc(v_val_3614_);
                        crate::leanh::lean_dec_ref_known(v___x_3613_, 1);
                        v_snd_3615_ = crate::leanh::lean_ctor_get(v_val_3614_, 1);
                        crate::leanh::lean_inc(v_snd_3615_);
                        v_fst_3616_ = crate::leanh::lean_ctor_get(v_val_3614_, 0);
                        crate::leanh::lean_inc(v_fst_3616_);
                        crate::leanh::lean_dec(v_val_3614_);
                        v_fst_3617_ = crate::leanh::lean_ctor_get(v_snd_3615_, 0);
                        v_isSharedCheck_3630_ =
                            (!crate::leanh::lean_is_exclusive(v_snd_3615_)) as u8;
                        if v_isSharedCheck_3630_ == 0 {
                            v_unused_3631_ = crate::leanh::lean_ctor_get(v_snd_3615_, 1);
                            crate::leanh::lean_dec(v_unused_3631_);
                            v___x_3619_ = v_snd_3615_;
                            v_isShared_3620_ = v_isSharedCheck_3630_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_3617_);
                            crate::leanh::lean_dec(v_snd_3615_);
                            v___x_3619_ = crate::leanh::lean_box(0);
                            v_isShared_3620_ = v_isSharedCheck_3630_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3613_);
                        v___x_3632_ = crate::leanh::lean_box(0);
                        v___x_3633_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(v_body_3611_, v___x_3612_, v___x_3632_, v_fst_3609_);
                        v___y_3600_ = v___x_3633_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fst_3634_ = crate::leanh::lean_ctor_get(v_snd_3604_, 0);
                    v_isSharedCheck_3645_ = (!crate::leanh::lean_is_exclusive(v_snd_3604_)) as u8;
                    if v_isSharedCheck_3645_ == 0 {
                        v_unused_3646_ = crate::leanh::lean_ctor_get(v_snd_3604_, 1);
                        crate::leanh::lean_dec(v_unused_3646_);
                        v___x_3636_ = v_snd_3604_;
                        v_isShared_3637_ = v_isSharedCheck_3645_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3634_);
                        crate::leanh::lean_dec(v_snd_3604_);
                        v___x_3636_ = crate::leanh::lean_box(0);
                        v_isShared_3637_ = v_isSharedCheck_3645_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3621_ = l_Lean_Expr_hasLooseBVars(v_fst_3617_);
                if v___x_3621_ == 0 {
                    if v_isShared_3620_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3619_, 1, v_fst_3616_);
                        v___x_3623_ = v___x_3619_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3627_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_fst_3617_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 1, v_fst_3616_);
                        v___x_3623_ = v_reuseFailAlloc_3627_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3619_);
                    crate::leanh::lean_dec(v_fst_3617_);
                    crate::leanh::lean_dec(v_fst_3616_);
                    v___x_3628_ = crate::leanh::lean_box(0);
                    v___x_3629_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(v_body_3611_, v___x_3612_, v___x_3628_, v_fst_3609_);
                    v___y_3600_ = v___x_3629_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_3624_ = lean_array_push(v_fst_3609_, v___x_3623_);
                v___x_3625_ = crate::leanh::lean_box(0);
                v___x_3626_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg___lam__0(v_body_3611_, v___x_3612_, v___x_3625_, v___x_3624_);
                v___y_3600_ = v___x_3626_;
                state = 1;
                continue;
            }
            5 => {
                crate::leanh::lean_inc(v_fst_3634_);
                v___x_3638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3638_, 0, v_fst_3634_);
                if v_isShared_3637_ == 0 {
                    v___x_3640_ = v___x_3636_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_fst_3634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_snd_3608_);
                    v___x_3640_ = v_reuseFailAlloc_3644_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3606_, 1, v___x_3640_);
                    crate::leanh::lean_ctor_set(v___x_3606_, 0, v___x_3638_);
                    v___x_3642_ = v___x_3606_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3643_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3643_, 1, v___x_3640_);
                    v___x_3642_ = v_reuseFailAlloc_3643_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(
    mut v_e_3651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_3652_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0;
    v___x_3653_ = crate::leanh::lean_box(0);
    v___x_3654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3654_, 0, v_r_3652_);
    crate::leanh::lean_ctor_set(v___x_3654_, 1, v_e_3651_);
    v___x_3655_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3655_, 0, v___x_3653_);
    crate::leanh::lean_ctor_set(v___x_3655_, 1, v___x_3654_);
    v___x_3656_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg(v___x_3655_);
    v_fst_3657_ = crate::leanh::lean_ctor_get(v___x_3656_, 0);
    crate::leanh::lean_inc(v_fst_3657_);
    if crate::leanh::lean_obj_tag(v_fst_3657_) == 0 {
        let mut v_snd_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_snd_3658_ = crate::leanh::lean_ctor_get(v___x_3656_, 1);
        crate::leanh::lean_inc(v_snd_3658_);
        crate::leanh::lean_dec_ref(v___x_3656_);
        v_fst_3659_ = crate::leanh::lean_ctor_get(v_snd_3658_, 0);
        crate::leanh::lean_inc(v_fst_3659_);
        crate::leanh::lean_dec(v_snd_3658_);
        return v_fst_3659_;
    } else {
        let mut v_val_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_3656_);
        v_val_3660_ = crate::leanh::lean_ctor_get(v_fst_3657_, 0);
        crate::leanh::lean_inc(v_val_3660_);
        crate::leanh::lean_dec_ref_known(v_fst_3657_, 1);
        return v_val_3660_;
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(
    mut v_inst_3661_: *mut crate::leanh::LeanObject,
    mut v_a_3662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3663_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0___redArg(v_a_3662_);
    return v___x_3663_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(
    mut v_msg_3664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = l_Lean_instInhabitedExpr;
    v___x_3666_ = lean_panic_fn_borrowed(v___x_3665_, v_msg_3664_);
    return v___x_3666_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3670_ =
        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2;
    v___x_3671_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_3672_ = crate::leanh::lean_unsigned_to_nat(22);
    v___x_3673_ =
        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1;
    v___x_3674_ =
        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0;
    v___x_3675_ = l_mkPanicMessageWithDecl(
        v___x_3674_,
        v___x_3673_,
        v___x_3672_,
        v___x_3671_,
        v___x_3670_,
    );
    return v___x_3675_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(
    mut v_e_3676_: *mut crate::leanh::LeanObject,
    mut v_lhsNew_3677_: *mut crate::leanh::LeanObject,
    mut v_ty_x3f_3678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: u8 = 0;
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: u8 = 0;
    let mut v___x_3694_: u8 = 0;
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: u8 = 0;
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: u8 = 0;
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: u8 = 0;
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3679_ = l_Lean_Expr_cleanupAnnotations(v_e_3676_);
                v___x_3680_ = l_Lean_Expr_isApp(v___x_3679_);
                if v___x_3680_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3679_);
                    crate::leanh::lean_dec(v_ty_x3f_3678_);
                    crate::leanh::lean_dec_ref(v_lhsNew_3677_);
                    v___x_3681_ = crate::leanh::lean_box(0);
                    return v___x_3681_;
                } else {
                    v_arg_3682_ = crate::leanh::lean_ctor_get(v___x_3679_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3682_);
                    v___x_3683_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3679_);
                    v___x_3684_ = l_Lean_Expr_isApp(v___x_3683_);
                    if v___x_3684_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3683_);
                        crate::leanh::lean_dec_ref(v_arg_3682_);
                        crate::leanh::lean_dec(v_ty_x3f_3678_);
                        crate::leanh::lean_dec_ref(v_lhsNew_3677_);
                        v___x_3685_ = crate::leanh::lean_box(0);
                        return v___x_3685_;
                    } else {
                        v_arg_3686_ = crate::leanh::lean_ctor_get(v___x_3683_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3686_);
                        v___x_3687_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3683_);
                        v___x_3688_ = l_Lean_Expr_isApp(v___x_3687_);
                        if v___x_3688_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3687_);
                            crate::leanh::lean_dec_ref(v_arg_3686_);
                            crate::leanh::lean_dec_ref(v_arg_3682_);
                            crate::leanh::lean_dec(v_ty_x3f_3678_);
                            crate::leanh::lean_dec_ref(v_lhsNew_3677_);
                            v___x_3689_ = crate::leanh::lean_box(0);
                            return v___x_3689_;
                        } else {
                            v_arg_3690_ = crate::leanh::lean_ctor_get(v___x_3687_, 1);
                            crate::leanh::lean_inc_ref(v_arg_3690_);
                            v___x_3691_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3687_);
                            v___x_3692_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1;
                            v___x_3693_ = l_Lean_Expr_isConstOf(v___x_3691_, v___x_3692_);
                            if v___x_3693_ == 0 {
                                v___x_3694_ = l_Lean_Expr_isApp(v___x_3691_);
                                if v___x_3694_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_3691_);
                                    crate::leanh::lean_dec_ref(v_arg_3690_);
                                    crate::leanh::lean_dec_ref(v_arg_3686_);
                                    crate::leanh::lean_dec_ref(v_arg_3682_);
                                    crate::leanh::lean_dec(v_ty_x3f_3678_);
                                    crate::leanh::lean_dec_ref(v_lhsNew_3677_);
                                    v___x_3695_ = crate::leanh::lean_box(0);
                                    return v___x_3695_;
                                } else {
                                    v___x_3696_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3691_);
                                    v___x_3701_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3;
                                    v___x_3702_ = l_Lean_Expr_isConstOf(v___x_3696_, v___x_3701_);
                                    if v___x_3702_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_3696_);
                                        crate::leanh::lean_dec_ref(v_arg_3690_);
                                        crate::leanh::lean_dec_ref(v_arg_3686_);
                                        crate::leanh::lean_dec_ref(v_arg_3682_);
                                        crate::leanh::lean_dec(v_ty_x3f_3678_);
                                        crate::leanh::lean_dec_ref(v_lhsNew_3677_);
                                        v___x_3703_ = crate::leanh::lean_box(0);
                                        return v___x_3703_;
                                    } else {
                                        v___x_3704_ = l_Lean_Expr_hasLooseBVars(v_arg_3690_);
                                        crate::leanh::lean_dec_ref(v_arg_3690_);
                                        if v___x_3704_ == 0 {
                                            if crate::leanh::lean_obj_tag(v_ty_x3f_3678_) == 0 {
                                                v___x_3705_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3);
                                                v___x_3706_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(v___x_3705_);
                                                v___y_3698_ = v___x_3706_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v_val_3707_ =
                                                    crate::leanh::lean_ctor_get(v_ty_x3f_3678_, 0);
                                                crate::leanh::lean_inc(v_val_3707_);
                                                crate::leanh::lean_dec_ref_known(v_ty_x3f_3678_, 1);
                                                v___y_3698_ = v_val_3707_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3696_);
                                            crate::leanh::lean_dec_ref(v_arg_3686_);
                                            crate::leanh::lean_dec_ref(v_arg_3682_);
                                            crate::leanh::lean_dec(v_ty_x3f_3678_);
                                            crate::leanh::lean_dec_ref(v_lhsNew_3677_);
                                            v___x_3708_ = crate::leanh::lean_box(0);
                                            return v___x_3708_;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_ty_x3f_3678_);
                                v___x_3709_ = l_Lean_Expr_hasLooseBVars(v_arg_3686_);
                                crate::leanh::lean_dec_ref(v_arg_3686_);
                                if v___x_3709_ == 0 {
                                    v___x_3710_ = l_Lean_mkApp3(
                                        v___x_3691_,
                                        v_arg_3690_,
                                        v_lhsNew_3677_,
                                        v_arg_3682_,
                                    );
                                    v___x_3711_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3711_, 0, v___x_3710_);
                                    return v___x_3711_;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3691_);
                                    crate::leanh::lean_dec_ref(v_arg_3690_);
                                    crate::leanh::lean_dec_ref(v_arg_3682_);
                                    crate::leanh::lean_dec_ref(v_lhsNew_3677_);
                                    v___x_3712_ = crate::leanh::lean_box(0);
                                    return v___x_3712_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3699_ = l_Lean_mkApp4(
                    v___x_3696_,
                    v___y_3698_,
                    v_lhsNew_3677_,
                    v_arg_3686_,
                    v_arg_3682_,
                );
                v___x_3700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3700_, 0, v___x_3699_);
                return v___x_3700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(
    mut v_xs_3713_: *mut crate::leanh::LeanObject,
    mut v_tys_3714_: *mut crate::leanh::LeanObject,
    mut v_e_3715_: *mut crate::leanh::LeanObject,
    mut v_i_3716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderName_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3720_: u8 = 0;
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: u8 = 0;
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3732_: u8 = 0;
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: u8 = 0;
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: usize = 0;
    let mut v___x_3737_: usize = 0;
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: usize = 0;
    let mut v___x_3740_: usize = 0;
    let mut v___x_3741_: u8 = 0;
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: u8 = 0;
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: u8 = 0;
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: usize = 0;
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: usize = 0;
    let mut v___x_3751_: usize = 0;
    let mut v___x_3752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_3715_) == 7 {
                    v_binderName_3717_ = crate::leanh::lean_ctor_get(v_e_3715_, 0);
                    v_binderType_3718_ = crate::leanh::lean_ctor_get(v_e_3715_, 1);
                    v_body_3719_ = crate::leanh::lean_ctor_get(v_e_3715_, 2);
                    v_binderInfo_3720_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_3715_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_3721_ = lean_array_get_size(v_xs_3713_);
                    v___x_3722_ = lean_nat_dec_lt(v_i_3716_, v___x_3721_);
                    if v___x_3722_ == 0 {
                        return v_e_3715_;
                    } else {
                        v___x_3723_ = lean_array_fget_borrowed(v_xs_3713_, v_i_3716_);
                        v___x_3724_ = crate::leanh::lean_box(0);
                        v___x_3725_ = lean_array_get_borrowed(v___x_3724_, v_tys_3714_, v_i_3716_);
                        crate::leanh::lean_inc(v___x_3725_);
                        crate::leanh::lean_inc(v___x_3723_);
                        crate::leanh::lean_inc_ref(v_binderType_3718_);
                        v___x_3726_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(v_binderType_3718_, v___x_3723_, v___x_3725_);
                        if crate::leanh::lean_obj_tag(v___x_3726_) == 1 {
                            v_val_3727_ = crate::leanh::lean_ctor_get(v___x_3726_, 0);
                            crate::leanh::lean_inc(v_val_3727_);
                            crate::leanh::lean_dec_ref_known(v___x_3726_, 1);
                            v___x_3728_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3729_ = lean_nat_add(v_i_3716_, v___x_3728_);
                            crate::leanh::lean_inc_ref(v_body_3719_);
                            v___x_3730_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_3713_, v_tys_3714_, v_body_3719_, v___x_3729_);
                            crate::leanh::lean_dec(v___x_3729_);
                            v___x_3736_ = lean_ptr_addr(v_binderType_3718_);
                            v___x_3737_ = lean_ptr_addr(v_val_3727_);
                            v___x_3738_ = lean_usize_dec_eq(v___x_3736_, v___x_3737_);
                            if v___x_3738_ == 0 {
                                v___y_3732_ = v___x_3738_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3739_ = lean_ptr_addr(v_body_3719_);
                                v___x_3740_ = lean_ptr_addr(v___x_3730_);
                                v___x_3741_ = lean_usize_dec_eq(v___x_3739_, v___x_3740_);
                                v___y_3732_ = v___x_3741_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3726_);
                            crate::leanh::lean_inc_ref(v_body_3719_);
                            v___x_3742_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_3713_, v_tys_3714_, v_body_3719_, v_i_3716_);
                            v___x_3748_ = lean_ptr_addr(v_binderType_3718_);
                            v___x_3749_ = lean_usize_dec_eq(v___x_3748_, v___x_3748_);
                            if v___x_3749_ == 0 {
                                v___y_3744_ = v___x_3749_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3750_ = lean_ptr_addr(v_body_3719_);
                                v___x_3751_ = lean_ptr_addr(v___x_3742_);
                                v___x_3752_ = lean_usize_dec_eq(v___x_3750_, v___x_3751_);
                                v___y_3744_ = v___x_3752_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    return v_e_3715_;
                }
            }
            1 => {
                if v___y_3732_ == 0 {
                    crate::leanh::lean_inc(v_binderName_3717_);
                    crate::leanh::lean_dec_ref_known(v_e_3715_, 3);
                    v___x_3733_ = l_Lean_Expr_forallE___override(
                        v_binderName_3717_,
                        v_val_3727_,
                        v___x_3730_,
                        v_binderInfo_3720_,
                    );
                    return v___x_3733_;
                } else {
                    v___x_3734_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_3720_, v_binderInfo_3720_);
                    if v___x_3734_ == 0 {
                        crate::leanh::lean_inc(v_binderName_3717_);
                        crate::leanh::lean_dec_ref_known(v_e_3715_, 3);
                        v___x_3735_ = l_Lean_Expr_forallE___override(
                            v_binderName_3717_,
                            v_val_3727_,
                            v___x_3730_,
                            v_binderInfo_3720_,
                        );
                        return v___x_3735_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3730_);
                        crate::leanh::lean_dec(v_val_3727_);
                        return v_e_3715_;
                    }
                }
            }
            2 => {
                if v___y_3744_ == 0 {
                    crate::leanh::lean_inc_ref(v_binderType_3718_);
                    crate::leanh::lean_inc(v_binderName_3717_);
                    crate::leanh::lean_dec_ref_known(v_e_3715_, 3);
                    v___x_3745_ = l_Lean_Expr_forallE___override(
                        v_binderName_3717_,
                        v_binderType_3718_,
                        v___x_3742_,
                        v_binderInfo_3720_,
                    );
                    return v___x_3745_;
                } else {
                    v___x_3746_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_3720_, v_binderInfo_3720_);
                    if v___x_3746_ == 0 {
                        crate::leanh::lean_inc_ref(v_binderType_3718_);
                        crate::leanh::lean_inc(v_binderName_3717_);
                        crate::leanh::lean_dec_ref_known(v_e_3715_, 3);
                        v___x_3747_ = l_Lean_Expr_forallE___override(
                            v_binderName_3717_,
                            v_binderType_3718_,
                            v___x_3742_,
                            v_binderInfo_3720_,
                        );
                        return v___x_3747_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3742_);
                        return v_e_3715_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(
    mut v_xs_3753_: *mut crate::leanh::LeanObject,
    mut v_tys_3754_: *mut crate::leanh::LeanObject,
    mut v_e_3755_: *mut crate::leanh::LeanObject,
    mut v_i_3756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3757_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_3753_, v_tys_3754_, v_e_3755_, v_i_3756_);
    crate::leanh::lean_dec(v_i_3756_);
    crate::leanh::lean_dec_ref(v_tys_3754_);
    crate::leanh::lean_dec_ref(v_xs_3753_);
    return v_res_3757_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(
    mut v_k_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
    mut v___y_3760_: *mut crate::leanh::LeanObject,
    mut v___y_3761_: *mut crate::leanh::LeanObject,
    mut v___y_3762_: *mut crate::leanh::LeanObject,
    mut v___y_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
    mut v_b_3765_: *mut crate::leanh::LeanObject,
    mut v___y_3766_: *mut crate::leanh::LeanObject,
    mut v___y_3767_: *mut crate::leanh::LeanObject,
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3769_);
    crate::leanh::lean_inc_ref(v___y_3768_);
    crate::leanh::lean_inc(v___y_3767_);
    crate::leanh::lean_inc_ref(v___y_3766_);
    crate::leanh::lean_inc(v___y_3764_);
    crate::leanh::lean_inc_ref(v___y_3763_);
    crate::leanh::lean_inc(v___y_3762_);
    crate::leanh::lean_inc_ref(v___y_3761_);
    crate::leanh::lean_inc(v___y_3760_);
    crate::leanh::lean_inc(v___y_3759_);
    v___x_3771_ = crate::leanh::lean_apply_12(
        v_k_3758_,
        v_b_3765_,
        v___y_3759_,
        v___y_3760_,
        v___y_3761_,
        v___y_3762_,
        v___y_3763_,
        v___y_3764_,
        v___y_3766_,
        v___y_3767_,
        v___y_3768_,
        v___y_3769_,
        crate::leanh::lean_box(0),
    );
    return v___x_3771_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_3772_: *mut crate::leanh::LeanObject,
    mut v___y_3773_: *mut crate::leanh::LeanObject,
    mut v___y_3774_: *mut crate::leanh::LeanObject,
    mut v___y_3775_: *mut crate::leanh::LeanObject,
    mut v___y_3776_: *mut crate::leanh::LeanObject,
    mut v___y_3777_: *mut crate::leanh::LeanObject,
    mut v___y_3778_: *mut crate::leanh::LeanObject,
    mut v_b_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
    mut v___y_3783_: *mut crate::leanh::LeanObject,
    mut v___y_3784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3785_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(v_k_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v_b_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
    crate::leanh::lean_dec(v___y_3783_);
    crate::leanh::lean_dec_ref(v___y_3782_);
    crate::leanh::lean_dec(v___y_3781_);
    crate::leanh::lean_dec_ref(v___y_3780_);
    crate::leanh::lean_dec(v___y_3778_);
    crate::leanh::lean_dec_ref(v___y_3777_);
    crate::leanh::lean_dec(v___y_3776_);
    crate::leanh::lean_dec_ref(v___y_3775_);
    crate::leanh::lean_dec(v___y_3774_);
    crate::leanh::lean_dec(v___y_3773_);
    return v_res_3785_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(
    mut v_name_3786_: *mut crate::leanh::LeanObject,
    mut v_bi_3787_: u8,
    mut v_type_3788_: *mut crate::leanh::LeanObject,
    mut v_k_3789_: *mut crate::leanh::LeanObject,
    mut v_kind_3790_: u8,
    mut v___y_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
    mut v___y_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
    mut v___y_3796_: *mut crate::leanh::LeanObject,
    mut v___y_3797_: *mut crate::leanh::LeanObject,
    mut v___y_3798_: *mut crate::leanh::LeanObject,
    mut v___y_3799_: *mut crate::leanh::LeanObject,
    mut v___y_3800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3807_: u8 = 0;
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3811_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3796_);
                crate::leanh::lean_inc_ref(v___y_3795_);
                crate::leanh::lean_inc(v___y_3794_);
                crate::leanh::lean_inc_ref(v___y_3793_);
                crate::leanh::lean_inc(v___y_3792_);
                crate::leanh::lean_inc(v___y_3791_);
                v___f_3802_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 7);
                crate::leanh::lean_closure_set(v___f_3802_, 0, v_k_3789_);
                crate::leanh::lean_closure_set(v___f_3802_, 1, v___y_3791_);
                crate::leanh::lean_closure_set(v___f_3802_, 2, v___y_3792_);
                crate::leanh::lean_closure_set(v___f_3802_, 3, v___y_3793_);
                crate::leanh::lean_closure_set(v___f_3802_, 4, v___y_3794_);
                crate::leanh::lean_closure_set(v___f_3802_, 5, v___y_3795_);
                crate::leanh::lean_closure_set(v___f_3802_, 6, v___y_3796_);
                v___x_3803_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3786_,
                    v_bi_3787_,
                    v_type_3788_,
                    v___f_3802_,
                    v_kind_3790_,
                    v___y_3797_,
                    v___y_3798_,
                    v___y_3799_,
                    v___y_3800_,
                );
                if crate::leanh::lean_obj_tag(v___x_3803_) == 0 {
                    return v___x_3803_;
                } else {
                    v_a_3804_ = crate::leanh::lean_ctor_get(v___x_3803_, 0);
                    v_isSharedCheck_3811_ = (!crate::leanh::lean_is_exclusive(v___x_3803_)) as u8;
                    if v_isSharedCheck_3811_ == 0 {
                        v___x_3806_ = v___x_3803_;
                        v_isShared_3807_ = v_isSharedCheck_3811_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3804_);
                        crate::leanh::lean_dec(v___x_3803_);
                        v___x_3806_ = crate::leanh::lean_box(0);
                        v_isShared_3807_ = v_isSharedCheck_3811_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3807_ == 0 {
                    v___x_3809_ = v___x_3806_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3810_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_a_3804_);
                    v___x_3809_ = v_reuseFailAlloc_3810_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___boxed(
    mut v_name_3812_: *mut crate::leanh::LeanObject,
    mut v_bi_3813_: *mut crate::leanh::LeanObject,
    mut v_type_3814_: *mut crate::leanh::LeanObject,
    mut v_k_3815_: *mut crate::leanh::LeanObject,
    mut v_kind_3816_: *mut crate::leanh::LeanObject,
    mut v___y_3817_: *mut crate::leanh::LeanObject,
    mut v___y_3818_: *mut crate::leanh::LeanObject,
    mut v___y_3819_: *mut crate::leanh::LeanObject,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
    mut v___y_3821_: *mut crate::leanh::LeanObject,
    mut v___y_3822_: *mut crate::leanh::LeanObject,
    mut v___y_3823_: *mut crate::leanh::LeanObject,
    mut v___y_3824_: *mut crate::leanh::LeanObject,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
    mut v___y_3826_: *mut crate::leanh::LeanObject,
    mut v___y_3827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3828_: u8 = 0;
    let mut v_kind_boxed_3829_: u8 = 0;
    let mut v_res_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3828_ = (crate::leanh::lean_unbox(v_bi_3813_) as u8);
    v_kind_boxed_3829_ = (crate::leanh::lean_unbox(v_kind_3816_) as u8);
    v_res_3830_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_3812_, v_bi_boxed_3828_, v_type_3814_, v_k_3815_, v_kind_boxed_3829_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
    crate::leanh::lean_dec(v___y_3826_);
    crate::leanh::lean_dec_ref(v___y_3825_);
    crate::leanh::lean_dec(v___y_3824_);
    crate::leanh::lean_dec_ref(v___y_3823_);
    crate::leanh::lean_dec(v___y_3822_);
    crate::leanh::lean_dec_ref(v___y_3821_);
    crate::leanh::lean_dec(v___y_3820_);
    crate::leanh::lean_dec_ref(v___y_3819_);
    crate::leanh::lean_dec(v___y_3818_);
    crate::leanh::lean_dec(v___y_3817_);
    return v_res_3830_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(
    mut v_name_3831_: *mut crate::leanh::LeanObject,
    mut v_type_3832_: *mut crate::leanh::LeanObject,
    mut v_k_3833_: *mut crate::leanh::LeanObject,
    mut v___y_3834_: *mut crate::leanh::LeanObject,
    mut v___y_3835_: *mut crate::leanh::LeanObject,
    mut v___y_3836_: *mut crate::leanh::LeanObject,
    mut v___y_3837_: *mut crate::leanh::LeanObject,
    mut v___y_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
    mut v___y_3841_: *mut crate::leanh::LeanObject,
    mut v___y_3842_: *mut crate::leanh::LeanObject,
    mut v___y_3843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3845_: u8 = 0;
    let mut v___x_3846_: u8 = 0;
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3845_ = 0;
    v___x_3846_ = 0;
    v___x_3847_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_3831_, v___x_3845_, v_type_3832_, v_k_3833_, v___x_3846_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
    return v___x_3847_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg___boxed(
    mut v_name_3848_: *mut crate::leanh::LeanObject,
    mut v_type_3849_: *mut crate::leanh::LeanObject,
    mut v_k_3850_: *mut crate::leanh::LeanObject,
    mut v___y_3851_: *mut crate::leanh::LeanObject,
    mut v___y_3852_: *mut crate::leanh::LeanObject,
    mut v___y_3853_: *mut crate::leanh::LeanObject,
    mut v___y_3854_: *mut crate::leanh::LeanObject,
    mut v___y_3855_: *mut crate::leanh::LeanObject,
    mut v___y_3856_: *mut crate::leanh::LeanObject,
    mut v___y_3857_: *mut crate::leanh::LeanObject,
    mut v___y_3858_: *mut crate::leanh::LeanObject,
    mut v___y_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3862_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_3848_, v_type_3849_, v_k_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
    crate::leanh::lean_dec(v___y_3860_);
    crate::leanh::lean_dec_ref(v___y_3859_);
    crate::leanh::lean_dec(v___y_3858_);
    crate::leanh::lean_dec_ref(v___y_3857_);
    crate::leanh::lean_dec(v___y_3856_);
    crate::leanh::lean_dec_ref(v___y_3855_);
    crate::leanh::lean_dec(v___y_3854_);
    crate::leanh::lean_dec_ref(v___y_3853_);
    crate::leanh::lean_dec(v___y_3852_);
    crate::leanh::lean_dec(v___y_3851_);
    return v_res_3862_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_3866_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_xs_3867_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_tys_3868_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_tysxs_3869_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_args_3870_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_val_3871_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_fst_3872_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_e_3873_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_lhss_u03b1s_3874_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_ty_3875_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_3876_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3877_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3878_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3879_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3880_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3881_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3882_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3883_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_3884_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_3885_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_3886_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_res_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3887_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(v_i_3866_, v_xs_3867_, v_tys_3868_, v_tysxs_3869_, v_args_3870_, v_val_3871_, v_fst_3872_, v_e_3873_, v_lhss_u03b1s_3874_, v_ty_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
    crate::leanh::lean_dec(v___y_3885_);
    crate::leanh::lean_dec_ref(v___y_3884_);
    crate::leanh::lean_dec(v___y_3883_);
    crate::leanh::lean_dec_ref(v___y_3882_);
    crate::leanh::lean_dec(v___y_3881_);
    crate::leanh::lean_dec_ref(v___y_3880_);
    crate::leanh::lean_dec(v___y_3879_);
    crate::leanh::lean_dec_ref(v___y_3878_);
    crate::leanh::lean_dec(v___y_3877_);
    crate::leanh::lean_dec(v___y_3876_);
    return v_res_3887_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(
    mut v_i_3891_: *mut crate::leanh::LeanObject,
    mut v_xs_3892_: *mut crate::leanh::LeanObject,
    mut v_tys_3893_: *mut crate::leanh::LeanObject,
    mut v_tysxs_3894_: *mut crate::leanh::LeanObject,
    mut v_args_3895_: *mut crate::leanh::LeanObject,
    mut v_fst_3896_: *mut crate::leanh::LeanObject,
    mut v_e_3897_: *mut crate::leanh::LeanObject,
    mut v_lhss_u03b1s_3898_: *mut crate::leanh::LeanObject,
    mut v_x_3899_: *mut crate::leanh::LeanObject,
    mut v___y_3900_: *mut crate::leanh::LeanObject,
    mut v___y_3901_: *mut crate::leanh::LeanObject,
    mut v___y_3902_: *mut crate::leanh::LeanObject,
    mut v___y_3903_: *mut crate::leanh::LeanObject,
    mut v___y_3904_: *mut crate::leanh::LeanObject,
    mut v___y_3905_: *mut crate::leanh::LeanObject,
    mut v___y_3906_: *mut crate::leanh::LeanObject,
    mut v___y_3907_: *mut crate::leanh::LeanObject,
    mut v___y_3908_: *mut crate::leanh::LeanObject,
    mut v___y_3909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3911_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3912_ = lean_nat_add(v_i_3891_, v___x_3911_);
    crate::leanh::lean_inc_ref(v_x_3899_);
    v___x_3913_ = lean_array_push(v_xs_3892_, v_x_3899_);
    v___x_3914_ = crate::leanh::lean_box(0);
    v___x_3915_ = lean_array_push(v_tys_3893_, v___x_3914_);
    v___x_3916_ = lean_array_push(v_tysxs_3894_, v_x_3899_);
    v___x_3917_ = lean_array_push(v_args_3895_, v_fst_3896_);
    v___x_3918_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_3897_, v_lhss_u03b1s_3898_, v___x_3912_, v___x_3913_, v___x_3915_, v___x_3916_, v___x_3917_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
    return v___x_3918_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_3919_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_xs_3920_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_tys_3921_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_tysxs_3922_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_args_3923_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_fst_3924_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_e_3925_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_lhss_u03b1s_3926_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_x_3927_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_3928_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_3929_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3930_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3931_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3932_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3933_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3934_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3935_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3936_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_3937_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_3938_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_res_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3939_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(v_i_3919_, v_xs_3920_, v_tys_3921_, v_tysxs_3922_, v_args_3923_, v_fst_3924_, v_e_3925_, v_lhss_u03b1s_3926_, v_x_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
    crate::leanh::lean_dec(v___y_3937_);
    crate::leanh::lean_dec_ref(v___y_3936_);
    crate::leanh::lean_dec(v___y_3935_);
    crate::leanh::lean_dec_ref(v___y_3934_);
    crate::leanh::lean_dec(v___y_3933_);
    crate::leanh::lean_dec_ref(v___y_3932_);
    crate::leanh::lean_dec(v___y_3931_);
    crate::leanh::lean_dec_ref(v___y_3930_);
    crate::leanh::lean_dec(v___y_3929_);
    crate::leanh::lean_dec(v___y_3928_);
    crate::leanh::lean_dec(v_i_3919_);
    return v_res_3939_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(
    mut v_e_3940_: *mut crate::leanh::LeanObject,
    mut v_lhss_u03b1s_3941_: *mut crate::leanh::LeanObject,
    mut v_i_3942_: *mut crate::leanh::LeanObject,
    mut v_xs_3943_: *mut crate::leanh::LeanObject,
    mut v_tys_3944_: *mut crate::leanh::LeanObject,
    mut v_tysxs_3945_: *mut crate::leanh::LeanObject,
    mut v_args_3946_: *mut crate::leanh::LeanObject,
    mut v_a_3947_: *mut crate::leanh::LeanObject,
    mut v_a_3948_: *mut crate::leanh::LeanObject,
    mut v_a_3949_: *mut crate::leanh::LeanObject,
    mut v_a_3950_: *mut crate::leanh::LeanObject,
    mut v_a_3951_: *mut crate::leanh::LeanObject,
    mut v_a_3952_: *mut crate::leanh::LeanObject,
    mut v_a_3953_: *mut crate::leanh::LeanObject,
    mut v_a_3954_: *mut crate::leanh::LeanObject,
    mut v_a_3955_: *mut crate::leanh::LeanObject,
    mut v_a_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAbst_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: u8 = 0;
    let mut v___x_3963_: u8 = 0;
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3971_: u8 = 0;
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut v_a_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3980_: u8 = 0;
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3984_: u8 = 0;
    let mut v_a_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3988_: u8 = 0;
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3992_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4006_: u8 = 0;
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4010_: u8 = 0;
    let mut v_fst_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3958_ = lean_array_get_size(v_lhss_u03b1s_3941_);
                v___x_3959_ = lean_nat_dec_lt(v_i_3942_, v___x_3958_);
                if v___x_3959_ == 0 {
                    crate::leanh::lean_dec(v_i_3942_);
                    crate::leanh::lean_dec_ref(v_lhss_u03b1s_3941_);
                    v___x_3960_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_eAbst_3961_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(v_xs_3943_, v_tys_3944_, v_e_3940_, v___x_3960_);
                    crate::leanh::lean_dec_ref(v_tys_3944_);
                    crate::leanh::lean_dec_ref(v_xs_3943_);
                    v___x_3962_ = 1;
                    v___x_3963_ = 1;
                    v___x_3964_ = l_Lean_Meta_mkLambdaFVars(
                        v_tysxs_3945_,
                        v_eAbst_3961_,
                        v___x_3959_,
                        v___x_3962_,
                        v___x_3959_,
                        v___x_3962_,
                        v___x_3963_,
                        v_a_3953_,
                        v_a_3954_,
                        v_a_3955_,
                        v_a_3956_,
                    );
                    crate::leanh::lean_dec_ref(v_tysxs_3945_);
                    if crate::leanh::lean_obj_tag(v___x_3964_) == 0 {
                        v_a_3965_ = crate::leanh::lean_ctor_get(v___x_3964_, 0);
                        crate::leanh::lean_inc(v_a_3965_);
                        crate::leanh::lean_dec_ref_known(v___x_3964_, 1);
                        v___x_3966_ = l_Lean_mkAppN(v_a_3965_, v_args_3946_);
                        v___x_3967_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_3966_, v_a_3952_);
                        if crate::leanh::lean_obj_tag(v___x_3967_) == 0 {
                            v_a_3968_ = crate::leanh::lean_ctor_get(v___x_3967_, 0);
                            v_isSharedCheck_3976_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3967_)) as u8;
                            if v_isSharedCheck_3976_ == 0 {
                                v___x_3970_ = v___x_3967_;
                                v_isShared_3971_ = v_isSharedCheck_3976_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3968_);
                                crate::leanh::lean_dec(v___x_3967_);
                                v___x_3970_ = crate::leanh::lean_box(0);
                                v_isShared_3971_ = v_isSharedCheck_3976_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_args_3946_);
                            v_a_3977_ = crate::leanh::lean_ctor_get(v___x_3967_, 0);
                            v_isSharedCheck_3984_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3967_)) as u8;
                            if v_isSharedCheck_3984_ == 0 {
                                v___x_3979_ = v___x_3967_;
                                v_isShared_3980_ = v_isSharedCheck_3984_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3977_);
                                crate::leanh::lean_dec(v___x_3967_);
                                v___x_3979_ = crate::leanh::lean_box(0);
                                v_isShared_3980_ = v_isSharedCheck_3984_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_args_3946_);
                        v_a_3985_ = crate::leanh::lean_ctor_get(v___x_3964_, 0);
                        v_isSharedCheck_3992_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3964_)) as u8;
                        if v_isSharedCheck_3992_ == 0 {
                            v___x_3987_ = v___x_3964_;
                            v_isShared_3988_ = v_isSharedCheck_3992_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3985_);
                            crate::leanh::lean_dec(v___x_3964_);
                            v___x_3987_ = crate::leanh::lean_box(0);
                            v_isShared_3988_ = v_isSharedCheck_3992_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v___x_3993_ = lean_array_fget_borrowed(v_lhss_u03b1s_3941_, v_i_3942_);
                    v_snd_3994_ = crate::leanh::lean_ctor_get(v___x_3993_, 1);
                    if crate::leanh::lean_obj_tag(v_snd_3994_) == 1 {
                        v_fst_3995_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                        crate::leanh::lean_inc(v_fst_3995_);
                        v_val_3996_ = crate::leanh::lean_ctor_get(v_snd_3994_, 0);
                        crate::leanh::lean_inc_n(v_val_3996_, 2);
                        crate::leanh::lean_inc(v_a_3956_);
                        crate::leanh::lean_inc_ref(v_a_3955_);
                        crate::leanh::lean_inc(v_a_3954_);
                        crate::leanh::lean_inc_ref(v_a_3953_);
                        v___x_3997_ = lean_infer_type(
                            v_val_3996_,
                            v_a_3953_,
                            v_a_3954_,
                            v_a_3955_,
                            v_a_3956_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3997_) == 0 {
                            v_a_3998_ = crate::leanh::lean_ctor_get(v___x_3997_, 0);
                            crate::leanh::lean_inc(v_a_3998_);
                            crate::leanh::lean_dec_ref_known(v___x_3997_, 1);
                            crate::leanh::lean_inc(v_i_3942_);
                            v___f_3999_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed as *mut core::ffi::c_void, 21, 9);
                            crate::leanh::lean_closure_set(v___f_3999_, 0, v_i_3942_);
                            crate::leanh::lean_closure_set(v___f_3999_, 1, v_xs_3943_);
                            crate::leanh::lean_closure_set(v___f_3999_, 2, v_tys_3944_);
                            crate::leanh::lean_closure_set(v___f_3999_, 3, v_tysxs_3945_);
                            crate::leanh::lean_closure_set(v___f_3999_, 4, v_args_3946_);
                            crate::leanh::lean_closure_set(v___f_3999_, 5, v_val_3996_);
                            crate::leanh::lean_closure_set(v___f_3999_, 6, v_fst_3995_);
                            crate::leanh::lean_closure_set(v___f_3999_, 7, v_e_3940_);
                            crate::leanh::lean_closure_set(v___f_3999_, 8, v_lhss_u03b1s_3941_);
                            v___x_4000_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1;
                            v___x_4001_ = lean_name_append_index_after(v___x_4000_, v_i_3942_);
                            v___x_4002_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_4001_, v_a_3998_, v___f_3999_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
                            return v___x_4002_;
                        } else {
                            crate::leanh::lean_dec(v_val_3996_);
                            crate::leanh::lean_dec(v_fst_3995_);
                            crate::leanh::lean_dec_ref(v_args_3946_);
                            crate::leanh::lean_dec_ref(v_tysxs_3945_);
                            crate::leanh::lean_dec_ref(v_tys_3944_);
                            crate::leanh::lean_dec_ref(v_xs_3943_);
                            crate::leanh::lean_dec(v_i_3942_);
                            crate::leanh::lean_dec_ref(v_lhss_u03b1s_3941_);
                            crate::leanh::lean_dec_ref(v_e_3940_);
                            v_a_4003_ = crate::leanh::lean_ctor_get(v___x_3997_, 0);
                            v_isSharedCheck_4010_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3997_)) as u8;
                            if v_isSharedCheck_4010_ == 0 {
                                v___x_4005_ = v___x_3997_;
                                v_isShared_4006_ = v_isSharedCheck_4010_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4003_);
                                crate::leanh::lean_dec(v___x_3997_);
                                v___x_4005_ = crate::leanh::lean_box(0);
                                v_isShared_4006_ = v_isSharedCheck_4010_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        v_fst_4011_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                        crate::leanh::lean_inc_n(v_fst_4011_, 2);
                        crate::leanh::lean_inc(v_a_3956_);
                        crate::leanh::lean_inc_ref(v_a_3955_);
                        crate::leanh::lean_inc(v_a_3954_);
                        crate::leanh::lean_inc_ref(v_a_3953_);
                        v___x_4012_ = lean_infer_type(
                            v_fst_4011_,
                            v_a_3953_,
                            v_a_3954_,
                            v_a_3955_,
                            v_a_3956_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4012_) == 0 {
                            v_a_4013_ = crate::leanh::lean_ctor_get(v___x_4012_, 0);
                            crate::leanh::lean_inc(v_a_4013_);
                            crate::leanh::lean_dec_ref_known(v___x_4012_, 1);
                            crate::leanh::lean_inc(v_i_3942_);
                            v___f_4014_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed as *mut core::ffi::c_void, 20, 8);
                            crate::leanh::lean_closure_set(v___f_4014_, 0, v_i_3942_);
                            crate::leanh::lean_closure_set(v___f_4014_, 1, v_xs_3943_);
                            crate::leanh::lean_closure_set(v___f_4014_, 2, v_tys_3944_);
                            crate::leanh::lean_closure_set(v___f_4014_, 3, v_tysxs_3945_);
                            crate::leanh::lean_closure_set(v___f_4014_, 4, v_args_3946_);
                            crate::leanh::lean_closure_set(v___f_4014_, 5, v_fst_4011_);
                            crate::leanh::lean_closure_set(v___f_4014_, 6, v_e_3940_);
                            crate::leanh::lean_closure_set(v___f_4014_, 7, v_lhss_u03b1s_3941_);
                            v___x_4015_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1;
                            v___x_4016_ = lean_name_append_index_after(v___x_4015_, v_i_3942_);
                            v___x_4017_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_4016_, v_a_4013_, v___f_4014_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
                            return v___x_4017_;
                        } else {
                            crate::leanh::lean_dec(v_fst_4011_);
                            crate::leanh::lean_dec_ref(v_args_3946_);
                            crate::leanh::lean_dec_ref(v_tysxs_3945_);
                            crate::leanh::lean_dec_ref(v_tys_3944_);
                            crate::leanh::lean_dec_ref(v_xs_3943_);
                            crate::leanh::lean_dec(v_i_3942_);
                            crate::leanh::lean_dec_ref(v_lhss_u03b1s_3941_);
                            crate::leanh::lean_dec_ref(v_e_3940_);
                            v_a_4018_ = crate::leanh::lean_ctor_get(v___x_4012_, 0);
                            v_isSharedCheck_4025_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4012_)) as u8;
                            if v_isSharedCheck_4025_ == 0 {
                                v___x_4020_ = v___x_4012_;
                                v_isShared_4021_ = v_isSharedCheck_4025_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4018_);
                                crate::leanh::lean_dec(v___x_4012_);
                                v___x_4020_ = crate::leanh::lean_box(0);
                                v_isShared_4021_ = v_isSharedCheck_4025_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3972_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3972_, 0, v_args_3946_);
                crate::leanh::lean_ctor_set(v___x_3972_, 1, v_a_3968_);
                if v_isShared_3971_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3970_, 0, v___x_3972_);
                    v___x_3974_ = v___x_3970_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3972_);
                    v___x_3974_ = v_reuseFailAlloc_3975_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3974_;
            }
            3 => {
                if v_isShared_3980_ == 0 {
                    v___x_3982_ = v___x_3979_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3983_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
                    v___x_3982_ = v_reuseFailAlloc_3983_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3982_;
            }
            5 => {
                if v_isShared_3988_ == 0 {
                    v___x_3990_ = v___x_3987_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3991_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
                    v___x_3990_ = v_reuseFailAlloc_3991_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3990_;
            }
            7 => {
                if v_isShared_4006_ == 0 {
                    v___x_4008_ = v___x_4005_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
                    v___x_4008_ = v_reuseFailAlloc_4009_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4008_;
            }
            9 => {
                if v_isShared_4021_ == 0 {
                    v___x_4023_ = v___x_4020_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4024_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
                    v___x_4023_ = v_reuseFailAlloc_4024_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(
    mut v_i_4026_: *mut crate::leanh::LeanObject,
    mut v_xs_4027_: *mut crate::leanh::LeanObject,
    mut v_ty_4028_: *mut crate::leanh::LeanObject,
    mut v_tys_4029_: *mut crate::leanh::LeanObject,
    mut v_tysxs_4030_: *mut crate::leanh::LeanObject,
    mut v_args_4031_: *mut crate::leanh::LeanObject,
    mut v_val_4032_: *mut crate::leanh::LeanObject,
    mut v_fst_4033_: *mut crate::leanh::LeanObject,
    mut v_e_4034_: *mut crate::leanh::LeanObject,
    mut v_lhss_u03b1s_4035_: *mut crate::leanh::LeanObject,
    mut v_x_4036_: *mut crate::leanh::LeanObject,
    mut v___y_4037_: *mut crate::leanh::LeanObject,
    mut v___y_4038_: *mut crate::leanh::LeanObject,
    mut v___y_4039_: *mut crate::leanh::LeanObject,
    mut v___y_4040_: *mut crate::leanh::LeanObject,
    mut v___y_4041_: *mut crate::leanh::LeanObject,
    mut v___y_4042_: *mut crate::leanh::LeanObject,
    mut v___y_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4048_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4049_ = lean_nat_add(v_i_4026_, v___x_4048_);
    crate::leanh::lean_inc_ref(v_x_4036_);
    v___x_4050_ = lean_array_push(v_xs_4027_, v_x_4036_);
    crate::leanh::lean_inc_ref(v_ty_4028_);
    v___x_4051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4051_, 0, v_ty_4028_);
    v___x_4052_ = lean_array_push(v_tys_4029_, v___x_4051_);
    v___x_4053_ = lean_array_push(v_tysxs_4030_, v_ty_4028_);
    v___x_4054_ = lean_array_push(v___x_4053_, v_x_4036_);
    v___x_4055_ = lean_array_push(v_args_4031_, v_val_4032_);
    v___x_4056_ = lean_array_push(v___x_4055_, v_fst_4033_);
    v___x_4057_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_4034_, v_lhss_u03b1s_4035_, v___x_4049_, v___x_4050_, v___x_4052_, v___x_4054_, v___x_4056_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
    return v___x_4057_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_4058_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_xs_4059_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_ty_4060_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_tys_4061_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_tysxs_4062_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_args_4063_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_val_4064_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_fst_4065_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_e_4066_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_lhss_u03b1s_4067_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_x_4068_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4069_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4070_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4071_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4072_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4073_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4074_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4075_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4076_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_4077_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_4078_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_4079_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_res_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4080_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(v_i_4058_, v_xs_4059_, v_ty_4060_, v_tys_4061_, v_tysxs_4062_, v_args_4063_, v_val_4064_, v_fst_4065_, v_e_4066_, v_lhss_u03b1s_4067_, v_x_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
    crate::leanh::lean_dec(v___y_4078_);
    crate::leanh::lean_dec_ref(v___y_4077_);
    crate::leanh::lean_dec(v___y_4076_);
    crate::leanh::lean_dec_ref(v___y_4075_);
    crate::leanh::lean_dec(v___y_4074_);
    crate::leanh::lean_dec_ref(v___y_4073_);
    crate::leanh::lean_dec(v___y_4072_);
    crate::leanh::lean_dec_ref(v___y_4071_);
    crate::leanh::lean_dec(v___y_4070_);
    crate::leanh::lean_dec(v___y_4069_);
    crate::leanh::lean_dec(v_i_4058_);
    return v_res_4080_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(
    mut v_i_4081_: *mut crate::leanh::LeanObject,
    mut v_xs_4082_: *mut crate::leanh::LeanObject,
    mut v_tys_4083_: *mut crate::leanh::LeanObject,
    mut v_tysxs_4084_: *mut crate::leanh::LeanObject,
    mut v_args_4085_: *mut crate::leanh::LeanObject,
    mut v_val_4086_: *mut crate::leanh::LeanObject,
    mut v_fst_4087_: *mut crate::leanh::LeanObject,
    mut v_e_4088_: *mut crate::leanh::LeanObject,
    mut v_lhss_u03b1s_4089_: *mut crate::leanh::LeanObject,
    mut v_ty_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
    mut v___y_4096_: *mut crate::leanh::LeanObject,
    mut v___y_4097_: *mut crate::leanh::LeanObject,
    mut v___y_4098_: *mut crate::leanh::LeanObject,
    mut v___y_4099_: *mut crate::leanh::LeanObject,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_ty_4090_);
    crate::leanh::lean_inc(v_i_4081_);
    v___f_4102_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed as *mut core::ffi::c_void, 22, 10);
    crate::leanh::lean_closure_set(v___f_4102_, 0, v_i_4081_);
    crate::leanh::lean_closure_set(v___f_4102_, 1, v_xs_4082_);
    crate::leanh::lean_closure_set(v___f_4102_, 2, v_ty_4090_);
    crate::leanh::lean_closure_set(v___f_4102_, 3, v_tys_4083_);
    crate::leanh::lean_closure_set(v___f_4102_, 4, v_tysxs_4084_);
    crate::leanh::lean_closure_set(v___f_4102_, 5, v_args_4085_);
    crate::leanh::lean_closure_set(v___f_4102_, 6, v_val_4086_);
    crate::leanh::lean_closure_set(v___f_4102_, 7, v_fst_4087_);
    crate::leanh::lean_closure_set(v___f_4102_, 8, v_e_4088_);
    crate::leanh::lean_closure_set(v___f_4102_, 9, v_lhss_u03b1s_4089_);
    v___x_4103_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1;
    v___x_4104_ = lean_name_append_index_after(v___x_4103_, v_i_4081_);
    v___x_4105_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v___x_4104_, v_ty_4090_, v___f_4102_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
    return v___x_4105_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_4106_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_lhss_u03b1s_4107_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_i_4108_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_xs_4109_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_tys_4110_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_tysxs_4111_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_args_4112_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_4113_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_4114_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_4115_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_a_4116_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_4117_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_4118_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_4119_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_a_4120_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_a_4121_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_a_4122_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_a_4123_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4124_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_e_4106_, v_lhss_u03b1s_4107_, v_i_4108_, v_xs_4109_, v_tys_4110_, v_tysxs_4111_, v_args_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_);
    crate::leanh::lean_dec(v_a_4122_);
    crate::leanh::lean_dec_ref(v_a_4121_);
    crate::leanh::lean_dec(v_a_4120_);
    crate::leanh::lean_dec_ref(v_a_4119_);
    crate::leanh::lean_dec(v_a_4118_);
    crate::leanh::lean_dec_ref(v_a_4117_);
    crate::leanh::lean_dec(v_a_4116_);
    crate::leanh::lean_dec_ref(v_a_4115_);
    crate::leanh::lean_dec(v_a_4114_);
    crate::leanh::lean_dec(v_a_4113_);
    return v_res_4124_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(
    mut v_00_u03b1_4125_: *mut crate::leanh::LeanObject,
    mut v_name_4126_: *mut crate::leanh::LeanObject,
    mut v_bi_4127_: u8,
    mut v_type_4128_: *mut crate::leanh::LeanObject,
    mut v_k_4129_: *mut crate::leanh::LeanObject,
    mut v_kind_4130_: u8,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
    mut v___y_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(v_name_4126_, v_bi_4127_, v_type_4128_, v_k_4129_, v_kind_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
    return v___x_4142_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03b1_4143_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_name_4144_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_bi_4145_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_type_4146_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_4147_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_kind_4148_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4149_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4150_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4151_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4152_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4153_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4154_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4155_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4156_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4157_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4158_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4159_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_bi_boxed_4160_: u8 = 0;
    let mut v_kind_boxed_4161_: u8 = 0;
    let mut v_res_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4160_ = (crate::leanh::lean_unbox(v_bi_4145_) as u8);
    v_kind_boxed_4161_ = (crate::leanh::lean_unbox(v_kind_4148_) as u8);
    v_res_4162_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(v_00_u03b1_4143_, v_name_4144_, v_bi_boxed_4160_, v_type_4146_, v_k_4147_, v_kind_boxed_4161_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
    crate::leanh::lean_dec(v___y_4158_);
    crate::leanh::lean_dec_ref(v___y_4157_);
    crate::leanh::lean_dec(v___y_4156_);
    crate::leanh::lean_dec_ref(v___y_4155_);
    crate::leanh::lean_dec(v___y_4154_);
    crate::leanh::lean_dec_ref(v___y_4153_);
    crate::leanh::lean_dec(v___y_4152_);
    crate::leanh::lean_dec_ref(v___y_4151_);
    crate::leanh::lean_dec(v___y_4150_);
    crate::leanh::lean_dec(v___y_4149_);
    return v_res_4162_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(
    mut v_00_u03b1_4163_: *mut crate::leanh::LeanObject,
    mut v_name_4164_: *mut crate::leanh::LeanObject,
    mut v_type_4165_: *mut crate::leanh::LeanObject,
    mut v_k_4166_: *mut crate::leanh::LeanObject,
    mut v___y_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
    mut v___y_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4178_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(v_name_4164_, v_type_4165_, v_k_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
    return v___x_4178_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___boxed(
    mut v_00_u03b1_4179_: *mut crate::leanh::LeanObject,
    mut v_name_4180_: *mut crate::leanh::LeanObject,
    mut v_type_4181_: *mut crate::leanh::LeanObject,
    mut v_k_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
    mut v___y_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4194_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(v_00_u03b1_4179_, v_name_4180_, v_type_4181_, v_k_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
    crate::leanh::lean_dec(v___y_4192_);
    crate::leanh::lean_dec_ref(v___y_4191_);
    crate::leanh::lean_dec(v___y_4190_);
    crate::leanh::lean_dec_ref(v___y_4189_);
    crate::leanh::lean_dec(v___y_4188_);
    crate::leanh::lean_dec_ref(v___y_4187_);
    crate::leanh::lean_dec(v___y_4186_);
    crate::leanh::lean_dec_ref(v___y_4185_);
    crate::leanh::lean_dec(v___y_4184_);
    crate::leanh::lean_dec(v___y_4183_);
    return v_res_4194_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(
    mut v_x_4195_: *mut crate::leanh::LeanObject,
    mut v_h__1_4196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4197_ = crate::leanh::lean_ctor_get(v_x_4195_, 0);
    crate::leanh::lean_inc(v_fst_4197_);
    v_snd_4198_ = crate::leanh::lean_ctor_get(v_x_4195_, 1);
    crate::leanh::lean_inc(v_snd_4198_);
    crate::leanh::lean_dec_ref(v_x_4195_);
    v___x_4199_ = crate::leanh::lean_apply_2(v_h__1_4196_, v_fst_4197_, v_snd_4198_);
    return v___x_4199_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter(
    mut v_motive_4200_: *mut crate::leanh::LeanObject,
    mut v_x_4201_: *mut crate::leanh::LeanObject,
    mut v_h__1_4202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_4203_ = crate::leanh::lean_ctor_get(v_x_4201_, 0);
    crate::leanh::lean_inc(v_fst_4203_);
    v_snd_4204_ = crate::leanh::lean_ctor_get(v_x_4201_, 1);
    crate::leanh::lean_inc(v_snd_4204_);
    crate::leanh::lean_dec_ref(v_x_4201_);
    v___x_4205_ = crate::leanh::lean_apply_2(v_h__1_4202_, v_fst_4203_, v_snd_4204_);
    return v___x_4205_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(
    mut v_00_u03b1_x3f_4206_: *mut crate::leanh::LeanObject,
    mut v_h__1_4207_: *mut crate::leanh::LeanObject,
    mut v_h__2_4208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_00_u03b1_x3f_4206_) == 1 {
        let mut v_val_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4208_);
        v_val_4209_ = crate::leanh::lean_ctor_get(v_00_u03b1_x3f_4206_, 0);
        crate::leanh::lean_inc(v_val_4209_);
        crate::leanh::lean_dec_ref_known(v_00_u03b1_x3f_4206_, 1);
        v___x_4210_ = crate::leanh::lean_apply_1(v_h__1_4207_, v_val_4209_);
        return v___x_4210_;
    } else {
        let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4207_);
        v___x_4211_ = crate::leanh::lean_apply_2(
            v_h__2_4208_,
            v_00_u03b1_x3f_4206_,
            crate::leanh::lean_box(0),
        );
        return v___x_4211_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(
    mut v_motive_4212_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_x3f_4213_: *mut crate::leanh::LeanObject,
    mut v_h__1_4214_: *mut crate::leanh::LeanObject,
    mut v_h__2_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_00_u03b1_x3f_4213_) == 1 {
        let mut v_val_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4215_);
        v_val_4216_ = crate::leanh::lean_ctor_get(v_00_u03b1_x3f_4213_, 0);
        crate::leanh::lean_inc(v_val_4216_);
        crate::leanh::lean_dec_ref_known(v_00_u03b1_x3f_4213_, 1);
        v___x_4217_ = crate::leanh::lean_apply_1(v_h__1_4214_, v_val_4216_);
        return v___x_4217_;
    } else {
        let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4214_);
        v___x_4218_ = crate::leanh::lean_apply_2(
            v_h__2_4215_,
            v_00_u03b1_x3f_4213_,
            crate::leanh::lean_box(0),
        );
        return v___x_4218_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(
    mut v_matchCond_4228_: *mut crate::leanh::LeanObject,
    mut v_a_4229_: *mut crate::leanh::LeanObject,
    mut v_a_4230_: *mut crate::leanh::LeanObject,
    mut v_a_4231_: *mut crate::leanh::LeanObject,
    mut v_a_4232_: *mut crate::leanh::LeanObject,
    mut v_a_4233_: *mut crate::leanh::LeanObject,
    mut v_a_4234_: *mut crate::leanh::LeanObject,
    mut v_a_4235_: *mut crate::leanh::LeanObject,
    mut v_a_4236_: *mut crate::leanh::LeanObject,
    mut v_a_4237_: *mut crate::leanh::LeanObject,
    mut v_a_4238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: u8 = 0;
    let mut v_arg_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: u8 = 0;
    let mut v_lhss_u03b1s_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_matchCond_4228_);
                v___x_4244_ = l_Lean_Expr_cleanupAnnotations(v_matchCond_4228_);
                v___x_4245_ = l_Lean_Expr_isApp(v___x_4244_);
                if v___x_4245_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4244_);
                    state = 1;
                    continue;
                } else {
                    v_arg_4246_ = crate::leanh::lean_ctor_get(v___x_4244_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4246_);
                    v___x_4247_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4244_);
                    v___x_4248_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4;
                    v___x_4249_ = l_Lean_Expr_isConstOf(v___x_4247_, v___x_4248_);
                    crate::leanh::lean_dec_ref(v___x_4247_);
                    if v___x_4249_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_4246_);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_matchCond_4228_);
                        crate::leanh::lean_inc_ref(v_arg_4246_);
                        v_lhss_u03b1s_4250_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(v_arg_4246_);
                        v___x_4251_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4252_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0;
                        v___x_4253_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(v_arg_4246_, v_lhss_u03b1s_4250_, v___x_4251_, v___x_4252_, v___x_4252_, v___x_4252_, v___x_4252_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
                        return v___x_4253_;
                    }
                }
            }
            1 => {
                v___x_4241_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0;
                v___x_4242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4242_, 0, v___x_4241_);
                crate::leanh::lean_ctor_set(v___x_4242_, 1, v_matchCond_4228_);
                v___x_4243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4242_);
                return v___x_4243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(
    mut v_matchCond_4254_: *mut crate::leanh::LeanObject,
    mut v_a_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
    mut v_a_4257_: *mut crate::leanh::LeanObject,
    mut v_a_4258_: *mut crate::leanh::LeanObject,
    mut v_a_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_a_4265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4266_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(
        v_matchCond_4254_,
        v_a_4255_,
        v_a_4256_,
        v_a_4257_,
        v_a_4258_,
        v_a_4259_,
        v_a_4260_,
        v_a_4261_,
        v_a_4262_,
        v_a_4263_,
        v_a_4264_,
    );
    crate::leanh::lean_dec(v_a_4264_);
    crate::leanh::lean_dec_ref(v_a_4263_);
    crate::leanh::lean_dec(v_a_4262_);
    crate::leanh::lean_dec_ref(v_a_4261_);
    crate::leanh::lean_dec(v_a_4260_);
    crate::leanh::lean_dec_ref(v_a_4259_);
    crate::leanh::lean_dec(v_a_4258_);
    crate::leanh::lean_dec_ref(v_a_4257_);
    crate::leanh::lean_dec(v_a_4256_);
    crate::leanh::lean_dec(v_a_4255_);
    return v_res_4266_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4270_ = crate::leanh::lean_box(0);
    v_dummy_4271_ = l_Lean_Expr_sort___override(v___x_4270_);
    return v_dummy_4271_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(
    mut v_lhs_4272_: *mut crate::leanh::LeanObject,
    mut v_rhs_4273_: *mut crate::leanh::LeanObject,
    mut v_a_4274_: *mut crate::leanh::LeanObject,
    mut v_a_4275_: *mut crate::leanh::LeanObject,
    mut v_a_4276_: *mut crate::leanh::LeanObject,
    mut v_a_4277_: *mut crate::leanh::LeanObject,
    mut v_a_4278_: *mut crate::leanh::LeanObject,
    mut v_a_4279_: *mut crate::leanh::LeanObject,
    mut v_a_4280_: *mut crate::leanh::LeanObject,
    mut v_a_4281_: *mut crate::leanh::LeanObject,
    mut v_a_4282_: *mut crate::leanh::LeanObject,
    mut v_a_4283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4285_: u8 = 0;
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4290_: u8 = 0;
    let mut v_ctor_4291_: u8 = 0;
    let mut v_interpreted_4292_: u8 = 0;
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: u8 = 0;
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: u8 = 0;
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4308_: u8 = 0;
    let mut v___x_4309_: u8 = 0;
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4317_: u8 = 0;
    let mut v_a_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4325_: u8 = 0;
    let mut v_a_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4329_: u8 = 0;
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4333_: u8 = 0;
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4343_: u8 = 0;
    let mut v_val_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4349_: u8 = 0;
    let mut v_toConstantVal_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4378_: u8 = 0;
    let mut v_fst_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4388_: u8 = 0;
    let mut v_a_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4392_: u8 = 0;
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4396_: u8 = 0;
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4405_: u8 = 0;
    let mut v_a_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4418_: u8 = 0;
    let mut v_a_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut v_a_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4435_: u8 = 0;
    let mut v___x_4436_: u8 = 0;
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4285_ = l_Lean_Expr_hasLooseBVars(v_lhs_4272_);
                if v___x_4285_ == 0 {
                    v___x_4286_ = l_Lean_Meta_Grind_getRootENode___redArg(
                        v_lhs_4272_,
                        v_a_4274_,
                        v_a_4280_,
                        v_a_4281_,
                        v_a_4282_,
                        v_a_4283_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4286_) == 0 {
                        v_a_4287_ = crate::leanh::lean_ctor_get(v___x_4286_, 0);
                        v_isSharedCheck_4427_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4286_)) as u8;
                        if v_isSharedCheck_4427_ == 0 {
                            v___x_4289_ = v___x_4286_;
                            v_isShared_4290_ = v_isSharedCheck_4427_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4287_);
                            crate::leanh::lean_dec(v___x_4286_);
                            v___x_4289_ = crate::leanh::lean_box(0);
                            v_isShared_4290_ = v_isSharedCheck_4427_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_rhs_4273_);
                        v_a_4428_ = crate::leanh::lean_ctor_get(v___x_4286_, 0);
                        v_isSharedCheck_4435_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4286_)) as u8;
                        if v_isSharedCheck_4435_ == 0 {
                            v___x_4430_ = v___x_4286_;
                            v_isShared_4431_ = v_isSharedCheck_4435_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4428_);
                            crate::leanh::lean_dec(v___x_4286_);
                            v___x_4430_ = crate::leanh::lean_box(0);
                            v_isShared_4431_ = v_isSharedCheck_4435_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_rhs_4273_);
                    crate::leanh::lean_dec_ref(v_lhs_4272_);
                    v___x_4436_ = 0;
                    v___x_4437_ = crate::leanh::lean_box((v___x_4436_) as usize);
                    v___x_4438_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4438_, 0, v___x_4437_);
                    return v___x_4438_;
                }
            }
            1 => {
                v_ctor_4291_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4287_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 2) as u32,
                );
                if v_ctor_4291_ == 0 {
                    v_interpreted_4292_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4287_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 1) as u32,
                    );
                    if v_interpreted_4292_ == 0 {
                        crate::leanh::lean_dec(v_a_4287_);
                        crate::leanh::lean_dec_ref(v_rhs_4273_);
                        v___x_4293_ = crate::leanh::lean_box((v_interpreted_4292_) as usize);
                        if v_isShared_4290_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4289_, 0, v___x_4293_);
                            v___x_4295_ = v___x_4289_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4296_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
                            v___x_4295_ = v_reuseFailAlloc_4296_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_self_4297_ = crate::leanh::lean_ctor_get(v_a_4287_, 0);
                        crate::leanh::lean_inc_ref(v_self_4297_);
                        crate::leanh::lean_dec(v_a_4287_);
                        v___x_4298_ = l_Lean_Expr_hasLooseBVars(v_rhs_4273_);
                        if v___x_4298_ == 0 {
                            crate::leanh::lean_del_object(v___x_4289_);
                            crate::leanh::lean_inc_ref(v_rhs_4273_);
                            v___x_4299_ = l_Lean_Meta_isLitValue(
                                v_rhs_4273_,
                                v_a_4280_,
                                v_a_4281_,
                                v_a_4282_,
                                v_a_4283_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4299_) == 0 {
                                v_a_4300_ = crate::leanh::lean_ctor_get(v___x_4299_, 0);
                                crate::leanh::lean_inc(v_a_4300_);
                                v___x_4301_ = (crate::leanh::lean_unbox(v_a_4300_) as u8);
                                if v___x_4301_ == 0 {
                                    crate::leanh::lean_dec(v_a_4300_);
                                    crate::leanh::lean_dec_ref(v_self_4297_);
                                    crate::leanh::lean_dec_ref(v_rhs_4273_);
                                    return v___x_4299_;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_4299_, 1);
                                    v___x_4302_ = l_Lean_Meta_normLitValue(
                                        v_self_4297_,
                                        v_a_4280_,
                                        v_a_4281_,
                                        v_a_4282_,
                                        v_a_4283_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4302_) == 0 {
                                        v_a_4303_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                                        crate::leanh::lean_inc(v_a_4303_);
                                        crate::leanh::lean_dec_ref_known(v___x_4302_, 1);
                                        v___x_4304_ = l_Lean_Meta_normLitValue(
                                            v_rhs_4273_,
                                            v_a_4280_,
                                            v_a_4281_,
                                            v_a_4282_,
                                            v_a_4283_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_4304_) == 0 {
                                            v_a_4305_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                                            v_isSharedCheck_4317_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4304_))
                                                    as u8;
                                            if v_isSharedCheck_4317_ == 0 {
                                                v___x_4307_ = v___x_4304_;
                                                v_isShared_4308_ = v_isSharedCheck_4317_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4305_);
                                                crate::leanh::lean_dec(v___x_4304_);
                                                v___x_4307_ = crate::leanh::lean_box(0);
                                                v_isShared_4308_ = v_isSharedCheck_4317_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_4303_);
                                            crate::leanh::lean_dec(v_a_4300_);
                                            v_a_4318_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                                            v_isSharedCheck_4325_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4304_))
                                                    as u8;
                                            if v_isSharedCheck_4325_ == 0 {
                                                v___x_4320_ = v___x_4304_;
                                                v_isShared_4321_ = v_isSharedCheck_4325_;
                                                state = 6;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4318_);
                                                crate::leanh::lean_dec(v___x_4304_);
                                                v___x_4320_ = crate::leanh::lean_box(0);
                                                v_isShared_4321_ = v_isSharedCheck_4325_;
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_4300_);
                                        crate::leanh::lean_dec_ref(v_rhs_4273_);
                                        v_a_4326_ = crate::leanh::lean_ctor_get(v___x_4302_, 0);
                                        v_isSharedCheck_4333_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4302_)) as u8;
                                        if v_isSharedCheck_4333_ == 0 {
                                            v___x_4328_ = v___x_4302_;
                                            v_isShared_4329_ = v_isSharedCheck_4333_;
                                            state = 8;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4326_);
                                            crate::leanh::lean_dec(v___x_4302_);
                                            v___x_4328_ = crate::leanh::lean_box(0);
                                            v_isShared_4329_ = v_isSharedCheck_4333_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_self_4297_);
                                crate::leanh::lean_dec_ref(v_rhs_4273_);
                                return v___x_4299_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_self_4297_);
                            crate::leanh::lean_dec_ref(v_rhs_4273_);
                            v___x_4334_ = crate::leanh::lean_box((v_ctor_4291_) as usize);
                            if v_isShared_4290_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4289_, 0, v___x_4334_);
                                v___x_4336_ = v___x_4289_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4337_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
                                v___x_4336_ = v_reuseFailAlloc_4337_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4289_);
                    v_self_4338_ = crate::leanh::lean_ctor_get(v_a_4287_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_4338_, 2);
                    crate::leanh::lean_dec(v_a_4287_);
                    v___x_4339_ = l_Lean_Meta_isConstructorApp_x3f(
                        v_self_4338_,
                        v_a_4280_,
                        v_a_4281_,
                        v_a_4282_,
                        v_a_4283_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4339_) == 0 {
                        v_a_4340_ = crate::leanh::lean_ctor_get(v___x_4339_, 0);
                        v_isSharedCheck_4418_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4339_)) as u8;
                        if v_isSharedCheck_4418_ == 0 {
                            v___x_4342_ = v___x_4339_;
                            v_isShared_4343_ = v_isSharedCheck_4418_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4340_);
                            crate::leanh::lean_dec(v___x_4339_);
                            v___x_4342_ = crate::leanh::lean_box(0);
                            v_isShared_4343_ = v_isSharedCheck_4418_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_self_4338_);
                        crate::leanh::lean_dec_ref(v_rhs_4273_);
                        v_a_4419_ = crate::leanh::lean_ctor_get(v___x_4339_, 0);
                        v_isSharedCheck_4426_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4339_)) as u8;
                        if v_isSharedCheck_4426_ == 0 {
                            v___x_4421_ = v___x_4339_;
                            v_isShared_4422_ = v_isSharedCheck_4426_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4419_);
                            crate::leanh::lean_dec(v___x_4339_);
                            v___x_4421_ = crate::leanh::lean_box(0);
                            v_isShared_4422_ = v_isSharedCheck_4426_;
                            state = 24;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4295_;
            }
            3 => {
                v___x_4309_ = lean_expr_eqv(v_a_4303_, v_a_4305_);
                crate::leanh::lean_dec(v_a_4305_);
                crate::leanh::lean_dec(v_a_4303_);
                if v___x_4309_ == 0 {
                    if v_isShared_4308_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4307_, 0, v_a_4300_);
                        v___x_4311_ = v___x_4307_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4300_);
                        v___x_4311_ = v_reuseFailAlloc_4312_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4300_);
                    v___x_4313_ = crate::leanh::lean_box((v___x_4298_) as usize);
                    if v_isShared_4308_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4307_, 0, v___x_4313_);
                        v___x_4315_ = v___x_4307_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4316_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4313_);
                        v___x_4315_ = v_reuseFailAlloc_4316_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4311_;
            }
            5 => {
                return v___x_4315_;
            }
            6 => {
                if v_isShared_4321_ == 0 {
                    v___x_4323_ = v___x_4320_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
                    v___x_4323_ = v_reuseFailAlloc_4324_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4323_;
            }
            8 => {
                if v_isShared_4329_ == 0 {
                    v___x_4331_ = v___x_4328_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
                    v___x_4331_ = v_reuseFailAlloc_4332_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4331_;
            }
            10 => {
                return v___x_4336_;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v_a_4340_) == 1 {
                    crate::leanh::lean_del_object(v___x_4342_);
                    v_val_4344_ = crate::leanh::lean_ctor_get(v_a_4340_, 0);
                    crate::leanh::lean_inc(v_val_4344_);
                    crate::leanh::lean_dec_ref_known(v_a_4340_, 1);
                    crate::leanh::lean_inc_ref(v_rhs_4273_);
                    v___x_4345_ = l_Lean_Meta_isConstructorApp_x3f(
                        v_rhs_4273_,
                        v_a_4280_,
                        v_a_4281_,
                        v_a_4282_,
                        v_a_4283_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4345_) == 0 {
                        v_a_4346_ = crate::leanh::lean_ctor_get(v___x_4345_, 0);
                        v_isSharedCheck_4405_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4345_)) as u8;
                        if v_isSharedCheck_4405_ == 0 {
                            v___x_4348_ = v___x_4345_;
                            v_isShared_4349_ = v_isSharedCheck_4405_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4346_);
                            crate::leanh::lean_dec(v___x_4345_);
                            v___x_4348_ = crate::leanh::lean_box(0);
                            v_isShared_4349_ = v_isSharedCheck_4405_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4344_);
                        crate::leanh::lean_dec_ref(v_self_4338_);
                        crate::leanh::lean_dec_ref(v_rhs_4273_);
                        v_a_4406_ = crate::leanh::lean_ctor_get(v___x_4345_, 0);
                        v_isSharedCheck_4413_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4345_)) as u8;
                        if v_isSharedCheck_4413_ == 0 {
                            v___x_4408_ = v___x_4345_;
                            v_isShared_4409_ = v_isSharedCheck_4413_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4406_);
                            crate::leanh::lean_dec(v___x_4345_);
                            v___x_4408_ = crate::leanh::lean_box(0);
                            v_isShared_4409_ = v_isSharedCheck_4413_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4340_);
                    crate::leanh::lean_dec_ref(v_self_4338_);
                    crate::leanh::lean_dec_ref(v_rhs_4273_);
                    v___x_4414_ = crate::leanh::lean_box((v___x_4285_) as usize);
                    if v_isShared_4343_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4342_, 0, v___x_4414_);
                        v___x_4416_ = v___x_4342_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_4417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4414_);
                        v___x_4416_ = v_reuseFailAlloc_4417_;
                        state = 23;
                        continue;
                    }
                }
            }
            12 => {
                if crate::leanh::lean_obj_tag(v_a_4346_) == 1 {
                    v_toConstantVal_4350_ = crate::leanh::lean_ctor_get(v_val_4344_, 0);
                    crate::leanh::lean_inc_ref(v_toConstantVal_4350_);
                    v_val_4351_ = crate::leanh::lean_ctor_get(v_a_4346_, 0);
                    crate::leanh::lean_inc(v_val_4351_);
                    crate::leanh::lean_dec_ref_known(v_a_4346_, 1);
                    v_toConstantVal_4352_ = crate::leanh::lean_ctor_get(v_val_4351_, 0);
                    crate::leanh::lean_inc_ref(v_toConstantVal_4352_);
                    crate::leanh::lean_dec(v_val_4351_);
                    v_numParams_4353_ = crate::leanh::lean_ctor_get(v_val_4344_, 3);
                    crate::leanh::lean_inc(v_numParams_4353_);
                    v_numFields_4354_ = crate::leanh::lean_ctor_get(v_val_4344_, 4);
                    crate::leanh::lean_inc(v_numFields_4354_);
                    crate::leanh::lean_dec(v_val_4344_);
                    v_name_4355_ = crate::leanh::lean_ctor_get(v_toConstantVal_4350_, 0);
                    crate::leanh::lean_inc(v_name_4355_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_4350_);
                    v_name_4356_ = crate::leanh::lean_ctor_get(v_toConstantVal_4352_, 0);
                    crate::leanh::lean_inc(v_name_4356_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_4352_);
                    v___x_4357_ = lean_name_eq(v_name_4355_, v_name_4356_);
                    crate::leanh::lean_dec(v_name_4356_);
                    crate::leanh::lean_dec(v_name_4355_);
                    if v___x_4357_ == 0 {
                        crate::leanh::lean_dec(v_numFields_4354_);
                        crate::leanh::lean_dec(v_numParams_4353_);
                        crate::leanh::lean_dec_ref(v_self_4338_);
                        crate::leanh::lean_dec_ref(v_rhs_4273_);
                        v___x_4358_ = crate::leanh::lean_box((v_ctor_4291_) as usize);
                        if v_isShared_4349_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4348_, 0, v___x_4358_);
                            v___x_4360_ = v___x_4348_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_4361_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
                            v___x_4360_ = v_reuseFailAlloc_4361_;
                            state = 13;
                            continue;
                        }
                    } else {
                        if v___x_4285_ == 0 {
                            crate::leanh::lean_del_object(v___x_4348_);
                            v_nargs_4362_ = l_Lean_Expr_getAppNumArgs(v_self_4338_);
                            v_nargs_4363_ = l_Lean_Expr_getAppNumArgs(v_rhs_4273_);
                            v___x_4364_ = lean_nat_add(v_numParams_4353_, v_numFields_4354_);
                            crate::leanh::lean_dec(v_numFields_4354_);
                            v___x_4365_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0;
                            v_dummy_4366_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
                            crate::leanh::lean_inc(v_nargs_4362_);
                            v___x_4367_ = lean_mk_array(v_nargs_4362_, v_dummy_4366_);
                            v___x_4368_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4369_ = lean_nat_sub(v_nargs_4362_, v___x_4368_);
                            crate::leanh::lean_dec(v_nargs_4362_);
                            v___x_4370_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_self_4338_,
                                v___x_4367_,
                                v___x_4369_,
                            );
                            crate::leanh::lean_inc(v_nargs_4363_);
                            v___x_4371_ = lean_mk_array(v_nargs_4363_, v_dummy_4366_);
                            v___x_4372_ = lean_nat_sub(v_nargs_4363_, v___x_4368_);
                            crate::leanh::lean_dec(v_nargs_4363_);
                            v___x_4373_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_rhs_4273_,
                                v___x_4371_,
                                v___x_4372_,
                            );
                            v___x_4374_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v___x_4364_, v___x_4370_, v___x_4373_, v_ctor_4291_, v_numParams_4353_, v___x_4365_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
                            crate::leanh::lean_dec_ref(v___x_4373_);
                            crate::leanh::lean_dec_ref(v___x_4370_);
                            crate::leanh::lean_dec(v___x_4364_);
                            if crate::leanh::lean_obj_tag(v___x_4374_) == 0 {
                                v_a_4375_ = crate::leanh::lean_ctor_get(v___x_4374_, 0);
                                v_isSharedCheck_4388_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4374_)) as u8;
                                if v_isSharedCheck_4388_ == 0 {
                                    v___x_4377_ = v___x_4374_;
                                    v_isShared_4378_ = v_isSharedCheck_4388_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4375_);
                                    crate::leanh::lean_dec(v___x_4374_);
                                    v___x_4377_ = crate::leanh::lean_box(0);
                                    v_isShared_4378_ = v_isSharedCheck_4388_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                v_a_4389_ = crate::leanh::lean_ctor_get(v___x_4374_, 0);
                                v_isSharedCheck_4396_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4374_)) as u8;
                                if v_isSharedCheck_4396_ == 0 {
                                    v___x_4391_ = v___x_4374_;
                                    v_isShared_4392_ = v_isSharedCheck_4396_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4389_);
                                    crate::leanh::lean_dec(v___x_4374_);
                                    v___x_4391_ = crate::leanh::lean_box(0);
                                    v_isShared_4392_ = v_isSharedCheck_4396_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_numFields_4354_);
                            crate::leanh::lean_dec(v_numParams_4353_);
                            crate::leanh::lean_dec_ref(v_self_4338_);
                            crate::leanh::lean_dec_ref(v_rhs_4273_);
                            v___x_4397_ = crate::leanh::lean_box((v_ctor_4291_) as usize);
                            if v_isShared_4349_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4348_, 0, v___x_4397_);
                                v___x_4399_ = v___x_4348_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_4400_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 0, v___x_4397_);
                                v___x_4399_ = v_reuseFailAlloc_4400_;
                                state = 19;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4346_);
                    crate::leanh::lean_dec(v_val_4344_);
                    crate::leanh::lean_dec_ref(v_self_4338_);
                    crate::leanh::lean_dec_ref(v_rhs_4273_);
                    v___x_4401_ = crate::leanh::lean_box((v___x_4285_) as usize);
                    if v_isShared_4349_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4348_, 0, v___x_4401_);
                        v___x_4403_ = v___x_4348_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_4404_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4401_);
                        v___x_4403_ = v_reuseFailAlloc_4404_;
                        state = 20;
                        continue;
                    }
                }
            }
            13 => {
                return v___x_4360_;
            }
            14 => {
                v_fst_4379_ = crate::leanh::lean_ctor_get(v_a_4375_, 0);
                crate::leanh::lean_inc(v_fst_4379_);
                crate::leanh::lean_dec(v_a_4375_);
                if crate::leanh::lean_obj_tag(v_fst_4379_) == 0 {
                    v___x_4380_ = crate::leanh::lean_box((v___x_4285_) as usize);
                    if v_isShared_4378_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4377_, 0, v___x_4380_);
                        v___x_4382_ = v___x_4377_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_4383_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4380_);
                        v___x_4382_ = v_reuseFailAlloc_4383_;
                        state = 15;
                        continue;
                    }
                } else {
                    v_val_4384_ = crate::leanh::lean_ctor_get(v_fst_4379_, 0);
                    crate::leanh::lean_inc(v_val_4384_);
                    crate::leanh::lean_dec_ref_known(v_fst_4379_, 1);
                    if v_isShared_4378_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4377_, 0, v_val_4384_);
                        v___x_4386_ = v___x_4377_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_4387_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_val_4384_);
                        v___x_4386_ = v_reuseFailAlloc_4387_;
                        state = 16;
                        continue;
                    }
                }
            }
            15 => {
                return v___x_4382_;
            }
            16 => {
                return v___x_4386_;
            }
            17 => {
                if v_isShared_4392_ == 0 {
                    v___x_4394_ = v___x_4391_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
                    v___x_4394_ = v_reuseFailAlloc_4395_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4394_;
            }
            19 => {
                return v___x_4399_;
            }
            20 => {
                return v___x_4403_;
            }
            21 => {
                if v_isShared_4409_ == 0 {
                    v___x_4411_ = v___x_4408_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
                    v___x_4411_ = v_reuseFailAlloc_4412_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4411_;
            }
            23 => {
                return v___x_4416_;
            }
            24 => {
                if v_isShared_4422_ == 0 {
                    v___x_4424_ = v___x_4421_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
                    v___x_4424_ = v_reuseFailAlloc_4425_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4424_;
            }
            26 => {
                if v_isShared_4431_ == 0 {
                    v___x_4433_ = v___x_4430_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
                    v___x_4433_ = v_reuseFailAlloc_4434_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(
    mut v_upperBound_4439_: *mut crate::leanh::LeanObject,
    mut v___x_4440_: *mut crate::leanh::LeanObject,
    mut v___x_4441_: *mut crate::leanh::LeanObject,
    mut v___x_4442_: u8,
    mut v_a_4443_: *mut crate::leanh::LeanObject,
    mut v_b_4444_: *mut crate::leanh::LeanObject,
    mut v___y_4445_: *mut crate::leanh::LeanObject,
    mut v___y_4446_: *mut crate::leanh::LeanObject,
    mut v___y_4447_: *mut crate::leanh::LeanObject,
    mut v___y_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
    mut v___y_4450_: *mut crate::leanh::LeanObject,
    mut v___y_4451_: *mut crate::leanh::LeanObject,
    mut v___y_4452_: *mut crate::leanh::LeanObject,
    mut v___y_4453_: *mut crate::leanh::LeanObject,
    mut v___y_4454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4456_: u8 = 0;
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4465_: u8 = 0;
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: u8 = 0;
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_a_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4482_: u8 = 0;
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4456_ = lean_nat_dec_lt(v_a_4443_, v_upperBound_4439_);
                if v___x_4456_ == 0 {
                    crate::leanh::lean_dec(v_a_4443_);
                    v___x_4457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4457_, 0, v_b_4444_);
                    return v___x_4457_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_4444_);
                    v___x_4458_ = l_Lean_instInhabitedExpr;
                    v___x_4459_ = lean_array_get_borrowed(v___x_4458_, v___x_4440_, v_a_4443_);
                    v___x_4460_ = lean_array_get_borrowed(v___x_4458_, v___x_4441_, v_a_4443_);
                    crate::leanh::lean_inc(v___x_4460_);
                    crate::leanh::lean_inc(v___x_4459_);
                    v___x_4461_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v___x_4459_, v___x_4460_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
                    if crate::leanh::lean_obj_tag(v___x_4461_) == 0 {
                        v_a_4462_ = crate::leanh::lean_ctor_get(v___x_4461_, 0);
                        v_isSharedCheck_4478_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4461_)) as u8;
                        if v_isSharedCheck_4478_ == 0 {
                            v___x_4464_ = v___x_4461_;
                            v_isShared_4465_ = v_isSharedCheck_4478_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4462_);
                            crate::leanh::lean_dec(v___x_4461_);
                            v___x_4464_ = crate::leanh::lean_box(0);
                            v_isShared_4465_ = v_isSharedCheck_4478_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4443_);
                        v_a_4479_ = crate::leanh::lean_ctor_get(v___x_4461_, 0);
                        v_isSharedCheck_4486_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4461_)) as u8;
                        if v_isSharedCheck_4486_ == 0 {
                            v___x_4481_ = v___x_4461_;
                            v_isShared_4482_ = v_isSharedCheck_4486_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4479_);
                            crate::leanh::lean_dec(v___x_4461_);
                            v___x_4481_ = crate::leanh::lean_box(0);
                            v_isShared_4482_ = v_isSharedCheck_4486_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4466_ = crate::leanh::lean_box(0);
                v___x_4467_ = (crate::leanh::lean_unbox(v_a_4462_) as u8);
                crate::leanh::lean_dec(v_a_4462_);
                if v___x_4467_ == 0 {
                    crate::leanh::lean_del_object(v___x_4464_);
                    v___x_4468_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___closed__0;
                    v___x_4469_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4470_ = lean_nat_add(v_a_4443_, v___x_4469_);
                    crate::leanh::lean_dec(v_a_4443_);
                    v_a_4443_ = v___x_4470_;
                    v_b_4444_ = v___x_4468_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_4443_);
                    v___x_4472_ = crate::leanh::lean_box((v___x_4442_) as usize);
                    v___x_4473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4473_, 0, v___x_4472_);
                    v___x_4474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4474_, 0, v___x_4473_);
                    crate::leanh::lean_ctor_set(v___x_4474_, 1, v___x_4466_);
                    if v_isShared_4465_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4464_, 0, v___x_4474_);
                        v___x_4476_ = v___x_4464_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4474_);
                        v___x_4476_ = v_reuseFailAlloc_4477_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4476_;
            }
            3 => {
                if v_isShared_4482_ == 0 {
                    v___x_4484_ = v___x_4481_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4479_);
                    v___x_4484_ = v_reuseFailAlloc_4485_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_4487_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_4488_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_4489_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_4490_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_4491_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_4492_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4493_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4494_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4495_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4496_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4497_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4498_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4499_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4500_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4501_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4502_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4503_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_28909__boxed_4504_: u8 = 0;
    let mut v_res_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_28909__boxed_4504_ = (crate::leanh::lean_unbox(v___x_4490_) as u8);
    v_res_4505_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_4487_, v___x_4488_, v___x_4489_, v___x_28909__boxed_4504_, v_a_4491_, v_b_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
    crate::leanh::lean_dec(v___y_4502_);
    crate::leanh::lean_dec_ref(v___y_4501_);
    crate::leanh::lean_dec(v___y_4500_);
    crate::leanh::lean_dec_ref(v___y_4499_);
    crate::leanh::lean_dec(v___y_4498_);
    crate::leanh::lean_dec_ref(v___y_4497_);
    crate::leanh::lean_dec(v___y_4496_);
    crate::leanh::lean_dec_ref(v___y_4495_);
    crate::leanh::lean_dec(v___y_4494_);
    crate::leanh::lean_dec(v___y_4493_);
    crate::leanh::lean_dec_ref(v___x_4489_);
    crate::leanh::lean_dec_ref(v___x_4488_);
    crate::leanh::lean_dec(v_upperBound_4487_);
    return v_res_4505_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(
    mut v_lhs_4506_: *mut crate::leanh::LeanObject,
    mut v_rhs_4507_: *mut crate::leanh::LeanObject,
    mut v_a_4508_: *mut crate::leanh::LeanObject,
    mut v_a_4509_: *mut crate::leanh::LeanObject,
    mut v_a_4510_: *mut crate::leanh::LeanObject,
    mut v_a_4511_: *mut crate::leanh::LeanObject,
    mut v_a_4512_: *mut crate::leanh::LeanObject,
    mut v_a_4513_: *mut crate::leanh::LeanObject,
    mut v_a_4514_: *mut crate::leanh::LeanObject,
    mut v_a_4515_: *mut crate::leanh::LeanObject,
    mut v_a_4516_: *mut crate::leanh::LeanObject,
    mut v_a_4517_: *mut crate::leanh::LeanObject,
    mut v_a_4518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4519_ =
        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(
            v_lhs_4506_,
            v_rhs_4507_,
            v_a_4508_,
            v_a_4509_,
            v_a_4510_,
            v_a_4511_,
            v_a_4512_,
            v_a_4513_,
            v_a_4514_,
            v_a_4515_,
            v_a_4516_,
            v_a_4517_,
        );
    crate::leanh::lean_dec(v_a_4517_);
    crate::leanh::lean_dec_ref(v_a_4516_);
    crate::leanh::lean_dec(v_a_4515_);
    crate::leanh::lean_dec_ref(v_a_4514_);
    crate::leanh::lean_dec(v_a_4513_);
    crate::leanh::lean_dec_ref(v_a_4512_);
    crate::leanh::lean_dec(v_a_4511_);
    crate::leanh::lean_dec_ref(v_a_4510_);
    crate::leanh::lean_dec(v_a_4509_);
    crate::leanh::lean_dec(v_a_4508_);
    return v_res_4519_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(
    mut v_upperBound_4520_: *mut crate::leanh::LeanObject,
    mut v___x_4521_: *mut crate::leanh::LeanObject,
    mut v___x_4522_: *mut crate::leanh::LeanObject,
    mut v___x_4523_: u8,
    mut v_inst_4524_: *mut crate::leanh::LeanObject,
    mut v_R_4525_: *mut crate::leanh::LeanObject,
    mut v_a_4526_: *mut crate::leanh::LeanObject,
    mut v_b_4527_: *mut crate::leanh::LeanObject,
    mut v_c_4528_: *mut crate::leanh::LeanObject,
    mut v___y_4529_: *mut crate::leanh::LeanObject,
    mut v___y_4530_: *mut crate::leanh::LeanObject,
    mut v___y_4531_: *mut crate::leanh::LeanObject,
    mut v___y_4532_: *mut crate::leanh::LeanObject,
    mut v___y_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
    mut v___y_4538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4540_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(v_upperBound_4520_, v___x_4521_, v___x_4522_, v___x_4523_, v_a_4526_, v_b_4527_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
    return v___x_4540_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_4541_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_4542_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_4543_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_4544_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_inst_4545_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_R_4546_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_4547_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_b_4548_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_c_4549_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4550_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4551_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4552_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4553_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4554_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4555_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4556_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4557_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4558_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4559_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_4560_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___x_29305__boxed_4561_: u8 = 0;
    let mut v_res_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_29305__boxed_4561_ = (crate::leanh::lean_unbox(v___x_4544_) as u8);
    v_res_4562_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(v_upperBound_4541_, v___x_4542_, v___x_4543_, v___x_29305__boxed_4561_, v_inst_4545_, v_R_4546_, v_a_4547_, v_b_4548_, v_c_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
    crate::leanh::lean_dec(v___y_4559_);
    crate::leanh::lean_dec_ref(v___y_4558_);
    crate::leanh::lean_dec(v___y_4557_);
    crate::leanh::lean_dec_ref(v___y_4556_);
    crate::leanh::lean_dec(v___y_4555_);
    crate::leanh::lean_dec_ref(v___y_4554_);
    crate::leanh::lean_dec(v___y_4553_);
    crate::leanh::lean_dec_ref(v___y_4552_);
    crate::leanh::lean_dec(v___y_4551_);
    crate::leanh::lean_dec(v___y_4550_);
    crate::leanh::lean_dec_ref(v___x_4543_);
    crate::leanh::lean_dec_ref(v___x_4542_);
    crate::leanh::lean_dec(v_upperBound_4541_);
    return v_res_4562_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(
    mut v_e_4563_: *mut crate::leanh::LeanObject,
    mut v_a_4564_: *mut crate::leanh::LeanObject,
    mut v_a_4565_: *mut crate::leanh::LeanObject,
    mut v_a_4566_: *mut crate::leanh::LeanObject,
    mut v_a_4567_: *mut crate::leanh::LeanObject,
    mut v_a_4568_: *mut crate::leanh::LeanObject,
    mut v_a_4569_: *mut crate::leanh::LeanObject,
    mut v_a_4570_: *mut crate::leanh::LeanObject,
    mut v_a_4571_: *mut crate::leanh::LeanObject,
    mut v_a_4572_: *mut crate::leanh::LeanObject,
    mut v_a_4573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4575_ =
        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(v_e_4563_);
    if crate::leanh::lean_obj_tag(v___x_4575_) == 1 {
        let mut v_val_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4576_ = crate::leanh::lean_ctor_get(v___x_4575_, 0);
        crate::leanh::lean_inc(v_val_4576_);
        crate::leanh::lean_dec_ref_known(v___x_4575_, 1);
        v_snd_4577_ = crate::leanh::lean_ctor_get(v_val_4576_, 1);
        crate::leanh::lean_inc(v_snd_4577_);
        crate::leanh::lean_dec(v_val_4576_);
        v_fst_4578_ = crate::leanh::lean_ctor_get(v_snd_4577_, 0);
        crate::leanh::lean_inc(v_fst_4578_);
        v_snd_4579_ = crate::leanh::lean_ctor_get(v_snd_4577_, 1);
        crate::leanh::lean_inc(v_snd_4579_);
        crate::leanh::lean_dec(v_snd_4577_);
        v___x_4580_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(v_fst_4578_, v_snd_4579_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_);
        return v___x_4580_;
    } else {
        let mut v___x_4581_: u8 = 0;
        let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_4575_);
        v___x_4581_ = 0;
        v___x_4582_ = crate::leanh::lean_box((v___x_4581_) as usize);
        v___x_4583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4583_, 0, v___x_4582_);
        return v___x_4583_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(
    mut v_e_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
    mut v_a_4586_: *mut crate::leanh::LeanObject,
    mut v_a_4587_: *mut crate::leanh::LeanObject,
    mut v_a_4588_: *mut crate::leanh::LeanObject,
    mut v_a_4589_: *mut crate::leanh::LeanObject,
    mut v_a_4590_: *mut crate::leanh::LeanObject,
    mut v_a_4591_: *mut crate::leanh::LeanObject,
    mut v_a_4592_: *mut crate::leanh::LeanObject,
    mut v_a_4593_: *mut crate::leanh::LeanObject,
    mut v_a_4594_: *mut crate::leanh::LeanObject,
    mut v_a_4595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4596_ =
        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(
            v_e_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_,
            v_a_4592_, v_a_4593_, v_a_4594_,
        );
    crate::leanh::lean_dec(v_a_4594_);
    crate::leanh::lean_dec_ref(v_a_4593_);
    crate::leanh::lean_dec(v_a_4592_);
    crate::leanh::lean_dec_ref(v_a_4591_);
    crate::leanh::lean_dec(v_a_4590_);
    crate::leanh::lean_dec_ref(v_a_4589_);
    crate::leanh::lean_dec(v_a_4588_);
    crate::leanh::lean_dec_ref(v_a_4587_);
    crate::leanh::lean_dec(v_a_4586_);
    crate::leanh::lean_dec(v_a_4585_);
    return v_res_4596_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(
    mut v___x_4597_: u8,
    mut v_snd_4598_: *mut crate::leanh::LeanObject,
    mut v_____r_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
    mut v___y_4601_: *mut crate::leanh::LeanObject,
    mut v___y_4602_: *mut crate::leanh::LeanObject,
    mut v___y_4603_: *mut crate::leanh::LeanObject,
    mut v___y_4604_: *mut crate::leanh::LeanObject,
    mut v___y_4605_: *mut crate::leanh::LeanObject,
    mut v___y_4606_: *mut crate::leanh::LeanObject,
    mut v___y_4607_: *mut crate::leanh::LeanObject,
    mut v___y_4608_: *mut crate::leanh::LeanObject,
    mut v___y_4609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4611_ = crate::leanh::lean_box((v___x_4597_) as usize);
    v___x_4612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4612_, 0, v___x_4611_);
    v___x_4613_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4613_, 0, v___x_4612_);
    crate::leanh::lean_ctor_set(v___x_4613_, 1, v_snd_4598_);
    v___x_4614_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4614_, 0, v___x_4613_);
    v___x_4615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4615_, 0, v___x_4614_);
    return v___x_4615_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0___boxed(
    mut v___x_4616_: *mut crate::leanh::LeanObject,
    mut v_snd_4617_: *mut crate::leanh::LeanObject,
    mut v_____r_4618_: *mut crate::leanh::LeanObject,
    mut v___y_4619_: *mut crate::leanh::LeanObject,
    mut v___y_4620_: *mut crate::leanh::LeanObject,
    mut v___y_4621_: *mut crate::leanh::LeanObject,
    mut v___y_4622_: *mut crate::leanh::LeanObject,
    mut v___y_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_32248__boxed_4630_: u8 = 0;
    let mut v_res_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_32248__boxed_4630_ = (crate::leanh::lean_unbox(v___x_4616_) as u8);
    v_res_4631_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_32248__boxed_4630_, v_snd_4617_, v_____r_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
    crate::leanh::lean_dec(v___y_4628_);
    crate::leanh::lean_dec_ref(v___y_4627_);
    crate::leanh::lean_dec(v___y_4626_);
    crate::leanh::lean_dec_ref(v___y_4625_);
    crate::leanh::lean_dec(v___y_4624_);
    crate::leanh::lean_dec_ref(v___y_4623_);
    crate::leanh::lean_dec(v___y_4622_);
    crate::leanh::lean_dec_ref(v___y_4621_);
    crate::leanh::lean_dec(v___y_4620_);
    crate::leanh::lean_dec(v___y_4619_);
    return v_res_4631_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(
    mut v_msgData_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4638_ = lean_st_ref_get(v___y_4636_);
    v_env_4639_ = crate::leanh::lean_ctor_get(v___x_4638_, 0);
    crate::leanh::lean_inc_ref(v_env_4639_);
    crate::leanh::lean_dec(v___x_4638_);
    v___x_4640_ = lean_st_ref_get(v___y_4634_);
    v_mctx_4641_ = crate::leanh::lean_ctor_get(v___x_4640_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4641_);
    crate::leanh::lean_dec(v___x_4640_);
    v_lctx_4642_ = crate::leanh::lean_ctor_get(v___y_4633_, 2);
    v_options_4643_ = crate::leanh::lean_ctor_get(v___y_4635_, 2);
    crate::leanh::lean_inc_ref(v_options_4643_);
    crate::leanh::lean_inc_ref(v_lctx_4642_);
    v___x_4644_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4644_, 0, v_env_4639_);
    crate::leanh::lean_ctor_set(v___x_4644_, 1, v_mctx_4641_);
    crate::leanh::lean_ctor_set(v___x_4644_, 2, v_lctx_4642_);
    crate::leanh::lean_ctor_set(v___x_4644_, 3, v_options_4643_);
    v___x_4645_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4645_, 0, v___x_4644_);
    crate::leanh::lean_ctor_set(v___x_4645_, 1, v_msgData_4632_);
    v___x_4646_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4646_, 0, v___x_4645_);
    return v___x_4646_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0___boxed(
    mut v_msgData_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msgData_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
    crate::leanh::lean_dec(v___y_4651_);
    crate::leanh::lean_dec_ref(v___y_4650_);
    crate::leanh::lean_dec(v___y_4649_);
    crate::leanh::lean_dec_ref(v___y_4648_);
    return v_res_4653_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: f64 = 0.0;
    v___x_4654_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4655_ = lean_float_of_nat(v___x_4654_);
    return v___x_4655_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(
    mut v_cls_4659_: *mut crate::leanh::LeanObject,
    mut v_msg_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
    mut v___y_4662_: *mut crate::leanh::LeanObject,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4671_: u8 = 0;
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4684_: u8 = 0;
    let mut v_tid_4685_: u64 = 0;
    let mut v_traces_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4689_: u8 = 0;
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: f64 = 0.0;
    let mut v___x_4692_: u8 = 0;
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4710_: u8 = 0;
    let mut v_isSharedCheck_4711_: u8 = 0;
    let mut v_isSharedCheck_4712_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4666_ = crate::leanh::lean_ctor_get(v___y_4663_, 5);
                v___x_4667_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0_spec__0(v_msg_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
                v_a_4668_ = crate::leanh::lean_ctor_get(v___x_4667_, 0);
                v_isSharedCheck_4712_ = (!crate::leanh::lean_is_exclusive(v___x_4667_)) as u8;
                if v_isSharedCheck_4712_ == 0 {
                    v___x_4670_ = v___x_4667_;
                    v_isShared_4671_ = v_isSharedCheck_4712_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4668_);
                    crate::leanh::lean_dec(v___x_4667_);
                    v___x_4670_ = crate::leanh::lean_box(0);
                    v_isShared_4671_ = v_isSharedCheck_4712_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4672_ = lean_st_ref_take(v___y_4664_);
                v_traceState_4673_ = crate::leanh::lean_ctor_get(v___x_4672_, 4);
                v_env_4674_ = crate::leanh::lean_ctor_get(v___x_4672_, 0);
                v_nextMacroScope_4675_ = crate::leanh::lean_ctor_get(v___x_4672_, 1);
                v_ngen_4676_ = crate::leanh::lean_ctor_get(v___x_4672_, 2);
                v_auxDeclNGen_4677_ = crate::leanh::lean_ctor_get(v___x_4672_, 3);
                v_cache_4678_ = crate::leanh::lean_ctor_get(v___x_4672_, 5);
                v_messages_4679_ = crate::leanh::lean_ctor_get(v___x_4672_, 6);
                v_infoState_4680_ = crate::leanh::lean_ctor_get(v___x_4672_, 7);
                v_snapshotTasks_4681_ = crate::leanh::lean_ctor_get(v___x_4672_, 8);
                v_isSharedCheck_4711_ = (!crate::leanh::lean_is_exclusive(v___x_4672_)) as u8;
                if v_isSharedCheck_4711_ == 0 {
                    v___x_4683_ = v___x_4672_;
                    v_isShared_4684_ = v_isSharedCheck_4711_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4681_);
                    crate::leanh::lean_inc(v_infoState_4680_);
                    crate::leanh::lean_inc(v_messages_4679_);
                    crate::leanh::lean_inc(v_cache_4678_);
                    crate::leanh::lean_inc(v_traceState_4673_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4677_);
                    crate::leanh::lean_inc(v_ngen_4676_);
                    crate::leanh::lean_inc(v_nextMacroScope_4675_);
                    crate::leanh::lean_inc(v_env_4674_);
                    crate::leanh::lean_dec(v___x_4672_);
                    v___x_4683_ = crate::leanh::lean_box(0);
                    v_isShared_4684_ = v_isSharedCheck_4711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4685_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4673_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4686_ = crate::leanh::lean_ctor_get(v_traceState_4673_, 0);
                v_isSharedCheck_4710_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4673_)) as u8;
                if v_isSharedCheck_4710_ == 0 {
                    v___x_4688_ = v_traceState_4673_;
                    v_isShared_4689_ = v_isSharedCheck_4710_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4686_);
                    crate::leanh::lean_dec(v_traceState_4673_);
                    v___x_4688_ = crate::leanh::lean_box(0);
                    v_isShared_4689_ = v_isSharedCheck_4710_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4690_ = crate::leanh::lean_box(0);
                v___x_4691_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0);
                v___x_4692_ = 0;
                v___x_4693_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1;
                v___x_4694_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4694_, 0, v_cls_4659_);
                crate::leanh::lean_ctor_set(v___x_4694_, 1, v___x_4690_);
                crate::leanh::lean_ctor_set(v___x_4694_, 2, v___x_4693_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4694_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4691_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4694_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4691_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4694_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4692_,
                );
                v___x_4695_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__2;
                v___x_4696_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4696_, 0, v___x_4694_);
                crate::leanh::lean_ctor_set(v___x_4696_, 1, v_a_4668_);
                crate::leanh::lean_ctor_set(v___x_4696_, 2, v___x_4695_);
                crate::leanh::lean_inc(v_ref_4666_);
                v___x_4697_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4697_, 0, v_ref_4666_);
                crate::leanh::lean_ctor_set(v___x_4697_, 1, v___x_4696_);
                v___x_4698_ = l_Lean_PersistentArray_push___redArg(v_traces_4686_, v___x_4697_);
                if v_isShared_4689_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4688_, 0, v___x_4698_);
                    v___x_4700_ = v___x_4688_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4709_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4709_, 0, v___x_4698_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4709_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4685_,
                    );
                    v___x_4700_ = v_reuseFailAlloc_4709_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4684_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4683_, 4, v___x_4700_);
                    v___x_4702_ = v___x_4683_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4708_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_env_4674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 1, v_nextMacroScope_4675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 2, v_ngen_4676_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 3, v_auxDeclNGen_4677_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 4, v___x_4700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 5, v_cache_4678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 6, v_messages_4679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 7, v_infoState_4680_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 8, v_snapshotTasks_4681_);
                    v___x_4702_ = v_reuseFailAlloc_4708_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4703_ = lean_st_ref_set(v___y_4664_, v___x_4702_);
                v___x_4704_ = crate::leanh::lean_box(0);
                if v_isShared_4671_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4670_, 0, v___x_4704_);
                    v___x_4706_ = v___x_4670_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4704_);
                    v___x_4706_ = v_reuseFailAlloc_4707_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(
    mut v_cls_4713_: *mut crate::leanh::LeanObject,
    mut v_msg_4714_: *mut crate::leanh::LeanObject,
    mut v___y_4715_: *mut crate::leanh::LeanObject,
    mut v___y_4716_: *mut crate::leanh::LeanObject,
    mut v___y_4717_: *mut crate::leanh::LeanObject,
    mut v___y_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4720_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_4713_, v_msg_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
    crate::leanh::lean_dec(v___y_4718_);
    crate::leanh::lean_dec_ref(v___y_4717_);
    crate::leanh::lean_dec(v___y_4716_);
    crate::leanh::lean_dec_ref(v___y_4715_);
    return v_res_4720_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4731_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3;
    v___x_4732_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5;
    v___x_4733_ = l_Lean_Name_append(v___x_4732_, v___x_4731_);
    return v___x_4733_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4735_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__7;
    v___x_4736_ = l_Lean_stringToMessageData(v___x_4735_);
    return v___x_4736_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4738_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__9;
    v___x_4739_ = l_Lean_stringToMessageData(v___x_4738_);
    return v___x_4739_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(
    mut v___x_4740_: u8,
    mut v_a_4741_: *mut crate::leanh::LeanObject,
    mut v___y_4742_: *mut crate::leanh::LeanObject,
    mut v___y_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
    mut v___y_4746_: *mut crate::leanh::LeanObject,
    mut v___y_4747_: *mut crate::leanh::LeanObject,
    mut v___y_4748_: *mut crate::leanh::LeanObject,
    mut v___y_4749_: *mut crate::leanh::LeanObject,
    mut v___y_4750_: *mut crate::leanh::LeanObject,
    mut v___y_4751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4758_: u8 = 0;
    let mut v_a_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4765_: u8 = 0;
    let mut v_a_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4773_: u8 = 0;
    let mut v_snd_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4777_: u8 = 0;
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4790_: u8 = 0;
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: u8 = 0;
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4811_: u8 = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_a_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4819_: u8 = 0;
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4823_: u8 = 0;
    let mut v_a_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4827_: u8 = 0;
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4831_: u8 = 0;
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4836_: u8 = 0;
    let mut v_unused_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_4774_ = crate::leanh::lean_ctor_get(v_a_4741_, 1);
                v_isSharedCheck_4836_ = (!crate::leanh::lean_is_exclusive(v_a_4741_)) as u8;
                if v_isSharedCheck_4836_ == 0 {
                    v_unused_4837_ = crate::leanh::lean_ctor_get(v_a_4741_, 0);
                    crate::leanh::lean_dec(v_unused_4837_);
                    v___x_4776_ = v_a_4741_;
                    v_isShared_4777_ = v_isSharedCheck_4836_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4774_);
                    crate::leanh::lean_dec(v_a_4741_);
                    v___x_4776_ = crate::leanh::lean_box(0);
                    v_isShared_4777_ = v_isSharedCheck_4836_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4754_) == 0 {
                    v_a_4755_ = crate::leanh::lean_ctor_get(v___y_4754_, 0);
                    v_isSharedCheck_4765_ = (!crate::leanh::lean_is_exclusive(v___y_4754_)) as u8;
                    if v_isSharedCheck_4765_ == 0 {
                        v___x_4757_ = v___y_4754_;
                        v_isShared_4758_ = v_isSharedCheck_4765_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4755_);
                        crate::leanh::lean_dec(v___y_4754_);
                        v___x_4757_ = crate::leanh::lean_box(0);
                        v_isShared_4758_ = v_isSharedCheck_4765_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4766_ = crate::leanh::lean_ctor_get(v___y_4754_, 0);
                    v_isSharedCheck_4773_ = (!crate::leanh::lean_is_exclusive(v___y_4754_)) as u8;
                    if v_isSharedCheck_4773_ == 0 {
                        v___x_4768_ = v___y_4754_;
                        v_isShared_4769_ = v_isSharedCheck_4773_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4766_);
                        crate::leanh::lean_dec(v___y_4754_);
                        v___x_4768_ = crate::leanh::lean_box(0);
                        v_isShared_4769_ = v_isSharedCheck_4773_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4755_) == 0 {
                    v_a_4759_ = crate::leanh::lean_ctor_get(v_a_4755_, 0);
                    crate::leanh::lean_inc(v_a_4759_);
                    crate::leanh::lean_dec_ref_known(v_a_4755_, 1);
                    if v_isShared_4758_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4757_, 0, v_a_4759_);
                        v___x_4761_ = v___x_4757_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4762_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4759_);
                        v___x_4761_ = v_reuseFailAlloc_4762_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4757_);
                    v_a_4763_ = crate::leanh::lean_ctor_get(v_a_4755_, 0);
                    crate::leanh::lean_inc(v_a_4763_);
                    crate::leanh::lean_dec_ref_known(v_a_4755_, 1);
                    v_a_4741_ = v_a_4763_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_4761_;
            }
            4 => {
                if v_isShared_4769_ == 0 {
                    v___x_4771_ = v___x_4768_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
                    v___x_4771_ = v_reuseFailAlloc_4772_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4771_;
            }
            6 => {
                v___x_4778_ = crate::leanh::lean_box(0);
                if crate::leanh::lean_obj_tag(v_snd_4774_) == 7 {
                    v_binderType_4779_ = crate::leanh::lean_ctor_get(v_snd_4774_, 1);
                    v_body_4780_ = crate::leanh::lean_ctor_get(v_snd_4774_, 2);
                    crate::leanh::lean_inc_ref(v_binderType_4779_);
                    v___x_4781_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_binderType_4779_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
                    if crate::leanh::lean_obj_tag(v___x_4781_) == 0 {
                        v_a_4782_ = crate::leanh::lean_ctor_get(v___x_4781_, 0);
                        crate::leanh::lean_inc(v_a_4782_);
                        crate::leanh::lean_dec_ref_known(v___x_4781_, 1);
                        v___x_4783_ = (crate::leanh::lean_unbox(v_a_4782_) as u8);
                        crate::leanh::lean_dec(v_a_4782_);
                        if v___x_4783_ == 0 {
                            crate::leanh::lean_inc_ref(v_body_4780_);
                            crate::leanh::lean_dec_ref_known(v_snd_4774_, 3);
                            if v_isShared_4777_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4776_, 1, v_body_4780_);
                                crate::leanh::lean_ctor_set(v___x_4776_, 0, v___x_4778_);
                                v___x_4785_ = v___x_4776_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_4787_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4778_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4787_,
                                    1,
                                    v_body_4780_,
                                );
                                v___x_4785_ = v_reuseFailAlloc_4787_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4776_);
                            v_options_4788_ = crate::leanh::lean_ctor_get(v___y_4750_, 2);
                            v_inheritedTraceOptions_4789_ =
                                crate::leanh::lean_ctor_get(v___y_4750_, 13);
                            v_hasTrace_4790_ = crate::leanh::lean_ctor_get_uint8(
                                v_options_4788_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            );
                            if v_hasTrace_4790_ == 0 {
                                state = 8;
                                continue;
                            } else {
                                v___x_4794_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3;
                                v___x_4795_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
                                v___x_4796_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_4789_,
                                        v_options_4788_,
                                        v___x_4795_,
                                    );
                                if v___x_4796_ == 0 {
                                    state = 8;
                                    continue;
                                } else {
                                    v___x_4797_ = l_Lean_Meta_Grind_updateLastTag(
                                        v___y_4742_,
                                        v___y_4743_,
                                        v___y_4744_,
                                        v___y_4745_,
                                        v___y_4746_,
                                        v___y_4747_,
                                        v___y_4748_,
                                        v___y_4749_,
                                        v___y_4750_,
                                        v___y_4751_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4797_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4797_, 1);
                                        v___x_4798_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__8);
                                        crate::leanh::lean_inc_ref(v_snd_4774_);
                                        v___x_4799_ = l_Lean_indentExpr(v_snd_4774_);
                                        v___x_4800_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4800_, 0, v___x_4798_);
                                        crate::leanh::lean_ctor_set(v___x_4800_, 1, v___x_4799_);
                                        v___x_4801_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__10);
                                        v___x_4802_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4802_, 0, v___x_4800_);
                                        crate::leanh::lean_ctor_set(v___x_4802_, 1, v___x_4801_);
                                        crate::leanh::lean_inc_ref(v_binderType_4779_);
                                        v___x_4803_ = l_Lean_indentExpr(v_binderType_4779_);
                                        v___x_4804_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4804_, 0, v___x_4802_);
                                        crate::leanh::lean_ctor_set(v___x_4804_, 1, v___x_4803_);
                                        v___x_4805_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_4794_, v___x_4804_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
                                        if crate::leanh::lean_obj_tag(v___x_4805_) == 0 {
                                            v_a_4806_ = crate::leanh::lean_ctor_get(v___x_4805_, 0);
                                            crate::leanh::lean_inc(v_a_4806_);
                                            crate::leanh::lean_dec_ref_known(v___x_4805_, 1);
                                            v___x_4807_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_4740_, v_snd_4774_, v_a_4806_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
                                            v___y_4754_ = v___x_4807_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref_known(v_snd_4774_, 3);
                                            v_a_4808_ = crate::leanh::lean_ctor_get(v___x_4805_, 0);
                                            v_isSharedCheck_4815_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4805_))
                                                    as u8;
                                            if v_isSharedCheck_4815_ == 0 {
                                                v___x_4810_ = v___x_4805_;
                                                v_isShared_4811_ = v_isSharedCheck_4815_;
                                                state = 9;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4808_);
                                                crate::leanh::lean_dec(v___x_4805_);
                                                v___x_4810_ = crate::leanh::lean_box(0);
                                                v_isShared_4811_ = v_isSharedCheck_4815_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_snd_4774_, 3);
                                        v_a_4816_ = crate::leanh::lean_ctor_get(v___x_4797_, 0);
                                        v_isSharedCheck_4823_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4797_)) as u8;
                                        if v_isSharedCheck_4823_ == 0 {
                                            v___x_4818_ = v___x_4797_;
                                            v_isShared_4819_ = v_isSharedCheck_4823_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4816_);
                                            crate::leanh::lean_dec(v___x_4797_);
                                            v___x_4818_ = crate::leanh::lean_box(0);
                                            v_isShared_4819_ = v_isSharedCheck_4823_;
                                            state = 11;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_snd_4774_, 3);
                        crate::leanh::lean_del_object(v___x_4776_);
                        v_a_4824_ = crate::leanh::lean_ctor_get(v___x_4781_, 0);
                        v_isSharedCheck_4831_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4781_)) as u8;
                        if v_isSharedCheck_4831_ == 0 {
                            v___x_4826_ = v___x_4781_;
                            v_isShared_4827_ = v_isSharedCheck_4831_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4824_);
                            crate::leanh::lean_dec(v___x_4781_);
                            v___x_4826_ = crate::leanh::lean_box(0);
                            v_isShared_4827_ = v_isSharedCheck_4831_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    if v_isShared_4777_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4776_, 0, v___x_4778_);
                        v___x_4833_ = v___x_4776_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_4835_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4778_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_snd_4774_);
                        v___x_4833_ = v_reuseFailAlloc_4835_;
                        state = 15;
                        continue;
                    }
                }
            }
            7 => {
                v_a_4741_ = v___x_4785_;
                state = 0;
                continue;
            }
            8 => {
                v___x_4792_ = crate::leanh::lean_box(0);
                v___x_4793_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___lam__0(v___x_4740_, v_snd_4774_, v___x_4792_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
                v___y_4754_ = v___x_4793_;
                state = 1;
                continue;
            }
            9 => {
                if v_isShared_4811_ == 0 {
                    v___x_4813_ = v___x_4810_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4814_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
                    v___x_4813_ = v_reuseFailAlloc_4814_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4813_;
            }
            11 => {
                if v_isShared_4819_ == 0 {
                    v___x_4821_ = v___x_4818_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
                    v___x_4821_ = v_reuseFailAlloc_4822_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4821_;
            }
            13 => {
                if v_isShared_4827_ == 0 {
                    v___x_4829_ = v___x_4826_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
                    v___x_4829_ = v_reuseFailAlloc_4830_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4829_;
            }
            15 => {
                v___x_4834_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4834_, 0, v___x_4833_);
                return v___x_4834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(
    mut v___x_4838_: *mut crate::leanh::LeanObject,
    mut v_a_4839_: *mut crate::leanh::LeanObject,
    mut v___y_4840_: *mut crate::leanh::LeanObject,
    mut v___y_4841_: *mut crate::leanh::LeanObject,
    mut v___y_4842_: *mut crate::leanh::LeanObject,
    mut v___y_4843_: *mut crate::leanh::LeanObject,
    mut v___y_4844_: *mut crate::leanh::LeanObject,
    mut v___y_4845_: *mut crate::leanh::LeanObject,
    mut v___y_4846_: *mut crate::leanh::LeanObject,
    mut v___y_4847_: *mut crate::leanh::LeanObject,
    mut v___y_4848_: *mut crate::leanh::LeanObject,
    mut v___y_4849_: *mut crate::leanh::LeanObject,
    mut v___y_4850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_32461__boxed_4851_: u8 = 0;
    let mut v_res_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_32461__boxed_4851_ = (crate::leanh::lean_unbox(v___x_4838_) as u8);
    v_res_4852_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_32461__boxed_4851_, v_a_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_, v___y_4849_);
    crate::leanh::lean_dec(v___y_4849_);
    crate::leanh::lean_dec_ref(v___y_4848_);
    crate::leanh::lean_dec(v___y_4847_);
    crate::leanh::lean_dec_ref(v___y_4846_);
    crate::leanh::lean_dec(v___y_4845_);
    crate::leanh::lean_dec_ref(v___y_4844_);
    crate::leanh::lean_dec(v___y_4843_);
    crate::leanh::lean_dec_ref(v___y_4842_);
    crate::leanh::lean_dec(v___y_4841_);
    crate::leanh::lean_dec(v___y_4840_);
    return v_res_4852_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(
    mut v_e_4853_: *mut crate::leanh::LeanObject,
    mut v_a_4854_: *mut crate::leanh::LeanObject,
    mut v_a_4855_: *mut crate::leanh::LeanObject,
    mut v_a_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
    mut v_a_4858_: *mut crate::leanh::LeanObject,
    mut v_a_4859_: *mut crate::leanh::LeanObject,
    mut v_a_4860_: *mut crate::leanh::LeanObject,
    mut v_a_4861_: *mut crate::leanh::LeanObject,
    mut v_a_4862_: *mut crate::leanh::LeanObject,
    mut v_a_4863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v___x_4871_: u8 = 0;
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: u8 = 0;
    let mut v_arg_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: u8 = 0;
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4888_: u8 = 0;
    let mut v_fst_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: u8 = 0;
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4899_: u8 = 0;
    let mut v_a_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4903_: u8 = 0;
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4907_: u8 = 0;
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut v_a_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4912_: u8 = 0;
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4865_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4853_, v_a_4861_);
                if crate::leanh::lean_obj_tag(v___x_4865_) == 0 {
                    v_a_4866_ = crate::leanh::lean_ctor_get(v___x_4865_, 0);
                    v_isSharedCheck_4908_ = (!crate::leanh::lean_is_exclusive(v___x_4865_)) as u8;
                    if v_isSharedCheck_4908_ == 0 {
                        v___x_4868_ = v___x_4865_;
                        v_isShared_4869_ = v_isSharedCheck_4908_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4866_);
                        crate::leanh::lean_dec(v___x_4865_);
                        v___x_4868_ = crate::leanh::lean_box(0);
                        v_isShared_4869_ = v_isSharedCheck_4908_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4909_ = crate::leanh::lean_ctor_get(v___x_4865_, 0);
                    v_isSharedCheck_4916_ = (!crate::leanh::lean_is_exclusive(v___x_4865_)) as u8;
                    if v_isSharedCheck_4916_ == 0 {
                        v___x_4911_ = v___x_4865_;
                        v_isShared_4912_ = v_isSharedCheck_4916_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4909_);
                        crate::leanh::lean_dec(v___x_4865_);
                        v___x_4911_ = crate::leanh::lean_box(0);
                        v_isShared_4912_ = v_isSharedCheck_4916_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4876_ = l_Lean_Expr_cleanupAnnotations(v_a_4866_);
                v___x_4877_ = l_Lean_Expr_isApp(v___x_4876_);
                if v___x_4877_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4876_);
                    state = 2;
                    continue;
                } else {
                    v_arg_4878_ = crate::leanh::lean_ctor_get(v___x_4876_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4878_);
                    v___x_4879_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4876_);
                    v___x_4880_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4;
                    v___x_4881_ = l_Lean_Expr_isConstOf(v___x_4879_, v___x_4880_);
                    crate::leanh::lean_dec_ref(v___x_4879_);
                    if v___x_4881_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_4878_);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_4868_);
                        v___x_4882_ = crate::leanh::lean_box(0);
                        v___x_4883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4883_, 0, v___x_4882_);
                        crate::leanh::lean_ctor_set(v___x_4883_, 1, v_arg_4878_);
                        v___x_4884_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_4881_, v___x_4883_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_);
                        if crate::leanh::lean_obj_tag(v___x_4884_) == 0 {
                            v_a_4885_ = crate::leanh::lean_ctor_get(v___x_4884_, 0);
                            v_isSharedCheck_4899_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4884_)) as u8;
                            if v_isSharedCheck_4899_ == 0 {
                                v___x_4887_ = v___x_4884_;
                                v_isShared_4888_ = v_isSharedCheck_4899_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4885_);
                                crate::leanh::lean_dec(v___x_4884_);
                                v___x_4887_ = crate::leanh::lean_box(0);
                                v_isShared_4888_ = v_isSharedCheck_4899_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_4900_ = crate::leanh::lean_ctor_get(v___x_4884_, 0);
                            v_isSharedCheck_4907_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4884_)) as u8;
                            if v_isSharedCheck_4907_ == 0 {
                                v___x_4902_ = v___x_4884_;
                                v_isShared_4903_ = v_isSharedCheck_4907_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4900_);
                                crate::leanh::lean_dec(v___x_4884_);
                                v___x_4902_ = crate::leanh::lean_box(0);
                                v_isShared_4903_ = v_isSharedCheck_4907_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_4871_ = 0;
                v___x_4872_ = crate::leanh::lean_box((v___x_4871_) as usize);
                if v_isShared_4869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4868_, 0, v___x_4872_);
                    v___x_4874_ = v___x_4868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4875_, 0, v___x_4872_);
                    v___x_4874_ = v_reuseFailAlloc_4875_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4874_;
            }
            4 => {
                v_fst_4889_ = crate::leanh::lean_ctor_get(v_a_4885_, 0);
                crate::leanh::lean_inc(v_fst_4889_);
                crate::leanh::lean_dec(v_a_4885_);
                if crate::leanh::lean_obj_tag(v_fst_4889_) == 0 {
                    v___x_4890_ = 0;
                    v___x_4891_ = crate::leanh::lean_box((v___x_4890_) as usize);
                    if v_isShared_4888_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4887_, 0, v___x_4891_);
                        v___x_4893_ = v___x_4887_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4891_);
                        v___x_4893_ = v_reuseFailAlloc_4894_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_4895_ = crate::leanh::lean_ctor_get(v_fst_4889_, 0);
                    crate::leanh::lean_inc(v_val_4895_);
                    crate::leanh::lean_dec_ref_known(v_fst_4889_, 1);
                    if v_isShared_4888_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4887_, 0, v_val_4895_);
                        v___x_4897_ = v___x_4887_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4898_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_val_4895_);
                        v___x_4897_ = v_reuseFailAlloc_4898_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4893_;
            }
            6 => {
                return v___x_4897_;
            }
            7 => {
                if v_isShared_4903_ == 0 {
                    v___x_4905_ = v___x_4902_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4906_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
                    v___x_4905_ = v_reuseFailAlloc_4906_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4905_;
            }
            9 => {
                if v_isShared_4912_ == 0 {
                    v___x_4914_ = v___x_4911_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4915_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4909_);
                    v___x_4914_ = v_reuseFailAlloc_4915_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(
    mut v_e_4917_: *mut crate::leanh::LeanObject,
    mut v_a_4918_: *mut crate::leanh::LeanObject,
    mut v_a_4919_: *mut crate::leanh::LeanObject,
    mut v_a_4920_: *mut crate::leanh::LeanObject,
    mut v_a_4921_: *mut crate::leanh::LeanObject,
    mut v_a_4922_: *mut crate::leanh::LeanObject,
    mut v_a_4923_: *mut crate::leanh::LeanObject,
    mut v_a_4924_: *mut crate::leanh::LeanObject,
    mut v_a_4925_: *mut crate::leanh::LeanObject,
    mut v_a_4926_: *mut crate::leanh::LeanObject,
    mut v_a_4927_: *mut crate::leanh::LeanObject,
    mut v_a_4928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4929_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(
        v_e_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_,
        v_a_4925_, v_a_4926_, v_a_4927_,
    );
    crate::leanh::lean_dec(v_a_4927_);
    crate::leanh::lean_dec_ref(v_a_4926_);
    crate::leanh::lean_dec(v_a_4925_);
    crate::leanh::lean_dec_ref(v_a_4924_);
    crate::leanh::lean_dec(v_a_4923_);
    crate::leanh::lean_dec_ref(v_a_4922_);
    crate::leanh::lean_dec(v_a_4921_);
    crate::leanh::lean_dec_ref(v_a_4920_);
    crate::leanh::lean_dec(v_a_4919_);
    crate::leanh::lean_dec(v_a_4918_);
    return v_res_4929_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(
    mut v_cls_4930_: *mut crate::leanh::LeanObject,
    mut v_msg_4931_: *mut crate::leanh::LeanObject,
    mut v___y_4932_: *mut crate::leanh::LeanObject,
    mut v___y_4933_: *mut crate::leanh::LeanObject,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
    mut v___y_4936_: *mut crate::leanh::LeanObject,
    mut v___y_4937_: *mut crate::leanh::LeanObject,
    mut v___y_4938_: *mut crate::leanh::LeanObject,
    mut v___y_4939_: *mut crate::leanh::LeanObject,
    mut v___y_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4943_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_4930_, v_msg_4931_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
    return v___x_4943_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(
    mut v_cls_4944_: *mut crate::leanh::LeanObject,
    mut v_msg_4945_: *mut crate::leanh::LeanObject,
    mut v___y_4946_: *mut crate::leanh::LeanObject,
    mut v___y_4947_: *mut crate::leanh::LeanObject,
    mut v___y_4948_: *mut crate::leanh::LeanObject,
    mut v___y_4949_: *mut crate::leanh::LeanObject,
    mut v___y_4950_: *mut crate::leanh::LeanObject,
    mut v___y_4951_: *mut crate::leanh::LeanObject,
    mut v___y_4952_: *mut crate::leanh::LeanObject,
    mut v___y_4953_: *mut crate::leanh::LeanObject,
    mut v___y_4954_: *mut crate::leanh::LeanObject,
    mut v___y_4955_: *mut crate::leanh::LeanObject,
    mut v___y_4956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4957_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(v_cls_4944_, v_msg_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
    crate::leanh::lean_dec(v___y_4955_);
    crate::leanh::lean_dec_ref(v___y_4954_);
    crate::leanh::lean_dec(v___y_4953_);
    crate::leanh::lean_dec_ref(v___y_4952_);
    crate::leanh::lean_dec(v___y_4951_);
    crate::leanh::lean_dec_ref(v___y_4950_);
    crate::leanh::lean_dec(v___y_4949_);
    crate::leanh::lean_dec_ref(v___y_4948_);
    crate::leanh::lean_dec(v___y_4947_);
    crate::leanh::lean_dec(v___y_4946_);
    return v_res_4957_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(
    mut v___x_4958_: u8,
    mut v_inst_4959_: *mut crate::leanh::LeanObject,
    mut v_a_4960_: *mut crate::leanh::LeanObject,
    mut v___y_4961_: *mut crate::leanh::LeanObject,
    mut v___y_4962_: *mut crate::leanh::LeanObject,
    mut v___y_4963_: *mut crate::leanh::LeanObject,
    mut v___y_4964_: *mut crate::leanh::LeanObject,
    mut v___y_4965_: *mut crate::leanh::LeanObject,
    mut v___y_4966_: *mut crate::leanh::LeanObject,
    mut v___y_4967_: *mut crate::leanh::LeanObject,
    mut v___y_4968_: *mut crate::leanh::LeanObject,
    mut v___y_4969_: *mut crate::leanh::LeanObject,
    mut v___y_4970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4972_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(v___x_4958_, v_a_4960_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_);
    return v___x_4972_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(
    mut v___x_4973_: *mut crate::leanh::LeanObject,
    mut v_inst_4974_: *mut crate::leanh::LeanObject,
    mut v_a_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
    mut v___y_4977_: *mut crate::leanh::LeanObject,
    mut v___y_4978_: *mut crate::leanh::LeanObject,
    mut v___y_4979_: *mut crate::leanh::LeanObject,
    mut v___y_4980_: *mut crate::leanh::LeanObject,
    mut v___y_4981_: *mut crate::leanh::LeanObject,
    mut v___y_4982_: *mut crate::leanh::LeanObject,
    mut v___y_4983_: *mut crate::leanh::LeanObject,
    mut v___y_4984_: *mut crate::leanh::LeanObject,
    mut v___y_4985_: *mut crate::leanh::LeanObject,
    mut v___y_4986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_32832__boxed_4987_: u8 = 0;
    let mut v_res_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_32832__boxed_4987_ = (crate::leanh::lean_unbox(v___x_4973_) as u8);
    v_res_4988_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(v___x_32832__boxed_4987_, v_inst_4974_, v_a_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_);
    crate::leanh::lean_dec(v___y_4985_);
    crate::leanh::lean_dec_ref(v___y_4984_);
    crate::leanh::lean_dec(v___y_4983_);
    crate::leanh::lean_dec_ref(v___y_4982_);
    crate::leanh::lean_dec(v___y_4981_);
    crate::leanh::lean_dec_ref(v___y_4980_);
    crate::leanh::lean_dec(v___y_4979_);
    crate::leanh::lean_dec_ref(v___y_4978_);
    crate::leanh::lean_dec(v___y_4977_);
    crate::leanh::lean_dec(v___y_4976_);
    return v_res_4988_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(
    mut v_k_4989_: *mut crate::leanh::LeanObject,
    mut v___y_4990_: *mut crate::leanh::LeanObject,
    mut v___y_4991_: *mut crate::leanh::LeanObject,
    mut v___y_4992_: *mut crate::leanh::LeanObject,
    mut v___y_4993_: *mut crate::leanh::LeanObject,
    mut v___y_4994_: *mut crate::leanh::LeanObject,
    mut v___y_4995_: *mut crate::leanh::LeanObject,
    mut v_b_4996_: *mut crate::leanh::LeanObject,
    mut v_c_4997_: *mut crate::leanh::LeanObject,
    mut v___y_4998_: *mut crate::leanh::LeanObject,
    mut v___y_4999_: *mut crate::leanh::LeanObject,
    mut v___y_5000_: *mut crate::leanh::LeanObject,
    mut v___y_5001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5001_);
    crate::leanh::lean_inc_ref(v___y_5000_);
    crate::leanh::lean_inc(v___y_4999_);
    crate::leanh::lean_inc_ref(v___y_4998_);
    crate::leanh::lean_inc(v___y_4995_);
    crate::leanh::lean_inc_ref(v___y_4994_);
    crate::leanh::lean_inc(v___y_4993_);
    crate::leanh::lean_inc_ref(v___y_4992_);
    crate::leanh::lean_inc(v___y_4991_);
    crate::leanh::lean_inc(v___y_4990_);
    v___x_5003_ = crate::leanh::lean_apply_13(
        v_k_4989_,
        v_b_4996_,
        v_c_4997_,
        v___y_4990_,
        v___y_4991_,
        v___y_4992_,
        v___y_4993_,
        v___y_4994_,
        v___y_4995_,
        v___y_4998_,
        v___y_4999_,
        v___y_5000_,
        v___y_5001_,
        crate::leanh::lean_box(0),
    );
    return v___x_5003_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(
    mut v_k_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
    mut v_b_5011_: *mut crate::leanh::LeanObject,
    mut v_c_5012_: *mut crate::leanh::LeanObject,
    mut v___y_5013_: *mut crate::leanh::LeanObject,
    mut v___y_5014_: *mut crate::leanh::LeanObject,
    mut v___y_5015_: *mut crate::leanh::LeanObject,
    mut v___y_5016_: *mut crate::leanh::LeanObject,
    mut v___y_5017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5018_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(v_k_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v_b_5011_, v_c_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
    crate::leanh::lean_dec(v___y_5016_);
    crate::leanh::lean_dec_ref(v___y_5015_);
    crate::leanh::lean_dec(v___y_5014_);
    crate::leanh::lean_dec_ref(v___y_5013_);
    crate::leanh::lean_dec(v___y_5010_);
    crate::leanh::lean_dec_ref(v___y_5009_);
    crate::leanh::lean_dec(v___y_5008_);
    crate::leanh::lean_dec_ref(v___y_5007_);
    crate::leanh::lean_dec(v___y_5006_);
    crate::leanh::lean_dec(v___y_5005_);
    return v_res_5018_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(
    mut v_type_5019_: *mut crate::leanh::LeanObject,
    mut v_k_5020_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5021_: u8,
    mut v_whnfType_5022_: u8,
    mut v___y_5023_: *mut crate::leanh::LeanObject,
    mut v___y_5024_: *mut crate::leanh::LeanObject,
    mut v___y_5025_: *mut crate::leanh::LeanObject,
    mut v___y_5026_: *mut crate::leanh::LeanObject,
    mut v___y_5027_: *mut crate::leanh::LeanObject,
    mut v___y_5028_: *mut crate::leanh::LeanObject,
    mut v___y_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5039_: u8 = 0;
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5028_);
                crate::leanh::lean_inc_ref(v___y_5027_);
                crate::leanh::lean_inc(v___y_5026_);
                crate::leanh::lean_inc_ref(v___y_5025_);
                crate::leanh::lean_inc(v___y_5024_);
                crate::leanh::lean_inc(v___y_5023_);
                v___f_5034_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
                crate::leanh::lean_closure_set(v___f_5034_, 0, v_k_5020_);
                crate::leanh::lean_closure_set(v___f_5034_, 1, v___y_5023_);
                crate::leanh::lean_closure_set(v___f_5034_, 2, v___y_5024_);
                crate::leanh::lean_closure_set(v___f_5034_, 3, v___y_5025_);
                crate::leanh::lean_closure_set(v___f_5034_, 4, v___y_5026_);
                crate::leanh::lean_closure_set(v___f_5034_, 5, v___y_5027_);
                crate::leanh::lean_closure_set(v___f_5034_, 6, v___y_5028_);
                v___x_5035_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_5019_,
                    v___f_5034_,
                    v_cleanupAnnotations_5021_,
                    v_whnfType_5022_,
                    v___y_5029_,
                    v___y_5030_,
                    v___y_5031_,
                    v___y_5032_,
                );
                if crate::leanh::lean_obj_tag(v___x_5035_) == 0 {
                    return v___x_5035_;
                } else {
                    v_a_5036_ = crate::leanh::lean_ctor_get(v___x_5035_, 0);
                    v_isSharedCheck_5043_ = (!crate::leanh::lean_is_exclusive(v___x_5035_)) as u8;
                    if v_isSharedCheck_5043_ == 0 {
                        v___x_5038_ = v___x_5035_;
                        v_isShared_5039_ = v_isSharedCheck_5043_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5036_);
                        crate::leanh::lean_dec(v___x_5035_);
                        v___x_5038_ = crate::leanh::lean_box(0);
                        v_isShared_5039_ = v_isSharedCheck_5043_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5039_ == 0 {
                    v___x_5041_ = v___x_5038_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5042_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_a_5036_);
                    v___x_5041_ = v_reuseFailAlloc_5042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(
    mut v_type_5044_: *mut crate::leanh::LeanObject,
    mut v_k_5045_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5046_: *mut crate::leanh::LeanObject,
    mut v_whnfType_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
    mut v___y_5055_: *mut crate::leanh::LeanObject,
    mut v___y_5056_: *mut crate::leanh::LeanObject,
    mut v___y_5057_: *mut crate::leanh::LeanObject,
    mut v___y_5058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5059_: u8 = 0;
    let mut v_whnfType_boxed_5060_: u8 = 0;
    let mut v_res_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5059_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_5046_) as u8);
    v_whnfType_boxed_5060_ = (crate::leanh::lean_unbox(v_whnfType_5047_) as u8);
    v_res_5061_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_5044_, v_k_5045_, v_cleanupAnnotations_boxed_5059_, v_whnfType_boxed_5060_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
    crate::leanh::lean_dec(v___y_5057_);
    crate::leanh::lean_dec_ref(v___y_5056_);
    crate::leanh::lean_dec(v___y_5055_);
    crate::leanh::lean_dec_ref(v___y_5054_);
    crate::leanh::lean_dec(v___y_5053_);
    crate::leanh::lean_dec_ref(v___y_5052_);
    crate::leanh::lean_dec(v___y_5051_);
    crate::leanh::lean_dec_ref(v___y_5050_);
    crate::leanh::lean_dec(v___y_5049_);
    crate::leanh::lean_dec(v___y_5048_);
    return v_res_5061_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(
    mut v_00_u03b1_5062_: *mut crate::leanh::LeanObject,
    mut v_type_5063_: *mut crate::leanh::LeanObject,
    mut v_k_5064_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5065_: u8,
    mut v_whnfType_5066_: u8,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
    mut v___y_5072_: *mut crate::leanh::LeanObject,
    mut v___y_5073_: *mut crate::leanh::LeanObject,
    mut v___y_5074_: *mut crate::leanh::LeanObject,
    mut v___y_5075_: *mut crate::leanh::LeanObject,
    mut v___y_5076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5078_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_type_5063_, v_k_5064_, v_cleanupAnnotations_5065_, v_whnfType_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_);
    return v___x_5078_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(
    mut v_00_u03b1_5079_: *mut crate::leanh::LeanObject,
    mut v_type_5080_: *mut crate::leanh::LeanObject,
    mut v_k_5081_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5082_: *mut crate::leanh::LeanObject,
    mut v_whnfType_5083_: *mut crate::leanh::LeanObject,
    mut v___y_5084_: *mut crate::leanh::LeanObject,
    mut v___y_5085_: *mut crate::leanh::LeanObject,
    mut v___y_5086_: *mut crate::leanh::LeanObject,
    mut v___y_5087_: *mut crate::leanh::LeanObject,
    mut v___y_5088_: *mut crate::leanh::LeanObject,
    mut v___y_5089_: *mut crate::leanh::LeanObject,
    mut v___y_5090_: *mut crate::leanh::LeanObject,
    mut v___y_5091_: *mut crate::leanh::LeanObject,
    mut v___y_5092_: *mut crate::leanh::LeanObject,
    mut v___y_5093_: *mut crate::leanh::LeanObject,
    mut v___y_5094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5095_: u8 = 0;
    let mut v_whnfType_boxed_5096_: u8 = 0;
    let mut v_res_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5095_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_5082_) as u8);
    v_whnfType_boxed_5096_ = (crate::leanh::lean_unbox(v_whnfType_5083_) as u8);
    v_res_5097_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(v_00_u03b1_5079_, v_type_5080_, v_k_5081_, v_cleanupAnnotations_boxed_5095_, v_whnfType_boxed_5096_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
    crate::leanh::lean_dec(v___y_5093_);
    crate::leanh::lean_dec_ref(v___y_5092_);
    crate::leanh::lean_dec(v___y_5091_);
    crate::leanh::lean_dec_ref(v___y_5090_);
    crate::leanh::lean_dec(v___y_5089_);
    crate::leanh::lean_dec_ref(v___y_5088_);
    crate::leanh::lean_dec(v___y_5087_);
    crate::leanh::lean_dec_ref(v___y_5086_);
    crate::leanh::lean_dec(v___y_5085_);
    crate::leanh::lean_dec(v___y_5084_);
    return v_res_5097_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(
    mut v_e_5101_: *mut crate::leanh::LeanObject,
    mut v_a_5102_: *mut crate::leanh::LeanObject,
    mut v_a_5103_: *mut crate::leanh::LeanObject,
    mut v_xs_5104_: *mut crate::leanh::LeanObject,
    mut v_x_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
    mut v___y_5109_: *mut crate::leanh::LeanObject,
    mut v___y_5110_: *mut crate::leanh::LeanObject,
    mut v___y_5111_: *mut crate::leanh::LeanObject,
    mut v___y_5112_: *mut crate::leanh::LeanObject,
    mut v___y_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_110573__boxed_5117_: u8 = 0;
    let mut v_res_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_110573__boxed_5117_ = (crate::leanh::lean_unbox(v_a_5102_) as u8);
    v_res_5118_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(v_e_5101_, v_a_110573__boxed_5117_, v_a_5103_, v_xs_5104_, v_x_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_);
    crate::leanh::lean_dec(v___y_5115_);
    crate::leanh::lean_dec_ref(v___y_5114_);
    crate::leanh::lean_dec(v___y_5113_);
    crate::leanh::lean_dec_ref(v___y_5112_);
    crate::leanh::lean_dec(v___y_5111_);
    crate::leanh::lean_dec_ref(v___y_5110_);
    crate::leanh::lean_dec(v___y_5109_);
    crate::leanh::lean_dec_ref(v___y_5108_);
    crate::leanh::lean_dec(v___y_5107_);
    crate::leanh::lean_dec(v___y_5106_);
    crate::leanh::lean_dec_ref(v_x_5105_);
    crate::leanh::lean_dec_ref(v_xs_5104_);
    return v_res_5118_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5120_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0;
    v___x_5121_ = l_Lean_stringToMessageData(v___x_5120_);
    return v___x_5121_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5123_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2;
    v___x_5124_ = l_Lean_stringToMessageData(v___x_5123_);
    return v___x_5124_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5126_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4;
    v___x_5127_ = l_Lean_stringToMessageData(v___x_5126_);
    return v___x_5127_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(
    mut v_e_5128_: *mut crate::leanh::LeanObject,
    mut v_h_5129_: *mut crate::leanh::LeanObject,
    mut v_a_5130_: *mut crate::leanh::LeanObject,
    mut v_a_5131_: *mut crate::leanh::LeanObject,
    mut v_a_5132_: *mut crate::leanh::LeanObject,
    mut v_a_5133_: *mut crate::leanh::LeanObject,
    mut v_a_5134_: *mut crate::leanh::LeanObject,
    mut v_a_5135_: *mut crate::leanh::LeanObject,
    mut v_a_5136_: *mut crate::leanh::LeanObject,
    mut v_a_5137_: *mut crate::leanh::LeanObject,
    mut v_a_5138_: *mut crate::leanh::LeanObject,
    mut v_a_5139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5145_: u8 = 0;
    let mut v___y_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5147_: u8 = 0;
    let mut v___y_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5150_: u8 = 0;
    let mut v_h_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5170_: u8 = 0;
    let mut v___x_5171_: u8 = 0;
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut v_a_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5189_: u8 = 0;
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5193_: u8 = 0;
    let mut v_a_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5197_: u8 = 0;
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5201_: u8 = 0;
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5206_: u8 = 0;
    let mut v_a_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5210_: u8 = 0;
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut v_a_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5218_: u8 = 0;
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5222_: u8 = 0;
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5227_: u8 = 0;
    let mut v_val_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5233_: u8 = 0;
    let mut v_val_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5237_: u8 = 0;
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5244_: u8 = 0;
    let mut v_name_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: u8 = 0;
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5260_: u8 = 0;
    let mut v_binderType_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: u8 = 0;
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5270_: u8 = 0;
    let mut v_a_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5274_: u8 = 0;
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5278_: u8 = 0;
    let mut v_a_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5282_: u8 = 0;
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5286_: u8 = 0;
    let mut v_isSharedCheck_5287_: u8 = 0;
    let mut v_a_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5291_: u8 = 0;
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5295_: u8 = 0;
    let mut v_isSharedCheck_5296_: u8 = 0;
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5301_: u8 = 0;
    let mut v_a_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5305_: u8 = 0;
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5309_: u8 = 0;
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5314_: u8 = 0;
    let mut v_a_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5318_: u8 = 0;
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5322_: u8 = 0;
    let mut v___y_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5338_: u8 = 0;
    let mut v_self_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_interpreted_5340_: u8 = 0;
    let mut v_ctor_5341_: u8 = 0;
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5347_: u8 = 0;
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: u8 = 0;
    let mut v_a_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5360_: u8 = 0;
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5364_: u8 = 0;
    let mut v_a_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5368_: u8 = 0;
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5372_: u8 = 0;
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: u8 = 0;
    let mut v_a_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5384_: u8 = 0;
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5388_: u8 = 0;
    let mut v_a_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5392_: u8 = 0;
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5396_: u8 = 0;
    let mut v_a_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5400_: u8 = 0;
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5404_: u8 = 0;
    let mut v_isSharedCheck_5405_: u8 = 0;
    let mut v_a_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5413_: u8 = 0;
    let mut v___y_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5429_: u8 = 0;
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5436_: u8 = 0;
    let mut v_fst_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5441_: u8 = 0;
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5446_: u8 = 0;
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: u8 = 0;
    let mut v_val_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: u8 = 0;
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: u8 = 0;
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5474_: u8 = 0;
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5478_: u8 = 0;
    let mut v_reuseFailAlloc_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5485_: u8 = 0;
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5489_: u8 = 0;
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
    let mut v_isSharedCheck_5514_: u8 = 0;
    let mut v_unused_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5516_: u8 = 0;
    let mut v_isSharedCheck_5517_: u8 = 0;
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5522_: u8 = 0;
    let mut v_a_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5526_: u8 = 0;
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5530_: u8 = 0;
    let mut v_options_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5532_: u8 = 0;
    let mut v_inheritedTraceOptions_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: u8 = 0;
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5547_: u8 = 0;
    let mut v___x_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5551_: u8 = 0;
    let mut v_a_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5555_: u8 = 0;
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5559_: u8 = 0;
    let mut v_a_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5563_: u8 = 0;
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5531_ = crate::leanh::lean_ctor_get(v_a_5138_, 2);
                v_hasTrace_5532_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_5531_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5532_ == 0 {
                    v___y_5415_ = v_a_5130_;
                    v___y_5416_ = v_a_5131_;
                    v___y_5417_ = v_a_5132_;
                    v___y_5418_ = v_a_5133_;
                    v___y_5419_ = v_a_5134_;
                    v___y_5420_ = v_a_5135_;
                    v___y_5421_ = v_a_5136_;
                    v___y_5422_ = v_a_5137_;
                    v___y_5423_ = v_a_5138_;
                    v___y_5424_ = v_a_5139_;
                    state = 50;
                    continue;
                } else {
                    v_inheritedTraceOptions_5533_ = crate::leanh::lean_ctor_get(v_a_5138_, 13);
                    v_cls_5534_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3;
                    v___x_5535_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
                    v___x_5536_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5533_,
                        v_options_5531_,
                        v___x_5535_,
                    );
                    if v___x_5536_ == 0 {
                        v___y_5415_ = v_a_5130_;
                        v___y_5416_ = v_a_5131_;
                        v___y_5417_ = v_a_5132_;
                        v___y_5418_ = v_a_5133_;
                        v___y_5419_ = v_a_5134_;
                        v___y_5420_ = v_a_5135_;
                        v___y_5421_ = v_a_5136_;
                        v___y_5422_ = v_a_5137_;
                        v___y_5423_ = v_a_5138_;
                        v___y_5424_ = v_a_5139_;
                        state = 50;
                        continue;
                    } else {
                        v___x_5537_ = l_Lean_Meta_Grind_updateLastTag(
                            v_a_5130_, v_a_5131_, v_a_5132_, v_a_5133_, v_a_5134_, v_a_5135_,
                            v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5537_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5537_, 1);
                            crate::leanh::lean_inc(v_a_5139_);
                            crate::leanh::lean_inc_ref(v_a_5138_);
                            crate::leanh::lean_inc(v_a_5137_);
                            crate::leanh::lean_inc_ref(v_a_5136_);
                            crate::leanh::lean_inc_ref(v_h_5129_);
                            v___x_5538_ = lean_infer_type(
                                v_h_5129_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5538_) == 0 {
                                v_a_5539_ = crate::leanh::lean_ctor_get(v___x_5538_, 0);
                                crate::leanh::lean_inc(v_a_5539_);
                                crate::leanh::lean_dec_ref_known(v___x_5538_, 1);
                                v___x_5540_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
                                v___x_5541_ = l_Lean_MessageData_ofExpr(v_a_5539_);
                                v___x_5542_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5542_, 0, v___x_5540_);
                                crate::leanh::lean_ctor_set(v___x_5542_, 1, v___x_5541_);
                                v___x_5543_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_5534_, v___x_5542_, v_a_5136_, v_a_5137_, v_a_5138_, v_a_5139_);
                                if crate::leanh::lean_obj_tag(v___x_5543_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5543_, 1);
                                    v___y_5415_ = v_a_5130_;
                                    v___y_5416_ = v_a_5131_;
                                    v___y_5417_ = v_a_5132_;
                                    v___y_5418_ = v_a_5133_;
                                    v___y_5419_ = v_a_5134_;
                                    v___y_5420_ = v_a_5135_;
                                    v___y_5421_ = v_a_5136_;
                                    v___y_5422_ = v_a_5137_;
                                    v___y_5423_ = v_a_5138_;
                                    v___y_5424_ = v_a_5139_;
                                    state = 50;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_h_5129_);
                                    crate::leanh::lean_dec_ref(v_e_5128_);
                                    v_a_5544_ = crate::leanh::lean_ctor_get(v___x_5543_, 0);
                                    v_isSharedCheck_5551_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5543_)) as u8;
                                    if v_isSharedCheck_5551_ == 0 {
                                        v___x_5546_ = v___x_5543_;
                                        v_isShared_5547_ = v_isSharedCheck_5551_;
                                        state = 71;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5544_);
                                        crate::leanh::lean_dec(v___x_5543_);
                                        v___x_5546_ = crate::leanh::lean_box(0);
                                        v_isShared_5547_ = v_isSharedCheck_5551_;
                                        state = 71;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_h_5129_);
                                crate::leanh::lean_dec_ref(v_e_5128_);
                                v_a_5552_ = crate::leanh::lean_ctor_get(v___x_5538_, 0);
                                v_isSharedCheck_5559_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5538_)) as u8;
                                if v_isSharedCheck_5559_ == 0 {
                                    v___x_5554_ = v___x_5538_;
                                    v_isShared_5555_ = v_isSharedCheck_5559_;
                                    state = 73;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5552_);
                                    crate::leanh::lean_dec(v___x_5538_);
                                    v___x_5554_ = crate::leanh::lean_box(0);
                                    v_isShared_5555_ = v_isSharedCheck_5559_;
                                    state = 73;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_h_5129_);
                            crate::leanh::lean_dec_ref(v_e_5128_);
                            v_a_5560_ = crate::leanh::lean_ctor_get(v___x_5537_, 0);
                            v_isSharedCheck_5567_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5537_)) as u8;
                            if v_isSharedCheck_5567_ == 0 {
                                v___x_5562_ = v___x_5537_;
                                v_isShared_5563_ = v_isSharedCheck_5567_;
                                state = 75;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5560_);
                                crate::leanh::lean_dec(v___x_5537_);
                                v___x_5562_ = crate::leanh::lean_box(0);
                                v_isShared_5563_ = v_isSharedCheck_5567_;
                                state = 75;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5142_ = crate::leanh::lean_box(0);
                v___x_5143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5143_, 0, v___x_5142_);
                return v___x_5143_;
            }
            2 => {
                if v___y_5147_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_5149_);
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    if v___y_5150_ == 0 {
                        crate::leanh::lean_dec_ref(v_h_5151_);
                        crate::leanh::lean_dec_ref(v___y_5148_);
                        crate::leanh::lean_dec_ref(v___y_5146_);
                        v___x_5162_ = crate::leanh::lean_box(0);
                        v___x_5163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5163_, 0, v___x_5162_);
                        return v___x_5163_;
                    } else {
                        crate::leanh::lean_inc_ref(v___y_5148_);
                        v___x_5164_ = l_Lean_Meta_normLitValue(
                            v___y_5148_,
                            v___y_5158_,
                            v___y_5159_,
                            v___y_5160_,
                            v___y_5161_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5164_) == 0 {
                            v_a_5165_ = crate::leanh::lean_ctor_get(v___x_5164_, 0);
                            crate::leanh::lean_inc(v_a_5165_);
                            crate::leanh::lean_dec_ref_known(v___x_5164_, 1);
                            crate::leanh::lean_inc_ref(v___y_5146_);
                            v___x_5166_ = l_Lean_Meta_normLitValue(
                                v___y_5146_,
                                v___y_5158_,
                                v___y_5159_,
                                v___y_5160_,
                                v___y_5161_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5166_) == 0 {
                                v_a_5167_ = crate::leanh::lean_ctor_get(v___x_5166_, 0);
                                v_isSharedCheck_5206_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5166_)) as u8;
                                if v_isSharedCheck_5206_ == 0 {
                                    v___x_5169_ = v___x_5166_;
                                    v_isShared_5170_ = v_isSharedCheck_5206_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5167_);
                                    crate::leanh::lean_dec(v___x_5166_);
                                    v___x_5169_ = crate::leanh::lean_box(0);
                                    v_isShared_5170_ = v_isSharedCheck_5206_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5165_);
                                crate::leanh::lean_dec_ref(v_h_5151_);
                                crate::leanh::lean_dec_ref(v___y_5148_);
                                crate::leanh::lean_dec_ref(v___y_5146_);
                                v_a_5207_ = crate::leanh::lean_ctor_get(v___x_5166_, 0);
                                v_isSharedCheck_5214_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5166_)) as u8;
                                if v_isSharedCheck_5214_ == 0 {
                                    v___x_5209_ = v___x_5166_;
                                    v_isShared_5210_ = v_isSharedCheck_5214_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5207_);
                                    crate::leanh::lean_dec(v___x_5166_);
                                    v___x_5209_ = crate::leanh::lean_box(0);
                                    v_isShared_5210_ = v_isSharedCheck_5214_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_h_5151_);
                            crate::leanh::lean_dec_ref(v___y_5148_);
                            crate::leanh::lean_dec_ref(v___y_5146_);
                            v_a_5215_ = crate::leanh::lean_ctor_get(v___x_5164_, 0);
                            v_isSharedCheck_5222_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5164_)) as u8;
                            if v_isSharedCheck_5222_ == 0 {
                                v___x_5217_ = v___x_5164_;
                                v_isShared_5218_ = v_isSharedCheck_5222_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5215_);
                                crate::leanh::lean_dec(v___x_5164_);
                                v___x_5217_ = crate::leanh::lean_box(0);
                                v_isShared_5218_ = v_isSharedCheck_5222_;
                                state = 13;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_5223_ = l_Lean_Meta_isConstructorApp_x3f(
                        v___y_5148_,
                        v___y_5158_,
                        v___y_5159_,
                        v___y_5160_,
                        v___y_5161_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5223_) == 0 {
                        v_a_5224_ = crate::leanh::lean_ctor_get(v___x_5223_, 0);
                        v_isSharedCheck_5314_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5223_)) as u8;
                        if v_isSharedCheck_5314_ == 0 {
                            v___x_5226_ = v___x_5223_;
                            v_isShared_5227_ = v_isSharedCheck_5314_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5224_);
                            crate::leanh::lean_dec(v___x_5223_);
                            v___x_5226_ = crate::leanh::lean_box(0);
                            v_isShared_5227_ = v_isSharedCheck_5314_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_h_5151_);
                        crate::leanh::lean_dec_ref(v___y_5149_);
                        crate::leanh::lean_dec_ref(v___y_5146_);
                        crate::leanh::lean_dec_ref(v_e_5128_);
                        v_a_5315_ = crate::leanh::lean_ctor_get(v___x_5223_, 0);
                        v_isSharedCheck_5322_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5223_)) as u8;
                        if v_isSharedCheck_5322_ == 0 {
                            v___x_5317_ = v___x_5223_;
                            v_isShared_5318_ = v_isSharedCheck_5322_;
                            state = 33;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5315_);
                            crate::leanh::lean_dec(v___x_5223_);
                            v___x_5317_ = crate::leanh::lean_box(0);
                            v_isShared_5318_ = v_isSharedCheck_5322_;
                            state = 33;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_5171_ = lean_expr_eqv(v_a_5165_, v_a_5167_);
                crate::leanh::lean_dec(v_a_5167_);
                crate::leanh::lean_dec(v_a_5165_);
                if v___x_5171_ == 0 {
                    crate::leanh::lean_del_object(v___x_5169_);
                    v___x_5172_ = l_Lean_Meta_mkEq(
                        v___y_5148_,
                        v___y_5146_,
                        v___y_5158_,
                        v___y_5159_,
                        v___y_5160_,
                        v___y_5161_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5172_) == 0 {
                        v_a_5173_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
                        crate::leanh::lean_inc(v_a_5173_);
                        crate::leanh::lean_dec_ref_known(v___x_5172_, 1);
                        v___x_5174_ = l_Lean_mkNot(v_a_5173_);
                        v___x_5175_ = l_Lean_Meta_mkDecideProof(
                            v___x_5174_,
                            v___y_5158_,
                            v___y_5159_,
                            v___y_5160_,
                            v___y_5161_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5175_) == 0 {
                            v_a_5176_ = crate::leanh::lean_ctor_get(v___x_5175_, 0);
                            v_isSharedCheck_5185_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5175_)) as u8;
                            if v_isSharedCheck_5185_ == 0 {
                                v___x_5178_ = v___x_5175_;
                                v_isShared_5179_ = v_isSharedCheck_5185_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5176_);
                                crate::leanh::lean_dec(v___x_5175_);
                                v___x_5178_ = crate::leanh::lean_box(0);
                                v_isShared_5179_ = v_isSharedCheck_5185_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_h_5151_);
                            v_a_5186_ = crate::leanh::lean_ctor_get(v___x_5175_, 0);
                            v_isSharedCheck_5193_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5175_)) as u8;
                            if v_isSharedCheck_5193_ == 0 {
                                v___x_5188_ = v___x_5175_;
                                v_isShared_5189_ = v_isSharedCheck_5193_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5186_);
                                crate::leanh::lean_dec(v___x_5175_);
                                v___x_5188_ = crate::leanh::lean_box(0);
                                v_isShared_5189_ = v_isSharedCheck_5193_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_h_5151_);
                        v_a_5194_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
                        v_isSharedCheck_5201_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5172_)) as u8;
                        if v_isSharedCheck_5201_ == 0 {
                            v___x_5196_ = v___x_5172_;
                            v_isShared_5197_ = v_isSharedCheck_5201_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5194_);
                            crate::leanh::lean_dec(v___x_5172_);
                            v___x_5196_ = crate::leanh::lean_box(0);
                            v_isShared_5197_ = v_isSharedCheck_5201_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_5151_);
                    crate::leanh::lean_dec_ref(v___y_5148_);
                    crate::leanh::lean_dec_ref(v___y_5146_);
                    v___x_5202_ = crate::leanh::lean_box(0);
                    if v_isShared_5170_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5169_, 0, v___x_5202_);
                        v___x_5204_ = v___x_5169_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5205_, 0, v___x_5202_);
                        v___x_5204_ = v_reuseFailAlloc_5205_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5180_ = l_Lean_Expr_app___override(v_a_5176_, v_h_5151_);
                v___x_5181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5181_, 0, v___x_5180_);
                if v_isShared_5179_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5178_, 0, v___x_5181_);
                    v___x_5183_ = v___x_5178_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5181_);
                    v___x_5183_ = v_reuseFailAlloc_5184_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5183_;
            }
            6 => {
                if v_isShared_5189_ == 0 {
                    v___x_5191_ = v___x_5188_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
                    v___x_5191_ = v_reuseFailAlloc_5192_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5191_;
            }
            8 => {
                if v_isShared_5197_ == 0 {
                    v___x_5199_ = v___x_5196_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5200_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
                    v___x_5199_ = v_reuseFailAlloc_5200_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5199_;
            }
            10 => {
                return v___x_5204_;
            }
            11 => {
                if v_isShared_5210_ == 0 {
                    v___x_5212_ = v___x_5209_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_a_5207_);
                    v___x_5212_ = v_reuseFailAlloc_5213_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5212_;
            }
            13 => {
                if v_isShared_5218_ == 0 {
                    v___x_5220_ = v___x_5217_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
                    v___x_5220_ = v_reuseFailAlloc_5221_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5220_;
            }
            15 => {
                if crate::leanh::lean_obj_tag(v_a_5224_) == 1 {
                    crate::leanh::lean_del_object(v___x_5226_);
                    v_val_5228_ = crate::leanh::lean_ctor_get(v_a_5224_, 0);
                    crate::leanh::lean_inc(v_val_5228_);
                    crate::leanh::lean_dec_ref_known(v_a_5224_, 1);
                    v___x_5229_ = l_Lean_Meta_isConstructorApp_x3f(
                        v___y_5146_,
                        v___y_5158_,
                        v___y_5159_,
                        v___y_5160_,
                        v___y_5161_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5229_) == 0 {
                        v_a_5230_ = crate::leanh::lean_ctor_get(v___x_5229_, 0);
                        v_isSharedCheck_5301_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5229_)) as u8;
                        if v_isSharedCheck_5301_ == 0 {
                            v___x_5232_ = v___x_5229_;
                            v_isShared_5233_ = v_isSharedCheck_5301_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5230_);
                            crate::leanh::lean_dec(v___x_5229_);
                            v___x_5232_ = crate::leanh::lean_box(0);
                            v_isShared_5233_ = v_isSharedCheck_5301_;
                            state = 16;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5228_);
                        crate::leanh::lean_dec_ref(v_h_5151_);
                        crate::leanh::lean_dec_ref(v___y_5149_);
                        crate::leanh::lean_dec_ref(v_e_5128_);
                        v_a_5302_ = crate::leanh::lean_ctor_get(v___x_5229_, 0);
                        v_isSharedCheck_5309_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5229_)) as u8;
                        if v_isSharedCheck_5309_ == 0 {
                            v___x_5304_ = v___x_5229_;
                            v_isShared_5305_ = v_isSharedCheck_5309_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5302_);
                            crate::leanh::lean_dec(v___x_5229_);
                            v___x_5304_ = crate::leanh::lean_box(0);
                            v_isShared_5305_ = v_isSharedCheck_5309_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5224_);
                    crate::leanh::lean_dec_ref(v_h_5151_);
                    crate::leanh::lean_dec_ref(v___y_5149_);
                    crate::leanh::lean_dec_ref(v___y_5146_);
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    v___x_5310_ = crate::leanh::lean_box(0);
                    if v_isShared_5227_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5226_, 0, v___x_5310_);
                        v___x_5312_ = v___x_5226_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_5313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5313_, 0, v___x_5310_);
                        v___x_5312_ = v_reuseFailAlloc_5313_;
                        state = 32;
                        continue;
                    }
                }
            }
            16 => {
                if crate::leanh::lean_obj_tag(v_a_5230_) == 1 {
                    crate::leanh::lean_del_object(v___x_5232_);
                    v_val_5234_ = crate::leanh::lean_ctor_get(v_a_5230_, 0);
                    v_isSharedCheck_5296_ = (!crate::leanh::lean_is_exclusive(v_a_5230_)) as u8;
                    if v_isSharedCheck_5296_ == 0 {
                        v___x_5236_ = v_a_5230_;
                        v_isShared_5237_ = v_isSharedCheck_5296_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5234_);
                        crate::leanh::lean_dec(v_a_5230_);
                        v___x_5236_ = crate::leanh::lean_box(0);
                        v_isShared_5237_ = v_isSharedCheck_5296_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5230_);
                    crate::leanh::lean_dec(v_val_5228_);
                    crate::leanh::lean_dec_ref(v_h_5151_);
                    crate::leanh::lean_dec_ref(v___y_5149_);
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    v___x_5297_ = crate::leanh::lean_box(0);
                    if v_isShared_5233_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5232_, 0, v___x_5297_);
                        v___x_5299_ = v___x_5232_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_5300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5300_, 0, v___x_5297_);
                        v___x_5299_ = v_reuseFailAlloc_5300_;
                        state = 29;
                        continue;
                    }
                }
            }
            17 => {
                v___x_5238_ = l_Lean_Meta_mkNoConfusion(
                    v___y_5149_,
                    v_h_5151_,
                    v___y_5158_,
                    v___y_5159_,
                    v___y_5160_,
                    v___y_5161_,
                );
                if crate::leanh::lean_obj_tag(v___x_5238_) == 0 {
                    v_toConstantVal_5239_ = crate::leanh::lean_ctor_get(v_val_5228_, 0);
                    crate::leanh::lean_inc_ref(v_toConstantVal_5239_);
                    crate::leanh::lean_dec(v_val_5228_);
                    v_toConstantVal_5240_ = crate::leanh::lean_ctor_get(v_val_5234_, 0);
                    crate::leanh::lean_inc_ref(v_toConstantVal_5240_);
                    crate::leanh::lean_dec(v_val_5234_);
                    v_a_5241_ = crate::leanh::lean_ctor_get(v___x_5238_, 0);
                    v_isSharedCheck_5287_ = (!crate::leanh::lean_is_exclusive(v___x_5238_)) as u8;
                    if v_isSharedCheck_5287_ == 0 {
                        v___x_5243_ = v___x_5238_;
                        v_isShared_5244_ = v_isSharedCheck_5287_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5241_);
                        crate::leanh::lean_dec(v___x_5238_);
                        v___x_5243_ = crate::leanh::lean_box(0);
                        v_isShared_5244_ = v_isSharedCheck_5287_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5236_);
                    crate::leanh::lean_dec(v_val_5234_);
                    crate::leanh::lean_dec(v_val_5228_);
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    v_a_5288_ = crate::leanh::lean_ctor_get(v___x_5238_, 0);
                    v_isSharedCheck_5295_ = (!crate::leanh::lean_is_exclusive(v___x_5238_)) as u8;
                    if v_isSharedCheck_5295_ == 0 {
                        v___x_5290_ = v___x_5238_;
                        v_isShared_5291_ = v_isSharedCheck_5295_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5288_);
                        crate::leanh::lean_dec(v___x_5238_);
                        v___x_5290_ = crate::leanh::lean_box(0);
                        v_isShared_5291_ = v_isSharedCheck_5295_;
                        state = 27;
                        continue;
                    }
                }
            }
            18 => {
                v_name_5245_ = crate::leanh::lean_ctor_get(v_toConstantVal_5239_, 0);
                crate::leanh::lean_inc(v_name_5245_);
                crate::leanh::lean_dec_ref(v_toConstantVal_5239_);
                v_name_5246_ = crate::leanh::lean_ctor_get(v_toConstantVal_5240_, 0);
                crate::leanh::lean_inc(v_name_5246_);
                crate::leanh::lean_dec_ref(v_toConstantVal_5240_);
                v___x_5247_ = lean_name_eq(v_name_5245_, v_name_5246_);
                crate::leanh::lean_dec(v_name_5246_);
                crate::leanh::lean_dec(v_name_5245_);
                if v___x_5247_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    if v_isShared_5237_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5236_, 0, v_a_5241_);
                        v___x_5249_ = v___x_5236_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_5253_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5241_);
                        v___x_5249_ = v_reuseFailAlloc_5253_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5243_);
                    crate::leanh::lean_del_object(v___x_5236_);
                    crate::leanh::lean_inc(v___y_5161_);
                    crate::leanh::lean_inc_ref(v___y_5160_);
                    crate::leanh::lean_inc(v___y_5159_);
                    crate::leanh::lean_inc_ref(v___y_5158_);
                    crate::leanh::lean_inc(v_a_5241_);
                    v___x_5254_ = lean_infer_type(
                        v_a_5241_,
                        v___y_5158_,
                        v___y_5159_,
                        v___y_5160_,
                        v___y_5161_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5254_) == 0 {
                        v_a_5255_ = crate::leanh::lean_ctor_get(v___x_5254_, 0);
                        crate::leanh::lean_inc(v_a_5255_);
                        crate::leanh::lean_dec_ref_known(v___x_5254_, 1);
                        v___x_5256_ = l_Lean_Meta_whnfD(
                            v_a_5255_,
                            v___y_5158_,
                            v___y_5159_,
                            v___y_5160_,
                            v___y_5161_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5256_) == 0 {
                            v_a_5257_ = crate::leanh::lean_ctor_get(v___x_5256_, 0);
                            v_isSharedCheck_5270_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5256_)) as u8;
                            if v_isSharedCheck_5270_ == 0 {
                                v___x_5259_ = v___x_5256_;
                                v_isShared_5260_ = v_isSharedCheck_5270_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5257_);
                                crate::leanh::lean_dec(v___x_5256_);
                                v___x_5259_ = crate::leanh::lean_box(0);
                                v_isShared_5260_ = v_isSharedCheck_5270_;
                                state = 21;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5241_);
                            crate::leanh::lean_dec_ref(v_e_5128_);
                            v_a_5271_ = crate::leanh::lean_ctor_get(v___x_5256_, 0);
                            v_isSharedCheck_5278_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5256_)) as u8;
                            if v_isSharedCheck_5278_ == 0 {
                                v___x_5273_ = v___x_5256_;
                                v_isShared_5274_ = v_isSharedCheck_5278_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5271_);
                                crate::leanh::lean_dec(v___x_5256_);
                                v___x_5273_ = crate::leanh::lean_box(0);
                                v_isShared_5274_ = v_isSharedCheck_5278_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5241_);
                        crate::leanh::lean_dec_ref(v_e_5128_);
                        v_a_5279_ = crate::leanh::lean_ctor_get(v___x_5254_, 0);
                        v_isSharedCheck_5286_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5254_)) as u8;
                        if v_isSharedCheck_5286_ == 0 {
                            v___x_5281_ = v___x_5254_;
                            v_isShared_5282_ = v_isSharedCheck_5286_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5279_);
                            crate::leanh::lean_dec(v___x_5254_);
                            v___x_5281_ = crate::leanh::lean_box(0);
                            v_isShared_5282_ = v_isSharedCheck_5286_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_5244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5243_, 0, v___x_5249_);
                    v___x_5251_ = v___x_5243_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
                    v___x_5251_ = v_reuseFailAlloc_5252_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5251_;
            }
            21 => {
                if crate::leanh::lean_obj_tag(v_a_5257_) == 7 {
                    crate::leanh::lean_del_object(v___x_5259_);
                    v_binderType_5261_ = crate::leanh::lean_ctor_get(v_a_5257_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_5261_);
                    crate::leanh::lean_dec_ref_known(v_a_5257_, 3);
                    v___x_5262_ = crate::leanh::lean_box((v___y_5145_) as usize);
                    v___f_5263_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed as *mut core::ffi::c_void, 16, 3);
                    crate::leanh::lean_closure_set(v___f_5263_, 0, v_e_5128_);
                    crate::leanh::lean_closure_set(v___f_5263_, 1, v___x_5262_);
                    crate::leanh::lean_closure_set(v___f_5263_, 2, v_a_5241_);
                    v___x_5264_ = 0;
                    v___x_5265_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_binderType_5261_, v___f_5263_, v___x_5264_, v___x_5264_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_);
                    return v___x_5265_;
                } else {
                    crate::leanh::lean_dec(v_a_5257_);
                    crate::leanh::lean_dec(v_a_5241_);
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    v___x_5266_ = crate::leanh::lean_box(0);
                    if v_isShared_5260_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5259_, 0, v___x_5266_);
                        v___x_5268_ = v___x_5259_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_5269_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5269_, 0, v___x_5266_);
                        v___x_5268_ = v_reuseFailAlloc_5269_;
                        state = 22;
                        continue;
                    }
                }
            }
            22 => {
                return v___x_5268_;
            }
            23 => {
                if v_isShared_5274_ == 0 {
                    v___x_5276_ = v___x_5273_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_a_5271_);
                    v___x_5276_ = v_reuseFailAlloc_5277_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5276_;
            }
            25 => {
                if v_isShared_5282_ == 0 {
                    v___x_5284_ = v___x_5281_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5285_, 0, v_a_5279_);
                    v___x_5284_ = v_reuseFailAlloc_5285_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5284_;
            }
            27 => {
                if v_isShared_5291_ == 0 {
                    v___x_5293_ = v___x_5290_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_a_5288_);
                    v___x_5293_ = v_reuseFailAlloc_5294_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5293_;
            }
            29 => {
                return v___x_5299_;
            }
            30 => {
                if v_isShared_5305_ == 0 {
                    v___x_5307_ = v___x_5304_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5308_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_a_5302_);
                    v___x_5307_ = v_reuseFailAlloc_5308_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_5307_;
            }
            32 => {
                return v___x_5312_;
            }
            33 => {
                if v_isShared_5318_ == 0 {
                    v___x_5320_ = v___x_5317_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5321_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_a_5315_);
                    v___x_5320_ = v_reuseFailAlloc_5321_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5320_;
            }
            35 => {
                v_self_5339_ = crate::leanh::lean_ctor_get(v___y_5327_, 0);
                crate::leanh::lean_inc_ref_n(v_self_5339_, 2);
                v_interpreted_5340_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5327_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 1) as u32,
                );
                v_ctor_5341_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_5327_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 2) as u32,
                );
                crate::leanh::lean_dec_ref(v___y_5327_);
                crate::leanh::lean_inc_ref(v___y_5324_);
                v___x_5342_ = l_Lean_Meta_Grind_hasSameType(
                    v_self_5339_,
                    v___y_5324_,
                    v___y_5330_,
                    v___y_5332_,
                    v___y_5326_,
                    v___y_5337_,
                );
                if crate::leanh::lean_obj_tag(v___x_5342_) == 0 {
                    v_a_5343_ = crate::leanh::lean_ctor_get(v___x_5342_, 0);
                    v_isSharedCheck_5405_ = (!crate::leanh::lean_is_exclusive(v___x_5342_)) as u8;
                    if v_isSharedCheck_5405_ == 0 {
                        v___x_5345_ = v___x_5342_;
                        v_isShared_5346_ = v_isSharedCheck_5405_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5343_);
                        crate::leanh::lean_dec(v___x_5342_);
                        v___x_5345_ = crate::leanh::lean_box(0);
                        v_isShared_5346_ = v_isSharedCheck_5405_;
                        state = 36;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_self_5339_);
                    crate::leanh::lean_dec_ref(v___y_5334_);
                    crate::leanh::lean_dec_ref(v___y_5329_);
                    crate::leanh::lean_dec_ref(v___y_5324_);
                    crate::leanh::lean_dec_ref(v_h_5129_);
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    v_a_5406_ = crate::leanh::lean_ctor_get(v___x_5342_, 0);
                    v_isSharedCheck_5413_ = (!crate::leanh::lean_is_exclusive(v___x_5342_)) as u8;
                    if v_isSharedCheck_5413_ == 0 {
                        v___x_5408_ = v___x_5342_;
                        v_isShared_5409_ = v_isSharedCheck_5413_;
                        state = 48;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5406_);
                        crate::leanh::lean_dec(v___x_5342_);
                        v___x_5408_ = crate::leanh::lean_box(0);
                        v_isShared_5409_ = v_isSharedCheck_5413_;
                        state = 48;
                        continue;
                    }
                }
            }
            36 => {
                v___x_5347_ = (crate::leanh::lean_unbox(v_a_5343_) as u8);
                if v___x_5347_ == 0 {
                    crate::leanh::lean_dec(v_a_5343_);
                    crate::leanh::lean_dec_ref(v_self_5339_);
                    crate::leanh::lean_dec_ref(v___y_5334_);
                    crate::leanh::lean_dec_ref(v___y_5329_);
                    crate::leanh::lean_dec_ref(v___y_5324_);
                    crate::leanh::lean_dec_ref(v_h_5129_);
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    v___x_5348_ = crate::leanh::lean_box(0);
                    if v_isShared_5346_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5345_, 0, v___x_5348_);
                        v___x_5350_ = v___x_5345_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_5351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5348_);
                        v___x_5350_ = v_reuseFailAlloc_5351_;
                        state = 37;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5345_);
                    if v___y_5338_ == 0 {
                        crate::leanh::lean_inc(v___y_5337_);
                        crate::leanh::lean_inc_ref(v___y_5326_);
                        crate::leanh::lean_inc(v___y_5332_);
                        crate::leanh::lean_inc_ref(v___y_5330_);
                        crate::leanh::lean_inc(v___y_5328_);
                        crate::leanh::lean_inc_ref(v___y_5333_);
                        crate::leanh::lean_inc(v___y_5335_);
                        crate::leanh::lean_inc_ref(v___y_5331_);
                        crate::leanh::lean_inc(v___y_5325_);
                        crate::leanh::lean_inc(v___y_5336_);
                        crate::leanh::lean_inc_ref(v_self_5339_);
                        v___x_5352_ = lean_grind_mk_eq_proof(
                            v_self_5339_,
                            v___y_5329_,
                            v___y_5336_,
                            v___y_5325_,
                            v___y_5331_,
                            v___y_5335_,
                            v___y_5333_,
                            v___y_5328_,
                            v___y_5330_,
                            v___y_5332_,
                            v___y_5326_,
                            v___y_5337_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5352_) == 0 {
                            v_a_5353_ = crate::leanh::lean_ctor_get(v___x_5352_, 0);
                            crate::leanh::lean_inc(v_a_5353_);
                            crate::leanh::lean_dec_ref_known(v___x_5352_, 1);
                            v___x_5354_ = l_Lean_Meta_mkEqTrans(
                                v_a_5353_,
                                v_h_5129_,
                                v___y_5330_,
                                v___y_5332_,
                                v___y_5326_,
                                v___y_5337_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5354_) == 0 {
                                v_a_5355_ = crate::leanh::lean_ctor_get(v___x_5354_, 0);
                                crate::leanh::lean_inc(v_a_5355_);
                                crate::leanh::lean_dec_ref_known(v___x_5354_, 1);
                                v___x_5356_ = (crate::leanh::lean_unbox(v_a_5343_) as u8);
                                crate::leanh::lean_dec(v_a_5343_);
                                v___y_5145_ = v___x_5356_;
                                v___y_5146_ = v___y_5324_;
                                v___y_5147_ = v_ctor_5341_;
                                v___y_5148_ = v_self_5339_;
                                v___y_5149_ = v___y_5334_;
                                v___y_5150_ = v_interpreted_5340_;
                                v_h_5151_ = v_a_5355_;
                                v___y_5152_ = v___y_5336_;
                                v___y_5153_ = v___y_5325_;
                                v___y_5154_ = v___y_5331_;
                                v___y_5155_ = v___y_5335_;
                                v___y_5156_ = v___y_5333_;
                                v___y_5157_ = v___y_5328_;
                                v___y_5158_ = v___y_5330_;
                                v___y_5159_ = v___y_5332_;
                                v___y_5160_ = v___y_5326_;
                                v___y_5161_ = v___y_5337_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_5343_);
                                crate::leanh::lean_dec_ref(v_self_5339_);
                                crate::leanh::lean_dec_ref(v___y_5334_);
                                crate::leanh::lean_dec_ref(v___y_5324_);
                                crate::leanh::lean_dec_ref(v_e_5128_);
                                v_a_5357_ = crate::leanh::lean_ctor_get(v___x_5354_, 0);
                                v_isSharedCheck_5364_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5354_)) as u8;
                                if v_isSharedCheck_5364_ == 0 {
                                    v___x_5359_ = v___x_5354_;
                                    v_isShared_5360_ = v_isSharedCheck_5364_;
                                    state = 38;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5357_);
                                    crate::leanh::lean_dec(v___x_5354_);
                                    v___x_5359_ = crate::leanh::lean_box(0);
                                    v_isShared_5360_ = v_isSharedCheck_5364_;
                                    state = 38;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5343_);
                            crate::leanh::lean_dec_ref(v_self_5339_);
                            crate::leanh::lean_dec_ref(v___y_5334_);
                            crate::leanh::lean_dec_ref(v___y_5324_);
                            crate::leanh::lean_dec_ref(v_h_5129_);
                            crate::leanh::lean_dec_ref(v_e_5128_);
                            v_a_5365_ = crate::leanh::lean_ctor_get(v___x_5352_, 0);
                            v_isSharedCheck_5372_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5352_)) as u8;
                            if v_isSharedCheck_5372_ == 0 {
                                v___x_5367_ = v___x_5352_;
                                v_isShared_5368_ = v_isSharedCheck_5372_;
                                state = 40;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5365_);
                                crate::leanh::lean_dec(v___x_5352_);
                                v___x_5367_ = crate::leanh::lean_box(0);
                                v_isShared_5368_ = v_isSharedCheck_5372_;
                                state = 40;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_inc(v___y_5337_);
                        crate::leanh::lean_inc_ref(v___y_5326_);
                        crate::leanh::lean_inc(v___y_5332_);
                        crate::leanh::lean_inc_ref(v___y_5330_);
                        crate::leanh::lean_inc(v___y_5328_);
                        crate::leanh::lean_inc_ref(v___y_5333_);
                        crate::leanh::lean_inc(v___y_5335_);
                        crate::leanh::lean_inc_ref(v___y_5331_);
                        crate::leanh::lean_inc(v___y_5325_);
                        crate::leanh::lean_inc(v___y_5336_);
                        crate::leanh::lean_inc_ref(v_self_5339_);
                        v___x_5373_ = lean_grind_mk_heq_proof(
                            v_self_5339_,
                            v___y_5329_,
                            v___y_5336_,
                            v___y_5325_,
                            v___y_5331_,
                            v___y_5335_,
                            v___y_5333_,
                            v___y_5328_,
                            v___y_5330_,
                            v___y_5332_,
                            v___y_5326_,
                            v___y_5337_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5373_) == 0 {
                            v_a_5374_ = crate::leanh::lean_ctor_get(v___x_5373_, 0);
                            crate::leanh::lean_inc(v_a_5374_);
                            crate::leanh::lean_dec_ref_known(v___x_5373_, 1);
                            v___x_5375_ = l_Lean_Meta_mkHEqTrans(
                                v_a_5374_,
                                v_h_5129_,
                                v___y_5330_,
                                v___y_5332_,
                                v___y_5326_,
                                v___y_5337_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5375_) == 0 {
                                v_a_5376_ = crate::leanh::lean_ctor_get(v___x_5375_, 0);
                                crate::leanh::lean_inc(v_a_5376_);
                                crate::leanh::lean_dec_ref_known(v___x_5375_, 1);
                                v___x_5377_ = 0;
                                v___x_5378_ = l_Lean_Meta_mkEqOfHEq(
                                    v_a_5376_,
                                    v___x_5377_,
                                    v___y_5330_,
                                    v___y_5332_,
                                    v___y_5326_,
                                    v___y_5337_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5378_) == 0 {
                                    v_a_5379_ = crate::leanh::lean_ctor_get(v___x_5378_, 0);
                                    crate::leanh::lean_inc(v_a_5379_);
                                    crate::leanh::lean_dec_ref_known(v___x_5378_, 1);
                                    v___x_5380_ = (crate::leanh::lean_unbox(v_a_5343_) as u8);
                                    crate::leanh::lean_dec(v_a_5343_);
                                    v___y_5145_ = v___x_5380_;
                                    v___y_5146_ = v___y_5324_;
                                    v___y_5147_ = v_ctor_5341_;
                                    v___y_5148_ = v_self_5339_;
                                    v___y_5149_ = v___y_5334_;
                                    v___y_5150_ = v_interpreted_5340_;
                                    v_h_5151_ = v_a_5379_;
                                    v___y_5152_ = v___y_5336_;
                                    v___y_5153_ = v___y_5325_;
                                    v___y_5154_ = v___y_5331_;
                                    v___y_5155_ = v___y_5335_;
                                    v___y_5156_ = v___y_5333_;
                                    v___y_5157_ = v___y_5328_;
                                    v___y_5158_ = v___y_5330_;
                                    v___y_5159_ = v___y_5332_;
                                    v___y_5160_ = v___y_5326_;
                                    v___y_5161_ = v___y_5337_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_5343_);
                                    crate::leanh::lean_dec_ref(v_self_5339_);
                                    crate::leanh::lean_dec_ref(v___y_5334_);
                                    crate::leanh::lean_dec_ref(v___y_5324_);
                                    crate::leanh::lean_dec_ref(v_e_5128_);
                                    v_a_5381_ = crate::leanh::lean_ctor_get(v___x_5378_, 0);
                                    v_isSharedCheck_5388_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5378_)) as u8;
                                    if v_isSharedCheck_5388_ == 0 {
                                        v___x_5383_ = v___x_5378_;
                                        v_isShared_5384_ = v_isSharedCheck_5388_;
                                        state = 42;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5381_);
                                        crate::leanh::lean_dec(v___x_5378_);
                                        v___x_5383_ = crate::leanh::lean_box(0);
                                        v_isShared_5384_ = v_isSharedCheck_5388_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5343_);
                                crate::leanh::lean_dec_ref(v_self_5339_);
                                crate::leanh::lean_dec_ref(v___y_5334_);
                                crate::leanh::lean_dec_ref(v___y_5324_);
                                crate::leanh::lean_dec_ref(v_e_5128_);
                                v_a_5389_ = crate::leanh::lean_ctor_get(v___x_5375_, 0);
                                v_isSharedCheck_5396_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5375_)) as u8;
                                if v_isSharedCheck_5396_ == 0 {
                                    v___x_5391_ = v___x_5375_;
                                    v_isShared_5392_ = v_isSharedCheck_5396_;
                                    state = 44;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5389_);
                                    crate::leanh::lean_dec(v___x_5375_);
                                    v___x_5391_ = crate::leanh::lean_box(0);
                                    v_isShared_5392_ = v_isSharedCheck_5396_;
                                    state = 44;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5343_);
                            crate::leanh::lean_dec_ref(v_self_5339_);
                            crate::leanh::lean_dec_ref(v___y_5334_);
                            crate::leanh::lean_dec_ref(v___y_5324_);
                            crate::leanh::lean_dec_ref(v_h_5129_);
                            crate::leanh::lean_dec_ref(v_e_5128_);
                            v_a_5397_ = crate::leanh::lean_ctor_get(v___x_5373_, 0);
                            v_isSharedCheck_5404_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5373_)) as u8;
                            if v_isSharedCheck_5404_ == 0 {
                                v___x_5399_ = v___x_5373_;
                                v_isShared_5400_ = v_isSharedCheck_5404_;
                                state = 46;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5397_);
                                crate::leanh::lean_dec(v___x_5373_);
                                v___x_5399_ = crate::leanh::lean_box(0);
                                v_isShared_5400_ = v_isSharedCheck_5404_;
                                state = 46;
                                continue;
                            }
                        }
                    }
                }
            }
            37 => {
                return v___x_5350_;
            }
            38 => {
                if v_isShared_5360_ == 0 {
                    v___x_5362_ = v___x_5359_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_5363_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5363_, 0, v_a_5357_);
                    v___x_5362_ = v_reuseFailAlloc_5363_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_5362_;
            }
            40 => {
                if v_isShared_5368_ == 0 {
                    v___x_5370_ = v___x_5367_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
                    v___x_5370_ = v_reuseFailAlloc_5371_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_5370_;
            }
            42 => {
                if v_isShared_5384_ == 0 {
                    v___x_5386_ = v___x_5383_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_5387_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_a_5381_);
                    v___x_5386_ = v_reuseFailAlloc_5387_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_5386_;
            }
            44 => {
                if v_isShared_5392_ == 0 {
                    v___x_5394_ = v___x_5391_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_5395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5389_);
                    v___x_5394_ = v_reuseFailAlloc_5395_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_5394_;
            }
            46 => {
                if v_isShared_5400_ == 0 {
                    v___x_5402_ = v___x_5399_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_5403_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_a_5397_);
                    v___x_5402_ = v_reuseFailAlloc_5403_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_5402_;
            }
            48 => {
                if v_isShared_5409_ == 0 {
                    v___x_5411_ = v___x_5408_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_5412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_a_5406_);
                    v___x_5411_ = v_reuseFailAlloc_5412_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_5411_;
            }
            50 => {
                crate::leanh::lean_inc(v___y_5424_);
                crate::leanh::lean_inc_ref(v___y_5423_);
                crate::leanh::lean_inc(v___y_5422_);
                crate::leanh::lean_inc_ref(v___y_5421_);
                crate::leanh::lean_inc_ref(v_h_5129_);
                v___x_5425_ = lean_infer_type(
                    v_h_5129_,
                    v___y_5421_,
                    v___y_5422_,
                    v___y_5423_,
                    v___y_5424_,
                );
                if crate::leanh::lean_obj_tag(v___x_5425_) == 0 {
                    v_a_5426_ = crate::leanh::lean_ctor_get(v___x_5425_, 0);
                    v_isSharedCheck_5522_ = (!crate::leanh::lean_is_exclusive(v___x_5425_)) as u8;
                    if v_isSharedCheck_5522_ == 0 {
                        v___x_5428_ = v___x_5425_;
                        v_isShared_5429_ = v_isSharedCheck_5522_;
                        state = 51;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5426_);
                        crate::leanh::lean_dec(v___x_5425_);
                        v___x_5428_ = crate::leanh::lean_box(0);
                        v_isShared_5429_ = v_isSharedCheck_5522_;
                        state = 51;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_5129_);
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    v_a_5523_ = crate::leanh::lean_ctor_get(v___x_5425_, 0);
                    v_isSharedCheck_5530_ = (!crate::leanh::lean_is_exclusive(v___x_5425_)) as u8;
                    if v_isSharedCheck_5530_ == 0 {
                        v___x_5525_ = v___x_5425_;
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 69;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5523_);
                        crate::leanh::lean_dec(v___x_5425_);
                        v___x_5525_ = crate::leanh::lean_box(0);
                        v_isShared_5526_ = v_isSharedCheck_5530_;
                        state = 69;
                        continue;
                    }
                }
            }
            51 => {
                v___x_5430_ =
                    l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(
                        v_a_5426_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5430_) == 1 {
                    crate::leanh::lean_del_object(v___x_5428_);
                    v_val_5431_ = crate::leanh::lean_ctor_get(v___x_5430_, 0);
                    crate::leanh::lean_inc(v_val_5431_);
                    crate::leanh::lean_dec_ref_known(v___x_5430_, 1);
                    v_snd_5432_ = crate::leanh::lean_ctor_get(v_val_5431_, 1);
                    v_fst_5433_ = crate::leanh::lean_ctor_get(v_val_5431_, 0);
                    v_isSharedCheck_5517_ = (!crate::leanh::lean_is_exclusive(v_val_5431_)) as u8;
                    if v_isSharedCheck_5517_ == 0 {
                        v___x_5435_ = v_val_5431_;
                        v_isShared_5436_ = v_isSharedCheck_5517_;
                        state = 52;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5432_);
                        crate::leanh::lean_inc(v_fst_5433_);
                        crate::leanh::lean_dec(v_val_5431_);
                        v___x_5435_ = crate::leanh::lean_box(0);
                        v_isShared_5436_ = v_isSharedCheck_5517_;
                        state = 52;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5430_);
                    crate::leanh::lean_dec_ref(v_h_5129_);
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    v___x_5518_ = crate::leanh::lean_box(0);
                    if v_isShared_5429_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5428_, 0, v___x_5518_);
                        v___x_5520_ = v___x_5428_;
                        state = 68;
                        continue;
                    } else {
                        v_reuseFailAlloc_5521_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5518_);
                        v___x_5520_ = v_reuseFailAlloc_5521_;
                        state = 68;
                        continue;
                    }
                }
            }
            52 => {
                v_fst_5437_ = crate::leanh::lean_ctor_get(v_snd_5432_, 0);
                v_snd_5438_ = crate::leanh::lean_ctor_get(v_snd_5432_, 1);
                v_isSharedCheck_5516_ = (!crate::leanh::lean_is_exclusive(v_snd_5432_)) as u8;
                if v_isSharedCheck_5516_ == 0 {
                    v___x_5440_ = v_snd_5432_;
                    v_isShared_5441_ = v_isSharedCheck_5516_;
                    state = 53;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5438_);
                    crate::leanh::lean_inc(v_fst_5437_);
                    crate::leanh::lean_dec(v_snd_5432_);
                    v___x_5440_ = crate::leanh::lean_box(0);
                    v_isShared_5441_ = v_isSharedCheck_5516_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                v___x_5442_ = lean_st_ref_get(v___y_5415_);
                v_mvarId_5443_ = crate::leanh::lean_ctor_get(v___x_5442_, 1);
                v_isSharedCheck_5514_ = (!crate::leanh::lean_is_exclusive(v___x_5442_)) as u8;
                if v_isSharedCheck_5514_ == 0 {
                    v_unused_5515_ = crate::leanh::lean_ctor_get(v___x_5442_, 0);
                    crate::leanh::lean_dec(v_unused_5515_);
                    v___x_5445_ = v___x_5442_;
                    v_isShared_5446_ = v_isSharedCheck_5514_;
                    state = 54;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_5443_);
                    crate::leanh::lean_dec(v___x_5442_);
                    v___x_5445_ = crate::leanh::lean_box(0);
                    v_isShared_5446_ = v_isSharedCheck_5514_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v___x_5447_ = l_Lean_MVarId_getType(
                    v_mvarId_5443_,
                    v___y_5421_,
                    v___y_5422_,
                    v___y_5423_,
                    v___y_5424_,
                );
                if crate::leanh::lean_obj_tag(v___x_5447_) == 0 {
                    v_a_5448_ = crate::leanh::lean_ctor_get(v___x_5447_, 0);
                    crate::leanh::lean_inc(v_a_5448_);
                    crate::leanh::lean_dec_ref_known(v___x_5447_, 1);
                    v___x_5449_ = l_Lean_Meta_Sym_shareCommon___redArg(v_fst_5437_, v___y_5420_);
                    if crate::leanh::lean_obj_tag(v___x_5449_) == 0 {
                        v_a_5450_ = crate::leanh::lean_ctor_get(v___x_5449_, 0);
                        crate::leanh::lean_inc(v_a_5450_);
                        crate::leanh::lean_dec_ref_known(v___x_5449_, 1);
                        v___x_5451_ =
                            l_Lean_Meta_Grind_getRootENode_x3f___redArg(v_a_5450_, v___y_5415_);
                        if crate::leanh::lean_obj_tag(v___x_5451_) == 0 {
                            v_a_5452_ = crate::leanh::lean_ctor_get(v___x_5451_, 0);
                            crate::leanh::lean_inc(v_a_5452_);
                            crate::leanh::lean_dec_ref_known(v___x_5451_, 1);
                            if crate::leanh::lean_obj_tag(v_a_5452_) == 1 {
                                crate::leanh::lean_del_object(v___x_5445_);
                                crate::leanh::lean_del_object(v___x_5440_);
                                crate::leanh::lean_del_object(v___x_5435_);
                                if crate::leanh::lean_obj_tag(v_fst_5433_) == 0 {
                                    v_val_5453_ = crate::leanh::lean_ctor_get(v_a_5452_, 0);
                                    crate::leanh::lean_inc(v_val_5453_);
                                    crate::leanh::lean_dec_ref_known(v_a_5452_, 1);
                                    v___x_5454_ = 0;
                                    v___y_5324_ = v_snd_5438_;
                                    v___y_5325_ = v___y_5416_;
                                    v___y_5326_ = v___y_5423_;
                                    v___y_5327_ = v_val_5453_;
                                    v___y_5328_ = v___y_5420_;
                                    v___y_5329_ = v_a_5450_;
                                    v___y_5330_ = v___y_5421_;
                                    v___y_5331_ = v___y_5417_;
                                    v___y_5332_ = v___y_5422_;
                                    v___y_5333_ = v___y_5419_;
                                    v___y_5334_ = v_a_5448_;
                                    v___y_5335_ = v___y_5418_;
                                    v___y_5336_ = v___y_5415_;
                                    v___y_5337_ = v___y_5424_;
                                    v___y_5338_ = v___x_5454_;
                                    state = 35;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_fst_5433_, 1);
                                    v_val_5455_ = crate::leanh::lean_ctor_get(v_a_5452_, 0);
                                    crate::leanh::lean_inc(v_val_5455_);
                                    crate::leanh::lean_dec_ref_known(v_a_5452_, 1);
                                    v___x_5456_ = 1;
                                    v___y_5324_ = v_snd_5438_;
                                    v___y_5325_ = v___y_5416_;
                                    v___y_5326_ = v___y_5423_;
                                    v___y_5327_ = v_val_5455_;
                                    v___y_5328_ = v___y_5420_;
                                    v___y_5329_ = v_a_5450_;
                                    v___y_5330_ = v___y_5421_;
                                    v___y_5331_ = v___y_5417_;
                                    v___y_5332_ = v___y_5422_;
                                    v___y_5333_ = v___y_5419_;
                                    v___y_5334_ = v_a_5448_;
                                    v___y_5335_ = v___y_5418_;
                                    v___y_5336_ = v___y_5415_;
                                    v___y_5337_ = v___y_5424_;
                                    v___y_5338_ = v___x_5456_;
                                    state = 35;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5452_);
                                crate::leanh::lean_dec(v_a_5448_);
                                crate::leanh::lean_dec(v_snd_5438_);
                                crate::leanh::lean_dec(v_fst_5433_);
                                crate::leanh::lean_dec_ref(v_h_5129_);
                                v___x_5457_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_5419_);
                                if crate::leanh::lean_obj_tag(v___x_5457_) == 0 {
                                    v_a_5458_ = crate::leanh::lean_ctor_get(v___x_5457_, 0);
                                    crate::leanh::lean_inc(v_a_5458_);
                                    crate::leanh::lean_dec_ref_known(v___x_5457_, 1);
                                    v___x_5459_ = (crate::leanh::lean_unbox(v_a_5458_) as u8);
                                    crate::leanh::lean_dec(v_a_5458_);
                                    if v___x_5459_ == 0 {
                                        crate::leanh::lean_dec(v_a_5450_);
                                        crate::leanh::lean_del_object(v___x_5445_);
                                        crate::leanh::lean_del_object(v___x_5440_);
                                        crate::leanh::lean_del_object(v___x_5435_);
                                        crate::leanh::lean_dec_ref(v_e_5128_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_5460_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
                                        v___x_5461_ = l_Lean_indentExpr(v_a_5450_);
                                        if v_isShared_5446_ == 0 {
                                            crate::leanh::lean_ctor_set_tag(v___x_5445_, 7);
                                            crate::leanh::lean_ctor_set(
                                                v___x_5445_,
                                                1,
                                                v___x_5461_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_5445_,
                                                0,
                                                v___x_5460_,
                                            );
                                            v___x_5463_ = v___x_5445_;
                                            state = 55;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_5481_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_5481_,
                                                0,
                                                v___x_5460_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_5481_,
                                                1,
                                                v___x_5461_,
                                            );
                                            v___x_5463_ = v_reuseFailAlloc_5481_;
                                            state = 55;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5450_);
                                    crate::leanh::lean_del_object(v___x_5445_);
                                    crate::leanh::lean_del_object(v___x_5440_);
                                    crate::leanh::lean_del_object(v___x_5435_);
                                    crate::leanh::lean_dec_ref(v_e_5128_);
                                    v_a_5482_ = crate::leanh::lean_ctor_get(v___x_5457_, 0);
                                    v_isSharedCheck_5489_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5457_)) as u8;
                                    if v_isSharedCheck_5489_ == 0 {
                                        v___x_5484_ = v___x_5457_;
                                        v_isShared_5485_ = v_isSharedCheck_5489_;
                                        state = 60;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5482_);
                                        crate::leanh::lean_dec(v___x_5457_);
                                        v___x_5484_ = crate::leanh::lean_box(0);
                                        v_isShared_5485_ = v_isSharedCheck_5489_;
                                        state = 60;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5450_);
                            crate::leanh::lean_dec(v_a_5448_);
                            crate::leanh::lean_del_object(v___x_5445_);
                            crate::leanh::lean_del_object(v___x_5440_);
                            crate::leanh::lean_dec(v_snd_5438_);
                            crate::leanh::lean_del_object(v___x_5435_);
                            crate::leanh::lean_dec(v_fst_5433_);
                            crate::leanh::lean_dec_ref(v_h_5129_);
                            crate::leanh::lean_dec_ref(v_e_5128_);
                            v_a_5490_ = crate::leanh::lean_ctor_get(v___x_5451_, 0);
                            v_isSharedCheck_5497_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5451_)) as u8;
                            if v_isSharedCheck_5497_ == 0 {
                                v___x_5492_ = v___x_5451_;
                                v_isShared_5493_ = v_isSharedCheck_5497_;
                                state = 62;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5490_);
                                crate::leanh::lean_dec(v___x_5451_);
                                v___x_5492_ = crate::leanh::lean_box(0);
                                v_isShared_5493_ = v_isSharedCheck_5497_;
                                state = 62;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5448_);
                        crate::leanh::lean_del_object(v___x_5445_);
                        crate::leanh::lean_del_object(v___x_5440_);
                        crate::leanh::lean_dec(v_snd_5438_);
                        crate::leanh::lean_del_object(v___x_5435_);
                        crate::leanh::lean_dec(v_fst_5433_);
                        crate::leanh::lean_dec_ref(v_h_5129_);
                        crate::leanh::lean_dec_ref(v_e_5128_);
                        v_a_5498_ = crate::leanh::lean_ctor_get(v___x_5449_, 0);
                        v_isSharedCheck_5505_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5449_)) as u8;
                        if v_isSharedCheck_5505_ == 0 {
                            v___x_5500_ = v___x_5449_;
                            v_isShared_5501_ = v_isSharedCheck_5505_;
                            state = 64;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5498_);
                            crate::leanh::lean_dec(v___x_5449_);
                            v___x_5500_ = crate::leanh::lean_box(0);
                            v_isShared_5501_ = v_isSharedCheck_5505_;
                            state = 64;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5445_);
                    crate::leanh::lean_del_object(v___x_5440_);
                    crate::leanh::lean_dec(v_snd_5438_);
                    crate::leanh::lean_dec(v_fst_5437_);
                    crate::leanh::lean_del_object(v___x_5435_);
                    crate::leanh::lean_dec(v_fst_5433_);
                    crate::leanh::lean_dec_ref(v_h_5129_);
                    crate::leanh::lean_dec_ref(v_e_5128_);
                    v_a_5506_ = crate::leanh::lean_ctor_get(v___x_5447_, 0);
                    v_isSharedCheck_5513_ = (!crate::leanh::lean_is_exclusive(v___x_5447_)) as u8;
                    if v_isSharedCheck_5513_ == 0 {
                        v___x_5508_ = v___x_5447_;
                        v_isShared_5509_ = v_isSharedCheck_5513_;
                        state = 66;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5506_);
                        crate::leanh::lean_dec(v___x_5447_);
                        v___x_5508_ = crate::leanh::lean_box(0);
                        v_isShared_5509_ = v_isSharedCheck_5513_;
                        state = 66;
                        continue;
                    }
                }
            }
            55 => {
                v___x_5464_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
                if v_isShared_5441_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5440_, 7);
                    crate::leanh::lean_ctor_set(v___x_5440_, 1, v___x_5464_);
                    crate::leanh::lean_ctor_set(v___x_5440_, 0, v___x_5463_);
                    v___x_5466_ = v___x_5440_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_5480_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5480_, 1, v___x_5464_);
                    v___x_5466_ = v_reuseFailAlloc_5480_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v___x_5467_ = l_Lean_indentExpr(v_e_5128_);
                if v_isShared_5436_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5435_, 7);
                    crate::leanh::lean_ctor_set(v___x_5435_, 1, v___x_5467_);
                    crate::leanh::lean_ctor_set(v___x_5435_, 0, v___x_5466_);
                    v___x_5469_ = v___x_5435_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_5479_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 0, v___x_5466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 1, v___x_5467_);
                    v___x_5469_ = v_reuseFailAlloc_5479_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                v___x_5470_ = l_Lean_Meta_Sym_reportIssue(
                    v___x_5469_,
                    v___y_5419_,
                    v___y_5420_,
                    v___y_5421_,
                    v___y_5422_,
                    v___y_5423_,
                    v___y_5424_,
                );
                if crate::leanh::lean_obj_tag(v___x_5470_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5470_, 1);
                    state = 1;
                    continue;
                } else {
                    v_a_5471_ = crate::leanh::lean_ctor_get(v___x_5470_, 0);
                    v_isSharedCheck_5478_ = (!crate::leanh::lean_is_exclusive(v___x_5470_)) as u8;
                    if v_isSharedCheck_5478_ == 0 {
                        v___x_5473_ = v___x_5470_;
                        v_isShared_5474_ = v_isSharedCheck_5478_;
                        state = 58;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5471_);
                        crate::leanh::lean_dec(v___x_5470_);
                        v___x_5473_ = crate::leanh::lean_box(0);
                        v_isShared_5474_ = v_isSharedCheck_5478_;
                        state = 58;
                        continue;
                    }
                }
            }
            58 => {
                if v_isShared_5474_ == 0 {
                    v___x_5476_ = v___x_5473_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_5477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_a_5471_);
                    v___x_5476_ = v_reuseFailAlloc_5477_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_5476_;
            }
            60 => {
                if v_isShared_5485_ == 0 {
                    v___x_5487_ = v___x_5484_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_5488_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_a_5482_);
                    v___x_5487_ = v_reuseFailAlloc_5488_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_5487_;
            }
            62 => {
                if v_isShared_5493_ == 0 {
                    v___x_5495_ = v___x_5492_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_5496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5496_, 0, v_a_5490_);
                    v___x_5495_ = v_reuseFailAlloc_5496_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_5495_;
            }
            64 => {
                if v_isShared_5501_ == 0 {
                    v___x_5503_ = v___x_5500_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_5504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_a_5498_);
                    v___x_5503_ = v_reuseFailAlloc_5504_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_5503_;
            }
            66 => {
                if v_isShared_5509_ == 0 {
                    v___x_5511_ = v___x_5508_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_5512_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_a_5506_);
                    v___x_5511_ = v_reuseFailAlloc_5512_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_5511_;
            }
            68 => {
                return v___x_5520_;
            }
            69 => {
                if v_isShared_5526_ == 0 {
                    v___x_5528_ = v___x_5525_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_5529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_a_5523_);
                    v___x_5528_ = v_reuseFailAlloc_5529_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_5528_;
            }
            71 => {
                if v_isShared_5547_ == 0 {
                    v___x_5549_ = v___x_5546_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_5550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_a_5544_);
                    v___x_5549_ = v_reuseFailAlloc_5550_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_5549_;
            }
            73 => {
                if v_isShared_5555_ == 0 {
                    v___x_5557_ = v___x_5554_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_5558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_a_5552_);
                    v___x_5557_ = v_reuseFailAlloc_5558_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                return v___x_5557_;
            }
            75 => {
                if v_isShared_5563_ == 0 {
                    v___x_5565_ = v___x_5562_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_5566_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_a_5560_);
                    v___x_5565_ = v_reuseFailAlloc_5566_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                return v___x_5565_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(
    mut v_e_5568_: *mut crate::leanh::LeanObject,
    mut v_xs_5569_: *mut crate::leanh::LeanObject,
    mut v_a_5570_: u8,
    mut v_a_5571_: *mut crate::leanh::LeanObject,
    mut v_as_5572_: *mut crate::leanh::LeanObject,
    mut v_sz_5573_: usize,
    mut v_i_5574_: usize,
    mut v_b_5575_: *mut crate::leanh::LeanObject,
    mut v___y_5576_: *mut crate::leanh::LeanObject,
    mut v___y_5577_: *mut crate::leanh::LeanObject,
    mut v___y_5578_: *mut crate::leanh::LeanObject,
    mut v___y_5579_: *mut crate::leanh::LeanObject,
    mut v___y_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
    mut v___y_5583_: *mut crate::leanh::LeanObject,
    mut v___y_5584_: *mut crate::leanh::LeanObject,
    mut v___y_5585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5587_: u8 = 0;
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5596_: u8 = 0;
    let mut v___x_5597_: u8 = 0;
    let mut v___x_5598_: u8 = 0;
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5603_: u8 = 0;
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5613_: u8 = 0;
    let mut v_a_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5621_: u8 = 0;
    let mut v_isSharedCheck_5622_: u8 = 0;
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: usize = 0;
    let mut v___x_5625_: usize = 0;
    let mut v_a_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5630_: u8 = 0;
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5587_ = lean_usize_dec_lt(v_i_5574_, v_sz_5573_);
                if v___x_5587_ == 0 {
                    crate::leanh::lean_dec_ref(v_a_5571_);
                    crate::leanh::lean_dec_ref(v_e_5568_);
                    v___x_5588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5588_, 0, v_b_5575_);
                    return v___x_5588_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5575_);
                    v_a_5589_ = lean_array_uget_borrowed(v_as_5572_, v_i_5574_);
                    crate::leanh::lean_inc(v_a_5589_);
                    crate::leanh::lean_inc_ref(v_e_5568_);
                    v___x_5590_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_5568_, v_a_5589_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, v___y_5585_);
                    if crate::leanh::lean_obj_tag(v___x_5590_) == 0 {
                        v_a_5591_ = crate::leanh::lean_ctor_get(v___x_5590_, 0);
                        crate::leanh::lean_inc(v_a_5591_);
                        crate::leanh::lean_dec_ref_known(v___x_5590_, 1);
                        v___x_5592_ = crate::leanh::lean_box(0);
                        if crate::leanh::lean_obj_tag(v_a_5591_) == 1 {
                            crate::leanh::lean_dec_ref(v_e_5568_);
                            v_val_5593_ = crate::leanh::lean_ctor_get(v_a_5591_, 0);
                            v_isSharedCheck_5622_ =
                                (!crate::leanh::lean_is_exclusive(v_a_5591_)) as u8;
                            if v_isSharedCheck_5622_ == 0 {
                                v___x_5595_ = v_a_5591_;
                                v_isShared_5596_ = v_isSharedCheck_5622_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_5593_);
                                crate::leanh::lean_dec(v_a_5591_);
                                v___x_5595_ = crate::leanh::lean_box(0);
                                v_isShared_5596_ = v_isSharedCheck_5622_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5591_);
                            v___x_5623_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0;
                            v___x_5624_ = 1usize;
                            v___x_5625_ = lean_usize_add(v_i_5574_, v___x_5624_);
                            v_i_5574_ = v___x_5625_;
                            v_b_5575_ = v___x_5623_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_5571_);
                        crate::leanh::lean_dec_ref(v_e_5568_);
                        v_a_5627_ = crate::leanh::lean_ctor_get(v___x_5590_, 0);
                        v_isSharedCheck_5634_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5590_)) as u8;
                        if v_isSharedCheck_5634_ == 0 {
                            v___x_5629_ = v___x_5590_;
                            v_isShared_5630_ = v_isSharedCheck_5634_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5627_);
                            crate::leanh::lean_dec(v___x_5590_);
                            v___x_5629_ = crate::leanh::lean_box(0);
                            v_isShared_5630_ = v_isSharedCheck_5634_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5597_ = 0;
                v___x_5598_ = 1;
                v___x_5599_ = l_Lean_Meta_mkLambdaFVars(
                    v_xs_5569_,
                    v_val_5593_,
                    v___x_5597_,
                    v_a_5570_,
                    v___x_5597_,
                    v_a_5570_,
                    v___x_5598_,
                    v___y_5582_,
                    v___y_5583_,
                    v___y_5584_,
                    v___y_5585_,
                );
                if crate::leanh::lean_obj_tag(v___x_5599_) == 0 {
                    v_a_5600_ = crate::leanh::lean_ctor_get(v___x_5599_, 0);
                    v_isSharedCheck_5613_ = (!crate::leanh::lean_is_exclusive(v___x_5599_)) as u8;
                    if v_isSharedCheck_5613_ == 0 {
                        v___x_5602_ = v___x_5599_;
                        v_isShared_5603_ = v_isSharedCheck_5613_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5600_);
                        crate::leanh::lean_dec(v___x_5599_);
                        v___x_5602_ = crate::leanh::lean_box(0);
                        v_isShared_5603_ = v_isSharedCheck_5613_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5595_);
                    crate::leanh::lean_dec_ref(v_a_5571_);
                    v_a_5614_ = crate::leanh::lean_ctor_get(v___x_5599_, 0);
                    v_isSharedCheck_5621_ = (!crate::leanh::lean_is_exclusive(v___x_5599_)) as u8;
                    if v_isSharedCheck_5621_ == 0 {
                        v___x_5616_ = v___x_5599_;
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5614_);
                        crate::leanh::lean_dec(v___x_5599_);
                        v___x_5616_ = crate::leanh::lean_box(0);
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5604_ = l_Lean_Expr_app___override(v_a_5571_, v_a_5600_);
                if v_isShared_5596_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5595_, 0, v___x_5604_);
                    v___x_5606_ = v___x_5595_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5612_, 0, v___x_5604_);
                    v___x_5606_ = v_reuseFailAlloc_5612_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5607_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5607_, 0, v___x_5606_);
                v___x_5608_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5608_, 0, v___x_5607_);
                crate::leanh::lean_ctor_set(v___x_5608_, 1, v___x_5592_);
                if v_isShared_5603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5602_, 0, v___x_5608_);
                    v___x_5610_ = v___x_5602_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5611_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5611_, 0, v___x_5608_);
                    v___x_5610_ = v_reuseFailAlloc_5611_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5610_;
            }
            5 => {
                if v_isShared_5617_ == 0 {
                    v___x_5619_ = v___x_5616_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5620_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
                    v___x_5619_ = v_reuseFailAlloc_5620_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5619_;
            }
            7 => {
                if v_isShared_5630_ == 0 {
                    v___x_5632_ = v___x_5629_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_a_5627_);
                    v___x_5632_ = v_reuseFailAlloc_5633_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(
    mut v_e_5635_: *mut crate::leanh::LeanObject,
    mut v_a_5636_: u8,
    mut v_a_5637_: *mut crate::leanh::LeanObject,
    mut v_xs_5638_: *mut crate::leanh::LeanObject,
    mut v_x_5639_: *mut crate::leanh::LeanObject,
    mut v___y_5640_: *mut crate::leanh::LeanObject,
    mut v___y_5641_: *mut crate::leanh::LeanObject,
    mut v___y_5642_: *mut crate::leanh::LeanObject,
    mut v___y_5643_: *mut crate::leanh::LeanObject,
    mut v___y_5644_: *mut crate::leanh::LeanObject,
    mut v___y_5645_: *mut crate::leanh::LeanObject,
    mut v___y_5646_: *mut crate::leanh::LeanObject,
    mut v___y_5647_: *mut crate::leanh::LeanObject,
    mut v___y_5648_: *mut crate::leanh::LeanObject,
    mut v___y_5649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5653_: usize = 0;
    let mut v___x_5654_: usize = 0;
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5659_: u8 = 0;
    let mut v_fst_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5668_: u8 = 0;
    let mut v_a_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5672_: u8 = 0;
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5651_ = crate::leanh::lean_box(0);
                v___x_5652_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0;
                v_sz_5653_ = lean_array_size(v_xs_5638_);
                v___x_5654_ = 0usize;
                v___x_5655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_5635_, v_xs_5638_, v_a_5636_, v_a_5637_, v_xs_5638_, v_sz_5653_, v___x_5654_, v___x_5652_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
                if crate::leanh::lean_obj_tag(v___x_5655_) == 0 {
                    v_a_5656_ = crate::leanh::lean_ctor_get(v___x_5655_, 0);
                    v_isSharedCheck_5668_ = (!crate::leanh::lean_is_exclusive(v___x_5655_)) as u8;
                    if v_isSharedCheck_5668_ == 0 {
                        v___x_5658_ = v___x_5655_;
                        v_isShared_5659_ = v_isSharedCheck_5668_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5656_);
                        crate::leanh::lean_dec(v___x_5655_);
                        v___x_5658_ = crate::leanh::lean_box(0);
                        v_isShared_5659_ = v_isSharedCheck_5668_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5669_ = crate::leanh::lean_ctor_get(v___x_5655_, 0);
                    v_isSharedCheck_5676_ = (!crate::leanh::lean_is_exclusive(v___x_5655_)) as u8;
                    if v_isSharedCheck_5676_ == 0 {
                        v___x_5671_ = v___x_5655_;
                        v_isShared_5672_ = v_isSharedCheck_5676_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5669_);
                        crate::leanh::lean_dec(v___x_5655_);
                        v___x_5671_ = crate::leanh::lean_box(0);
                        v_isShared_5672_ = v_isSharedCheck_5676_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5660_ = crate::leanh::lean_ctor_get(v_a_5656_, 0);
                crate::leanh::lean_inc(v_fst_5660_);
                crate::leanh::lean_dec(v_a_5656_);
                if crate::leanh::lean_obj_tag(v_fst_5660_) == 0 {
                    if v_isShared_5659_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5658_, 0, v___x_5651_);
                        v___x_5662_ = v___x_5658_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5663_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5663_, 0, v___x_5651_);
                        v___x_5662_ = v_reuseFailAlloc_5663_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5664_ = crate::leanh::lean_ctor_get(v_fst_5660_, 0);
                    crate::leanh::lean_inc(v_val_5664_);
                    crate::leanh::lean_dec_ref_known(v_fst_5660_, 1);
                    if v_isShared_5659_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5658_, 0, v_val_5664_);
                        v___x_5666_ = v___x_5658_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_val_5664_);
                        v___x_5666_ = v_reuseFailAlloc_5667_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5662_;
            }
            3 => {
                return v___x_5666_;
            }
            4 => {
                if v_isShared_5672_ == 0 {
                    v___x_5674_ = v___x_5671_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5675_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
                    v___x_5674_ = v_reuseFailAlloc_5675_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_5677_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_xs_5678_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_a_5679_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_5680_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_as_5681_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_sz_5682_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_i_5683_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_b_5684_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5685_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5686_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5687_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5688_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5689_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5690_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5691_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5692_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5693_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5694_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5695_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_a_110597__boxed_5696_: u8 = 0;
    let mut v_sz_boxed_5697_: usize = 0;
    let mut v_i_boxed_5698_: usize = 0;
    let mut v_res_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_110597__boxed_5696_ = (crate::leanh::lean_unbox(v_a_5679_) as u8);
    v_sz_boxed_5697_ = crate::leanh::lean_unbox_usize(v_sz_5682_);
    crate::leanh::lean_dec(v_sz_5682_);
    v_i_boxed_5698_ = crate::leanh::lean_unbox_usize(v_i_5683_);
    crate::leanh::lean_dec(v_i_5683_);
    v_res_5699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(v_e_5677_, v_xs_5678_, v_a_110597__boxed_5696_, v_a_5680_, v_as_5681_, v_sz_boxed_5697_, v_i_boxed_5698_, v_b_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
    crate::leanh::lean_dec(v___y_5694_);
    crate::leanh::lean_dec_ref(v___y_5693_);
    crate::leanh::lean_dec(v___y_5692_);
    crate::leanh::lean_dec_ref(v___y_5691_);
    crate::leanh::lean_dec(v___y_5690_);
    crate::leanh::lean_dec_ref(v___y_5689_);
    crate::leanh::lean_dec(v___y_5688_);
    crate::leanh::lean_dec_ref(v___y_5687_);
    crate::leanh::lean_dec(v___y_5686_);
    crate::leanh::lean_dec(v___y_5685_);
    crate::leanh::lean_dec_ref(v_as_5681_);
    crate::leanh::lean_dec_ref(v_xs_5678_);
    return v_res_5699_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(
    mut v_e_5700_: *mut crate::leanh::LeanObject,
    mut v_h_5701_: *mut crate::leanh::LeanObject,
    mut v_a_5702_: *mut crate::leanh::LeanObject,
    mut v_a_5703_: *mut crate::leanh::LeanObject,
    mut v_a_5704_: *mut crate::leanh::LeanObject,
    mut v_a_5705_: *mut crate::leanh::LeanObject,
    mut v_a_5706_: *mut crate::leanh::LeanObject,
    mut v_a_5707_: *mut crate::leanh::LeanObject,
    mut v_a_5708_: *mut crate::leanh::LeanObject,
    mut v_a_5709_: *mut crate::leanh::LeanObject,
    mut v_a_5710_: *mut crate::leanh::LeanObject,
    mut v_a_5711_: *mut crate::leanh::LeanObject,
    mut v_a_5712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5713_ =
        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(
            v_e_5700_, v_h_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_,
            v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_,
        );
    crate::leanh::lean_dec(v_a_5711_);
    crate::leanh::lean_dec_ref(v_a_5710_);
    crate::leanh::lean_dec(v_a_5709_);
    crate::leanh::lean_dec_ref(v_a_5708_);
    crate::leanh::lean_dec(v_a_5707_);
    crate::leanh::lean_dec_ref(v_a_5706_);
    crate::leanh::lean_dec(v_a_5705_);
    crate::leanh::lean_dec_ref(v_a_5704_);
    crate::leanh::lean_dec(v_a_5703_);
    crate::leanh::lean_dec(v_a_5702_);
    return v_res_5713_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__0;
    v___x_5716_ = l_Lean_stringToMessageData(v___x_5715_);
    return v___x_5716_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(
    mut v_e_5717_: *mut crate::leanh::LeanObject,
    mut v_xs_5718_: *mut crate::leanh::LeanObject,
    mut v___x_5719_: u8,
    mut v_as_5720_: *mut crate::leanh::LeanObject,
    mut v_sz_5721_: usize,
    mut v_i_5722_: usize,
    mut v_b_5723_: *mut crate::leanh::LeanObject,
    mut v___y_5724_: *mut crate::leanh::LeanObject,
    mut v___y_5725_: *mut crate::leanh::LeanObject,
    mut v___y_5726_: *mut crate::leanh::LeanObject,
    mut v___y_5727_: *mut crate::leanh::LeanObject,
    mut v___y_5728_: *mut crate::leanh::LeanObject,
    mut v___y_5729_: *mut crate::leanh::LeanObject,
    mut v___y_5730_: *mut crate::leanh::LeanObject,
    mut v___y_5731_: *mut crate::leanh::LeanObject,
    mut v___y_5732_: *mut crate::leanh::LeanObject,
    mut v___y_5733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: usize = 0;
    let mut v___x_5738_: usize = 0;
    let mut v___x_5740_: u8 = 0;
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5765_: u8 = 0;
    let mut v___x_5766_: u8 = 0;
    let mut v___x_5767_: u8 = 0;
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5772_: u8 = 0;
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5781_: u8 = 0;
    let mut v_a_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5785_: u8 = 0;
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5789_: u8 = 0;
    let mut v_isSharedCheck_5790_: u8 = 0;
    let mut v_a_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5794_: u8 = 0;
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5798_: u8 = 0;
    let mut v___x_5799_: u8 = 0;
    let mut v_options_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5801_: u8 = 0;
    let mut v_inheritedTraceOptions_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: u8 = 0;
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5814_: u8 = 0;
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5818_: u8 = 0;
    let mut v_a_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5822_: u8 = 0;
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5826_: u8 = 0;
    let mut v_a_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5830_: u8 = 0;
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5834_: u8 = 0;
    let mut v_a_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5838_: u8 = 0;
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5740_ = lean_usize_dec_lt(v_i_5722_, v_sz_5721_);
                if v___x_5740_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_5717_);
                    v___x_5741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5741_, 0, v_b_5723_);
                    return v___x_5741_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5723_);
                    v_a_5742_ = lean_array_uget_borrowed(v_as_5720_, v_i_5722_);
                    crate::leanh::lean_inc(v___y_5733_);
                    crate::leanh::lean_inc_ref(v___y_5732_);
                    crate::leanh::lean_inc(v___y_5731_);
                    crate::leanh::lean_inc_ref(v___y_5730_);
                    crate::leanh::lean_inc(v_a_5742_);
                    v___x_5743_ = lean_infer_type(
                        v_a_5742_,
                        v___y_5730_,
                        v___y_5731_,
                        v___y_5732_,
                        v___y_5733_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5743_) == 0 {
                        v_a_5744_ = crate::leanh::lean_ctor_get(v___x_5743_, 0);
                        crate::leanh::lean_inc_n(v_a_5744_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5743_, 1);
                        v___x_5745_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(v_a_5744_, v___y_5724_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_);
                        if crate::leanh::lean_obj_tag(v___x_5745_) == 0 {
                            v_a_5746_ = crate::leanh::lean_ctor_get(v___x_5745_, 0);
                            crate::leanh::lean_inc(v_a_5746_);
                            crate::leanh::lean_dec_ref_known(v___x_5745_, 1);
                            v___x_5747_ = crate::leanh::lean_box(0);
                            v___x_5748_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0;
                            v___x_5799_ = (crate::leanh::lean_unbox(v_a_5746_) as u8);
                            crate::leanh::lean_dec(v_a_5746_);
                            if v___x_5799_ == 0 {
                                crate::leanh::lean_dec(v_a_5744_);
                                v_a_5736_ = v___x_5748_;
                                state = 1;
                                continue;
                            } else {
                                v_options_5800_ = crate::leanh::lean_ctor_get(v___y_5732_, 2);
                                v_hasTrace_5801_ = crate::leanh::lean_ctor_get_uint8(
                                    v_options_5800_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                );
                                if v_hasTrace_5801_ == 0 {
                                    crate::leanh::lean_dec(v_a_5744_);
                                    v___y_5750_ = v___y_5724_;
                                    v___y_5751_ = v___y_5725_;
                                    v___y_5752_ = v___y_5726_;
                                    v___y_5753_ = v___y_5727_;
                                    v___y_5754_ = v___y_5728_;
                                    v___y_5755_ = v___y_5729_;
                                    v___y_5756_ = v___y_5730_;
                                    v___y_5757_ = v___y_5731_;
                                    v___y_5758_ = v___y_5732_;
                                    v___y_5759_ = v___y_5733_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_inheritedTraceOptions_5802_ =
                                        crate::leanh::lean_ctor_get(v___y_5732_, 13);
                                    v___x_5803_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3;
                                    v___x_5804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
                                    v___x_5805_ =
                                        l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                            v_inheritedTraceOptions_5802_,
                                            v_options_5800_,
                                            v___x_5804_,
                                        );
                                    if v___x_5805_ == 0 {
                                        crate::leanh::lean_dec(v_a_5744_);
                                        v___y_5750_ = v___y_5724_;
                                        v___y_5751_ = v___y_5725_;
                                        v___y_5752_ = v___y_5726_;
                                        v___y_5753_ = v___y_5727_;
                                        v___y_5754_ = v___y_5728_;
                                        v___y_5755_ = v___y_5729_;
                                        v___y_5756_ = v___y_5730_;
                                        v___y_5757_ = v___y_5731_;
                                        v___y_5758_ = v___y_5732_;
                                        v___y_5759_ = v___y_5733_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_5806_ = l_Lean_Meta_Grind_updateLastTag(
                                            v___y_5724_,
                                            v___y_5725_,
                                            v___y_5726_,
                                            v___y_5727_,
                                            v___y_5728_,
                                            v___y_5729_,
                                            v___y_5730_,
                                            v___y_5731_,
                                            v___y_5732_,
                                            v___y_5733_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_5806_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_5806_, 1);
                                            v___x_5807_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___closed__1);
                                            v___x_5808_ = l_Lean_MessageData_ofExpr(v_a_5744_);
                                            v___x_5809_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_5809_,
                                                0,
                                                v___x_5807_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_5809_,
                                                1,
                                                v___x_5808_,
                                            );
                                            v___x_5810_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v___x_5803_, v___x_5809_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_);
                                            if crate::leanh::lean_obj_tag(v___x_5810_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_5810_, 1);
                                                v___y_5750_ = v___y_5724_;
                                                v___y_5751_ = v___y_5725_;
                                                v___y_5752_ = v___y_5726_;
                                                v___y_5753_ = v___y_5727_;
                                                v___y_5754_ = v___y_5728_;
                                                v___y_5755_ = v___y_5729_;
                                                v___y_5756_ = v___y_5730_;
                                                v___y_5757_ = v___y_5731_;
                                                v___y_5758_ = v___y_5732_;
                                                v___y_5759_ = v___y_5733_;
                                                state = 2;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v_e_5717_);
                                                v_a_5811_ =
                                                    crate::leanh::lean_ctor_get(v___x_5810_, 0);
                                                v_isSharedCheck_5818_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5810_))
                                                        as u8;
                                                if v_isSharedCheck_5818_ == 0 {
                                                    v___x_5813_ = v___x_5810_;
                                                    v_isShared_5814_ = v_isSharedCheck_5818_;
                                                    state = 11;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5811_);
                                                    crate::leanh::lean_dec(v___x_5810_);
                                                    v___x_5813_ = crate::leanh::lean_box(0);
                                                    v_isShared_5814_ = v_isSharedCheck_5818_;
                                                    state = 11;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_5744_);
                                            crate::leanh::lean_dec_ref(v_e_5717_);
                                            v_a_5819_ = crate::leanh::lean_ctor_get(v___x_5806_, 0);
                                            v_isSharedCheck_5826_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5806_))
                                                    as u8;
                                            if v_isSharedCheck_5826_ == 0 {
                                                v___x_5821_ = v___x_5806_;
                                                v_isShared_5822_ = v_isSharedCheck_5826_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5819_);
                                                crate::leanh::lean_dec(v___x_5806_);
                                                v___x_5821_ = crate::leanh::lean_box(0);
                                                v_isShared_5822_ = v_isSharedCheck_5826_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5744_);
                            crate::leanh::lean_dec_ref(v_e_5717_);
                            v_a_5827_ = crate::leanh::lean_ctor_get(v___x_5745_, 0);
                            v_isSharedCheck_5834_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5745_)) as u8;
                            if v_isSharedCheck_5834_ == 0 {
                                v___x_5829_ = v___x_5745_;
                                v_isShared_5830_ = v_isSharedCheck_5834_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5827_);
                                crate::leanh::lean_dec(v___x_5745_);
                                v___x_5829_ = crate::leanh::lean_box(0);
                                v_isShared_5830_ = v_isSharedCheck_5834_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_5717_);
                        v_a_5835_ = crate::leanh::lean_ctor_get(v___x_5743_, 0);
                        v_isSharedCheck_5842_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5743_)) as u8;
                        if v_isSharedCheck_5842_ == 0 {
                            v___x_5837_ = v___x_5743_;
                            v_isShared_5838_ = v_isSharedCheck_5842_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5835_);
                            crate::leanh::lean_dec(v___x_5743_);
                            v___x_5837_ = crate::leanh::lean_box(0);
                            v_isShared_5838_ = v_isSharedCheck_5842_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5737_ = 1usize;
                v___x_5738_ = lean_usize_add(v_i_5722_, v___x_5737_);
                crate::leanh::lean_inc_ref(v_a_5736_);
                v_i_5722_ = v___x_5738_;
                v_b_5723_ = v_a_5736_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v_a_5742_);
                crate::leanh::lean_inc_ref(v_e_5717_);
                v___x_5760_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(v_e_5717_, v_a_5742_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_, v___y_5759_);
                if crate::leanh::lean_obj_tag(v___x_5760_) == 0 {
                    v_a_5761_ = crate::leanh::lean_ctor_get(v___x_5760_, 0);
                    crate::leanh::lean_inc(v_a_5761_);
                    crate::leanh::lean_dec_ref_known(v___x_5760_, 1);
                    if crate::leanh::lean_obj_tag(v_a_5761_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_5717_);
                        v_val_5762_ = crate::leanh::lean_ctor_get(v_a_5761_, 0);
                        v_isSharedCheck_5790_ = (!crate::leanh::lean_is_exclusive(v_a_5761_)) as u8;
                        if v_isSharedCheck_5790_ == 0 {
                            v___x_5764_ = v_a_5761_;
                            v_isShared_5765_ = v_isSharedCheck_5790_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5762_);
                            crate::leanh::lean_dec(v_a_5761_);
                            v___x_5764_ = crate::leanh::lean_box(0);
                            v_isShared_5765_ = v_isSharedCheck_5790_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5761_);
                        v_a_5736_ = v___x_5748_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5717_);
                    v_a_5791_ = crate::leanh::lean_ctor_get(v___x_5760_, 0);
                    v_isSharedCheck_5798_ = (!crate::leanh::lean_is_exclusive(v___x_5760_)) as u8;
                    if v_isSharedCheck_5798_ == 0 {
                        v___x_5793_ = v___x_5760_;
                        v_isShared_5794_ = v_isSharedCheck_5798_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5791_);
                        crate::leanh::lean_dec(v___x_5760_);
                        v___x_5793_ = crate::leanh::lean_box(0);
                        v_isShared_5794_ = v_isSharedCheck_5798_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5766_ = 0;
                v___x_5767_ = 1;
                v___x_5768_ = l_Lean_Meta_mkLambdaFVars(
                    v_xs_5718_,
                    v_val_5762_,
                    v___x_5766_,
                    v___x_5719_,
                    v___x_5766_,
                    v___x_5719_,
                    v___x_5767_,
                    v___y_5756_,
                    v___y_5757_,
                    v___y_5758_,
                    v___y_5759_,
                );
                if crate::leanh::lean_obj_tag(v___x_5768_) == 0 {
                    v_a_5769_ = crate::leanh::lean_ctor_get(v___x_5768_, 0);
                    v_isSharedCheck_5781_ = (!crate::leanh::lean_is_exclusive(v___x_5768_)) as u8;
                    if v_isSharedCheck_5781_ == 0 {
                        v___x_5771_ = v___x_5768_;
                        v_isShared_5772_ = v_isSharedCheck_5781_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5769_);
                        crate::leanh::lean_dec(v___x_5768_);
                        v___x_5771_ = crate::leanh::lean_box(0);
                        v_isShared_5772_ = v_isSharedCheck_5781_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5764_);
                    v_a_5782_ = crate::leanh::lean_ctor_get(v___x_5768_, 0);
                    v_isSharedCheck_5789_ = (!crate::leanh::lean_is_exclusive(v___x_5768_)) as u8;
                    if v_isSharedCheck_5789_ == 0 {
                        v___x_5784_ = v___x_5768_;
                        v_isShared_5785_ = v_isSharedCheck_5789_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5782_);
                        crate::leanh::lean_dec(v___x_5768_);
                        v___x_5784_ = crate::leanh::lean_box(0);
                        v_isShared_5785_ = v_isSharedCheck_5789_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5765_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5764_, 0, v_a_5769_);
                    v___x_5774_ = v___x_5764_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_a_5769_);
                    v___x_5774_ = v_reuseFailAlloc_5780_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5775_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5775_, 0, v___x_5774_);
                v___x_5776_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5776_, 0, v___x_5775_);
                crate::leanh::lean_ctor_set(v___x_5776_, 1, v___x_5747_);
                if v_isShared_5772_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5771_, 0, v___x_5776_);
                    v___x_5778_ = v___x_5771_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5779_, 0, v___x_5776_);
                    v___x_5778_ = v_reuseFailAlloc_5779_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5778_;
            }
            7 => {
                if v_isShared_5785_ == 0 {
                    v___x_5787_ = v___x_5784_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5788_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5788_, 0, v_a_5782_);
                    v___x_5787_ = v_reuseFailAlloc_5788_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5787_;
            }
            9 => {
                if v_isShared_5794_ == 0 {
                    v___x_5796_ = v___x_5793_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5797_, 0, v_a_5791_);
                    v___x_5796_ = v_reuseFailAlloc_5797_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5796_;
            }
            11 => {
                if v_isShared_5814_ == 0 {
                    v___x_5816_ = v___x_5813_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_a_5811_);
                    v___x_5816_ = v_reuseFailAlloc_5817_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5816_;
            }
            13 => {
                if v_isShared_5822_ == 0 {
                    v___x_5824_ = v___x_5821_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5825_, 0, v_a_5819_);
                    v___x_5824_ = v_reuseFailAlloc_5825_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5824_;
            }
            15 => {
                if v_isShared_5830_ == 0 {
                    v___x_5832_ = v___x_5829_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5833_, 0, v_a_5827_);
                    v___x_5832_ = v_reuseFailAlloc_5833_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5832_;
            }
            17 => {
                if v_isShared_5838_ == 0 {
                    v___x_5840_ = v___x_5837_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 0, v_a_5835_);
                    v___x_5840_ = v_reuseFailAlloc_5841_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_5843_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_xs_5844_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_5845_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_as_5846_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_sz_5847_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_i_5848_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_b_5849_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_5850_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5851_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5852_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5853_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5854_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5855_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5856_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5857_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5858_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5859_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5860_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_30241__boxed_5861_: u8 = 0;
    let mut v_sz_boxed_5862_: usize = 0;
    let mut v_i_boxed_5863_: usize = 0;
    let mut v_res_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_30241__boxed_5861_ = (crate::leanh::lean_unbox(v___x_5845_) as u8);
    v_sz_boxed_5862_ = crate::leanh::lean_unbox_usize(v_sz_5847_);
    crate::leanh::lean_dec(v_sz_5847_);
    v_i_boxed_5863_ = crate::leanh::lean_unbox_usize(v_i_5848_);
    crate::leanh::lean_dec(v_i_5848_);
    v_res_5864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_5843_, v_xs_5844_, v___x_30241__boxed_5861_, v_as_5846_, v_sz_boxed_5862_, v_i_boxed_5863_, v_b_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_);
    crate::leanh::lean_dec(v___y_5859_);
    crate::leanh::lean_dec_ref(v___y_5858_);
    crate::leanh::lean_dec(v___y_5857_);
    crate::leanh::lean_dec_ref(v___y_5856_);
    crate::leanh::lean_dec(v___y_5855_);
    crate::leanh::lean_dec_ref(v___y_5854_);
    crate::leanh::lean_dec(v___y_5853_);
    crate::leanh::lean_dec_ref(v___y_5852_);
    crate::leanh::lean_dec(v___y_5851_);
    crate::leanh::lean_dec(v___y_5850_);
    crate::leanh::lean_dec_ref(v_as_5846_);
    crate::leanh::lean_dec_ref(v_xs_5844_);
    return v_res_5864_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(
    mut v_e_5865_: *mut crate::leanh::LeanObject,
    mut v___x_5866_: u8,
    mut v_xs_5867_: *mut crate::leanh::LeanObject,
    mut v_x_5868_: *mut crate::leanh::LeanObject,
    mut v___y_5869_: *mut crate::leanh::LeanObject,
    mut v___y_5870_: *mut crate::leanh::LeanObject,
    mut v___y_5871_: *mut crate::leanh::LeanObject,
    mut v___y_5872_: *mut crate::leanh::LeanObject,
    mut v___y_5873_: *mut crate::leanh::LeanObject,
    mut v___y_5874_: *mut crate::leanh::LeanObject,
    mut v___y_5875_: *mut crate::leanh::LeanObject,
    mut v___y_5876_: *mut crate::leanh::LeanObject,
    mut v___y_5877_: *mut crate::leanh::LeanObject,
    mut v___y_5878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5882_: usize = 0;
    let mut v___x_5883_: usize = 0;
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5888_: u8 = 0;
    let mut v_fst_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5897_: u8 = 0;
    let mut v_a_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5901_: u8 = 0;
    let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5880_ = crate::leanh::lean_box(0);
                v___x_5881_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0;
                v_sz_5882_ = lean_array_size(v_xs_5867_);
                v___x_5883_ = 0usize;
                v___x_5884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(v_e_5865_, v_xs_5867_, v___x_5866_, v_xs_5867_, v_sz_5882_, v___x_5883_, v___x_5881_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_);
                if crate::leanh::lean_obj_tag(v___x_5884_) == 0 {
                    v_a_5885_ = crate::leanh::lean_ctor_get(v___x_5884_, 0);
                    v_isSharedCheck_5897_ = (!crate::leanh::lean_is_exclusive(v___x_5884_)) as u8;
                    if v_isSharedCheck_5897_ == 0 {
                        v___x_5887_ = v___x_5884_;
                        v_isShared_5888_ = v_isSharedCheck_5897_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5885_);
                        crate::leanh::lean_dec(v___x_5884_);
                        v___x_5887_ = crate::leanh::lean_box(0);
                        v_isShared_5888_ = v_isSharedCheck_5897_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5898_ = crate::leanh::lean_ctor_get(v___x_5884_, 0);
                    v_isSharedCheck_5905_ = (!crate::leanh::lean_is_exclusive(v___x_5884_)) as u8;
                    if v_isSharedCheck_5905_ == 0 {
                        v___x_5900_ = v___x_5884_;
                        v_isShared_5901_ = v_isSharedCheck_5905_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5898_);
                        crate::leanh::lean_dec(v___x_5884_);
                        v___x_5900_ = crate::leanh::lean_box(0);
                        v_isShared_5901_ = v_isSharedCheck_5905_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5889_ = crate::leanh::lean_ctor_get(v_a_5885_, 0);
                crate::leanh::lean_inc(v_fst_5889_);
                crate::leanh::lean_dec(v_a_5885_);
                if crate::leanh::lean_obj_tag(v_fst_5889_) == 0 {
                    if v_isShared_5888_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5887_, 0, v___x_5880_);
                        v___x_5891_ = v___x_5887_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5892_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5892_, 0, v___x_5880_);
                        v___x_5891_ = v_reuseFailAlloc_5892_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5893_ = crate::leanh::lean_ctor_get(v_fst_5889_, 0);
                    crate::leanh::lean_inc(v_val_5893_);
                    crate::leanh::lean_dec_ref_known(v_fst_5889_, 1);
                    if v_isShared_5888_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5887_, 0, v_val_5893_);
                        v___x_5895_ = v___x_5887_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5896_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5896_, 0, v_val_5893_);
                        v___x_5895_ = v_reuseFailAlloc_5896_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5891_;
            }
            3 => {
                return v___x_5895_;
            }
            4 => {
                if v_isShared_5901_ == 0 {
                    v___x_5903_ = v___x_5900_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5904_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5904_, 0, v_a_5898_);
                    v___x_5903_ = v_reuseFailAlloc_5904_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(
    mut v_e_5906_: *mut crate::leanh::LeanObject,
    mut v___x_5907_: *mut crate::leanh::LeanObject,
    mut v_xs_5908_: *mut crate::leanh::LeanObject,
    mut v_x_5909_: *mut crate::leanh::LeanObject,
    mut v___y_5910_: *mut crate::leanh::LeanObject,
    mut v___y_5911_: *mut crate::leanh::LeanObject,
    mut v___y_5912_: *mut crate::leanh::LeanObject,
    mut v___y_5913_: *mut crate::leanh::LeanObject,
    mut v___y_5914_: *mut crate::leanh::LeanObject,
    mut v___y_5915_: *mut crate::leanh::LeanObject,
    mut v___y_5916_: *mut crate::leanh::LeanObject,
    mut v___y_5917_: *mut crate::leanh::LeanObject,
    mut v___y_5918_: *mut crate::leanh::LeanObject,
    mut v___y_5919_: *mut crate::leanh::LeanObject,
    mut v___y_5920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_30493__boxed_5921_: u8 = 0;
    let mut v_res_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_30493__boxed_5921_ = (crate::leanh::lean_unbox(v___x_5907_) as u8);
    v_res_5922_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(v_e_5906_, v___x_30493__boxed_5921_, v_xs_5908_, v_x_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_);
    crate::leanh::lean_dec(v___y_5919_);
    crate::leanh::lean_dec_ref(v___y_5918_);
    crate::leanh::lean_dec(v___y_5917_);
    crate::leanh::lean_dec_ref(v___y_5916_);
    crate::leanh::lean_dec(v___y_5915_);
    crate::leanh::lean_dec_ref(v___y_5914_);
    crate::leanh::lean_dec(v___y_5913_);
    crate::leanh::lean_dec_ref(v___y_5912_);
    crate::leanh::lean_dec(v___y_5911_);
    crate::leanh::lean_dec(v___y_5910_);
    crate::leanh::lean_dec_ref(v_x_5909_);
    crate::leanh::lean_dec_ref(v_xs_5908_);
    return v_res_5922_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(
    mut v_e_5923_: *mut crate::leanh::LeanObject,
    mut v_a_5924_: *mut crate::leanh::LeanObject,
    mut v_a_5925_: *mut crate::leanh::LeanObject,
    mut v_a_5926_: *mut crate::leanh::LeanObject,
    mut v_a_5927_: *mut crate::leanh::LeanObject,
    mut v_a_5928_: *mut crate::leanh::LeanObject,
    mut v_a_5929_: *mut crate::leanh::LeanObject,
    mut v_a_5930_: *mut crate::leanh::LeanObject,
    mut v_a_5931_: *mut crate::leanh::LeanObject,
    mut v_a_5932_: *mut crate::leanh::LeanObject,
    mut v_a_5933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5939_: u8 = 0;
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: u8 = 0;
    let mut v_arg_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: u8 = 0;
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: u8 = 0;
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5955_: u8 = 0;
    let mut v_a_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5959_: u8 = 0;
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_5923_);
                v___x_5935_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_5923_, v_a_5931_);
                if crate::leanh::lean_obj_tag(v___x_5935_) == 0 {
                    v_a_5936_ = crate::leanh::lean_ctor_get(v___x_5935_, 0);
                    v_isSharedCheck_5955_ = (!crate::leanh::lean_is_exclusive(v___x_5935_)) as u8;
                    if v_isSharedCheck_5955_ == 0 {
                        v___x_5938_ = v___x_5935_;
                        v_isShared_5939_ = v_isSharedCheck_5955_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5936_);
                        crate::leanh::lean_dec(v___x_5935_);
                        v___x_5938_ = crate::leanh::lean_box(0);
                        v_isShared_5939_ = v_isSharedCheck_5955_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5923_);
                    v_a_5956_ = crate::leanh::lean_ctor_get(v___x_5935_, 0);
                    v_isSharedCheck_5963_ = (!crate::leanh::lean_is_exclusive(v___x_5935_)) as u8;
                    if v_isSharedCheck_5963_ == 0 {
                        v___x_5958_ = v___x_5935_;
                        v_isShared_5959_ = v_isSharedCheck_5963_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5956_);
                        crate::leanh::lean_dec(v___x_5935_);
                        v___x_5958_ = crate::leanh::lean_box(0);
                        v_isShared_5959_ = v_isSharedCheck_5963_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5945_ = l_Lean_Expr_cleanupAnnotations(v_a_5936_);
                v___x_5946_ = l_Lean_Expr_isApp(v___x_5945_);
                if v___x_5946_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5945_);
                    crate::leanh::lean_dec_ref(v_e_5923_);
                    state = 2;
                    continue;
                } else {
                    v_arg_5947_ = crate::leanh::lean_ctor_get(v___x_5945_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5947_);
                    v___x_5948_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5945_);
                    v___x_5949_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4;
                    v___x_5950_ = l_Lean_Expr_isConstOf(v___x_5948_, v___x_5949_);
                    crate::leanh::lean_dec_ref(v___x_5948_);
                    if v___x_5950_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_5947_);
                        crate::leanh::lean_dec_ref(v_e_5923_);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_5938_);
                        v___x_5951_ = crate::leanh::lean_box((v___x_5950_) as usize);
                        v___f_5952_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed as *mut core::ffi::c_void, 15, 2);
                        crate::leanh::lean_closure_set(v___f_5952_, 0, v_e_5923_);
                        crate::leanh::lean_closure_set(v___f_5952_, 1, v___x_5951_);
                        v___x_5953_ = 0;
                        v___x_5954_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(v_arg_5947_, v___f_5952_, v___x_5953_, v___x_5953_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_, v_a_5933_);
                        return v___x_5954_;
                    }
                }
            }
            2 => {
                v___x_5941_ = crate::leanh::lean_box(0);
                if v_isShared_5939_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5938_, 0, v___x_5941_);
                    v___x_5943_ = v___x_5938_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5944_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 0, v___x_5941_);
                    v___x_5943_ = v_reuseFailAlloc_5944_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5943_;
            }
            4 => {
                if v_isShared_5959_ == 0 {
                    v___x_5961_ = v___x_5958_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5962_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_a_5956_);
                    v___x_5961_ = v_reuseFailAlloc_5962_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(
    mut v_e_5964_: *mut crate::leanh::LeanObject,
    mut v_a_5965_: *mut crate::leanh::LeanObject,
    mut v_a_5966_: *mut crate::leanh::LeanObject,
    mut v_a_5967_: *mut crate::leanh::LeanObject,
    mut v_a_5968_: *mut crate::leanh::LeanObject,
    mut v_a_5969_: *mut crate::leanh::LeanObject,
    mut v_a_5970_: *mut crate::leanh::LeanObject,
    mut v_a_5971_: *mut crate::leanh::LeanObject,
    mut v_a_5972_: *mut crate::leanh::LeanObject,
    mut v_a_5973_: *mut crate::leanh::LeanObject,
    mut v_a_5974_: *mut crate::leanh::LeanObject,
    mut v_a_5975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5976_ =
        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(
            v_e_5964_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_,
            v_a_5972_, v_a_5973_, v_a_5974_,
        );
    crate::leanh::lean_dec(v_a_5974_);
    crate::leanh::lean_dec_ref(v_a_5973_);
    crate::leanh::lean_dec(v_a_5972_);
    crate::leanh::lean_dec_ref(v_a_5971_);
    crate::leanh::lean_dec(v_a_5970_);
    crate::leanh::lean_dec_ref(v_a_5969_);
    crate::leanh::lean_dec(v_a_5968_);
    crate::leanh::lean_dec_ref(v_a_5967_);
    crate::leanh::lean_dec(v_a_5966_);
    crate::leanh::lean_dec(v_a_5965_);
    return v_res_5976_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(
    mut v_e_5977_: *mut crate::leanh::LeanObject,
    mut v_a_5978_: *mut crate::leanh::LeanObject,
    mut v_a_5979_: *mut crate::leanh::LeanObject,
    mut v_a_5980_: *mut crate::leanh::LeanObject,
    mut v_a_5981_: *mut crate::leanh::LeanObject,
    mut v_a_5982_: *mut crate::leanh::LeanObject,
    mut v_a_5983_: *mut crate::leanh::LeanObject,
    mut v_a_5984_: *mut crate::leanh::LeanObject,
    mut v_a_5985_: *mut crate::leanh::LeanObject,
    mut v_a_5986_: *mut crate::leanh::LeanObject,
    mut v_a_5987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5993_: u8 = 0;
    let mut v_ctor_5994_: u8 = 0;
    let mut v_interpreted_5995_: u8 = 0;
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6008_: u8 = 0;
    let mut v_val_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: u8 = 0;
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6026_: u8 = 0;
    let mut v_snd_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: u8 = 0;
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6036_: u8 = 0;
    let mut v_a_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6044_: u8 = 0;
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6048_: u8 = 0;
    let mut v_a_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6052_: u8 = 0;
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6056_: u8 = 0;
    let mut v_isSharedCheck_6057_: u8 = 0;
    let mut v_a_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6061_: u8 = 0;
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_5977_);
                v___x_5989_ = l_Lean_Meta_Grind_getRootENode___redArg(
                    v_e_5977_, v_a_5978_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_,
                );
                if crate::leanh::lean_obj_tag(v___x_5989_) == 0 {
                    v_a_5990_ = crate::leanh::lean_ctor_get(v___x_5989_, 0);
                    v_isSharedCheck_6057_ = (!crate::leanh::lean_is_exclusive(v___x_5989_)) as u8;
                    if v_isSharedCheck_6057_ == 0 {
                        v___x_5992_ = v___x_5989_;
                        v_isShared_5993_ = v_isSharedCheck_6057_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5990_);
                        crate::leanh::lean_dec(v___x_5989_);
                        v___x_5992_ = crate::leanh::lean_box(0);
                        v_isShared_5993_ = v_isSharedCheck_6057_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5977_);
                    v_a_6058_ = crate::leanh::lean_ctor_get(v___x_5989_, 0);
                    v_isSharedCheck_6065_ = (!crate::leanh::lean_is_exclusive(v___x_5989_)) as u8;
                    if v_isSharedCheck_6065_ == 0 {
                        v___x_6060_ = v___x_5989_;
                        v_isShared_6061_ = v_isSharedCheck_6065_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6058_);
                        crate::leanh::lean_dec(v___x_5989_);
                        v___x_6060_ = crate::leanh::lean_box(0);
                        v_isShared_6061_ = v_isSharedCheck_6065_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_ctor_5994_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5990_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 2) as u32,
                );
                if v_ctor_5994_ == 0 {
                    v_interpreted_5995_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5990_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 12 + 1) as u32,
                    );
                    if v_interpreted_5995_ == 0 {
                        crate::leanh::lean_dec(v_a_5990_);
                        if v_isShared_5993_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5992_, 0, v_e_5977_);
                            v___x_5997_ = v___x_5992_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5998_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5998_, 0, v_e_5977_);
                            v___x_5997_ = v_reuseFailAlloc_5998_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_5977_);
                        v_self_5999_ = crate::leanh::lean_ctor_get(v_a_5990_, 0);
                        crate::leanh::lean_inc_ref(v_self_5999_);
                        crate::leanh::lean_dec(v_a_5990_);
                        if v_isShared_5993_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5992_, 0, v_self_5999_);
                            v___x_6001_ = v___x_5992_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6002_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6002_, 0, v_self_5999_);
                            v___x_6001_ = v_reuseFailAlloc_6002_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5992_);
                    crate::leanh::lean_dec_ref(v_e_5977_);
                    v_self_6003_ = crate::leanh::lean_ctor_get(v_a_5990_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_6003_, 2);
                    crate::leanh::lean_dec(v_a_5990_);
                    v___x_6004_ = l_Lean_Meta_isConstructorApp_x3f(
                        v_self_6003_,
                        v_a_5984_,
                        v_a_5985_,
                        v_a_5986_,
                        v_a_5987_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6004_) == 0 {
                        v_a_6005_ = crate::leanh::lean_ctor_get(v___x_6004_, 0);
                        v_isSharedCheck_6048_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6004_)) as u8;
                        if v_isSharedCheck_6048_ == 0 {
                            v___x_6007_ = v___x_6004_;
                            v_isShared_6008_ = v_isSharedCheck_6048_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6005_);
                            crate::leanh::lean_dec(v___x_6004_);
                            v___x_6007_ = crate::leanh::lean_box(0);
                            v_isShared_6008_ = v_isSharedCheck_6048_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_self_6003_);
                        v_a_6049_ = crate::leanh::lean_ctor_get(v___x_6004_, 0);
                        v_isSharedCheck_6056_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6004_)) as u8;
                        if v_isSharedCheck_6056_ == 0 {
                            v___x_6051_ = v___x_6004_;
                            v_isShared_6052_ = v_isSharedCheck_6056_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6049_);
                            crate::leanh::lean_dec(v___x_6004_);
                            v___x_6051_ = crate::leanh::lean_box(0);
                            v_isShared_6052_ = v_isSharedCheck_6056_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5997_;
            }
            3 => {
                return v___x_6001_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_6005_) == 1 {
                    crate::leanh::lean_del_object(v___x_6007_);
                    v_val_6009_ = crate::leanh::lean_ctor_get(v_a_6005_, 0);
                    crate::leanh::lean_inc(v_val_6009_);
                    crate::leanh::lean_dec_ref_known(v_a_6005_, 1);
                    v_numParams_6010_ = crate::leanh::lean_ctor_get(v_val_6009_, 3);
                    crate::leanh::lean_inc(v_numParams_6010_);
                    v_numFields_6011_ = crate::leanh::lean_ctor_get(v_val_6009_, 4);
                    crate::leanh::lean_inc(v_numFields_6011_);
                    crate::leanh::lean_dec(v_val_6009_);
                    v_nargs_6012_ = l_Lean_Expr_getAppNumArgs(v_self_6003_);
                    v___x_6013_ = lean_nat_add(v_numParams_6010_, v_numFields_6011_);
                    crate::leanh::lean_dec(v_numFields_6011_);
                    v_dummy_6014_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0);
                    crate::leanh::lean_inc(v_nargs_6012_);
                    v___x_6015_ = lean_mk_array(v_nargs_6012_, v_dummy_6014_);
                    v___x_6016_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6017_ = lean_nat_sub(v_nargs_6012_, v___x_6016_);
                    crate::leanh::lean_dec(v_nargs_6012_);
                    crate::leanh::lean_inc_ref(v_self_6003_);
                    v___x_6018_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_self_6003_,
                        v___x_6015_,
                        v___x_6017_,
                    );
                    v___x_6019_ = 0;
                    v___x_6020_ = crate::leanh::lean_box((v___x_6019_) as usize);
                    v___x_6021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6021_, 0, v___x_6018_);
                    crate::leanh::lean_ctor_set(v___x_6021_, 1, v___x_6020_);
                    v___x_6022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v___x_6013_, v_ctor_5994_, v_numParams_6010_, v___x_6021_, v_a_5978_, v_a_5979_, v_a_5980_, v_a_5981_, v_a_5982_, v_a_5983_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_);
                    crate::leanh::lean_dec(v___x_6013_);
                    if crate::leanh::lean_obj_tag(v___x_6022_) == 0 {
                        v_a_6023_ = crate::leanh::lean_ctor_get(v___x_6022_, 0);
                        v_isSharedCheck_6036_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6022_)) as u8;
                        if v_isSharedCheck_6036_ == 0 {
                            v___x_6025_ = v___x_6022_;
                            v_isShared_6026_ = v_isSharedCheck_6036_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6023_);
                            crate::leanh::lean_dec(v___x_6022_);
                            v___x_6025_ = crate::leanh::lean_box(0);
                            v_isShared_6026_ = v_isSharedCheck_6036_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_self_6003_);
                        v_a_6037_ = crate::leanh::lean_ctor_get(v___x_6022_, 0);
                        v_isSharedCheck_6044_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6022_)) as u8;
                        if v_isSharedCheck_6044_ == 0 {
                            v___x_6039_ = v___x_6022_;
                            v_isShared_6040_ = v_isSharedCheck_6044_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6037_);
                            crate::leanh::lean_dec(v___x_6022_);
                            v___x_6039_ = crate::leanh::lean_box(0);
                            v_isShared_6040_ = v_isSharedCheck_6044_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6005_);
                    if v_isShared_6008_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6007_, 0, v_self_6003_);
                        v___x_6046_ = v___x_6007_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_6047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6047_, 0, v_self_6003_);
                        v___x_6046_ = v_reuseFailAlloc_6047_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v_snd_6027_ = crate::leanh::lean_ctor_get(v_a_6023_, 1);
                v___x_6028_ = (crate::leanh::lean_unbox(v_snd_6027_) as u8);
                if v___x_6028_ == 0 {
                    crate::leanh::lean_dec(v_a_6023_);
                    if v_isShared_6026_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6025_, 0, v_self_6003_);
                        v___x_6030_ = v___x_6025_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6031_, 0, v_self_6003_);
                        v___x_6030_ = v_reuseFailAlloc_6031_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6025_);
                    v_fst_6032_ = crate::leanh::lean_ctor_get(v_a_6023_, 0);
                    crate::leanh::lean_inc(v_fst_6032_);
                    crate::leanh::lean_dec(v_a_6023_);
                    v___x_6033_ = l_Lean_Expr_getAppFn(v_self_6003_);
                    crate::leanh::lean_dec_ref(v_self_6003_);
                    v___x_6034_ = l_Lean_mkAppN(v___x_6033_, v_fst_6032_);
                    crate::leanh::lean_dec(v_fst_6032_);
                    v___x_6035_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_6034_, v_a_5983_);
                    return v___x_6035_;
                }
            }
            6 => {
                return v___x_6030_;
            }
            7 => {
                if v_isShared_6040_ == 0 {
                    v___x_6042_ = v___x_6039_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
                    v___x_6042_ = v_reuseFailAlloc_6043_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6042_;
            }
            9 => {
                return v___x_6046_;
            }
            10 => {
                if v_isShared_6052_ == 0 {
                    v___x_6054_ = v___x_6051_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6055_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 0, v_a_6049_);
                    v___x_6054_ = v_reuseFailAlloc_6055_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6054_;
            }
            12 => {
                if v_isShared_6061_ == 0 {
                    v___x_6063_ = v___x_6060_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_a_6058_);
                    v___x_6063_ = v_reuseFailAlloc_6064_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(
    mut v_upperBound_6066_: *mut crate::leanh::LeanObject,
    mut v___x_6067_: u8,
    mut v_a_6068_: *mut crate::leanh::LeanObject,
    mut v_b_6069_: *mut crate::leanh::LeanObject,
    mut v___y_6070_: *mut crate::leanh::LeanObject,
    mut v___y_6071_: *mut crate::leanh::LeanObject,
    mut v___y_6072_: *mut crate::leanh::LeanObject,
    mut v___y_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
    mut v___y_6077_: *mut crate::leanh::LeanObject,
    mut v___y_6078_: *mut crate::leanh::LeanObject,
    mut v___y_6079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6081_: u8 = 0;
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6087_: u8 = 0;
    let mut v___x_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: u8 = 0;
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6109_: u8 = 0;
    let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6113_: u8 = 0;
    let mut v_isSharedCheck_6114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6081_ = lean_nat_dec_lt(v_a_6068_, v_upperBound_6066_);
                if v___x_6081_ == 0 {
                    crate::leanh::lean_dec(v_a_6068_);
                    v___x_6082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6082_, 0, v_b_6069_);
                    return v___x_6082_;
                } else {
                    v_fst_6083_ = crate::leanh::lean_ctor_get(v_b_6069_, 0);
                    v_snd_6084_ = crate::leanh::lean_ctor_get(v_b_6069_, 1);
                    v_isSharedCheck_6114_ = (!crate::leanh::lean_is_exclusive(v_b_6069_)) as u8;
                    if v_isSharedCheck_6114_ == 0 {
                        v___x_6086_ = v_b_6069_;
                        v_isShared_6087_ = v_isSharedCheck_6114_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6084_);
                        crate::leanh::lean_inc(v_fst_6083_);
                        crate::leanh::lean_dec(v_b_6069_);
                        v___x_6086_ = crate::leanh::lean_box(0);
                        v_isShared_6087_ = v_isSharedCheck_6114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6088_ = l_Lean_instInhabitedExpr;
                v___x_6089_ = lean_array_get_borrowed(v___x_6088_, v_fst_6083_, v_a_6068_);
                crate::leanh::lean_inc(v___x_6089_);
                v___x_6090_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v___x_6089_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_);
                if crate::leanh::lean_obj_tag(v___x_6090_) == 0 {
                    v_a_6091_ = crate::leanh::lean_ctor_get(v___x_6090_, 0);
                    crate::leanh::lean_inc(v_a_6091_);
                    crate::leanh::lean_dec_ref_known(v___x_6090_, 1);
                    v___x_6097_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v___x_6089_,
                            v_a_6091_,
                        );
                    if v___x_6097_ == 0 {
                        crate::leanh::lean_dec(v_snd_6084_);
                        v___x_6098_ = lean_array_set(v_fst_6083_, v_a_6068_, v_a_6091_);
                        v___x_6099_ = crate::leanh::lean_box((v___x_6067_) as usize);
                        if v_isShared_6087_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6086_, 1, v___x_6099_);
                            crate::leanh::lean_ctor_set(v___x_6086_, 0, v___x_6098_);
                            v___x_6101_ = v___x_6086_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6102_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6102_, 0, v___x_6098_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6102_, 1, v___x_6099_);
                            v___x_6101_ = v_reuseFailAlloc_6102_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6091_);
                        if v_isShared_6087_ == 0 {
                            v___x_6104_ = v___x_6086_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6105_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6105_, 0, v_fst_6083_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6105_, 1, v_snd_6084_);
                            v___x_6104_ = v_reuseFailAlloc_6105_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6086_);
                    crate::leanh::lean_dec(v_snd_6084_);
                    crate::leanh::lean_dec(v_fst_6083_);
                    crate::leanh::lean_dec(v_a_6068_);
                    v_a_6106_ = crate::leanh::lean_ctor_get(v___x_6090_, 0);
                    v_isSharedCheck_6113_ = (!crate::leanh::lean_is_exclusive(v___x_6090_)) as u8;
                    if v_isSharedCheck_6113_ == 0 {
                        v___x_6108_ = v___x_6090_;
                        v_isShared_6109_ = v_isSharedCheck_6113_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6106_);
                        crate::leanh::lean_dec(v___x_6090_);
                        v___x_6108_ = crate::leanh::lean_box(0);
                        v_isShared_6109_ = v_isSharedCheck_6113_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6094_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6095_ = lean_nat_add(v_a_6068_, v___x_6094_);
                crate::leanh::lean_dec(v_a_6068_);
                v_a_6068_ = v___x_6095_;
                v_b_6069_ = v_a_6093_;
                state = 0;
                continue;
            }
            3 => {
                v_a_6093_ = v___x_6101_;
                state = 2;
                continue;
            }
            4 => {
                v_a_6093_ = v___x_6104_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_6109_ == 0 {
                    v___x_6111_ = v___x_6108_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6112_, 0, v_a_6106_);
                    v___x_6111_ = v_reuseFailAlloc_6112_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(
    mut v_upperBound_6115_: *mut crate::leanh::LeanObject,
    mut v___x_6116_: *mut crate::leanh::LeanObject,
    mut v_a_6117_: *mut crate::leanh::LeanObject,
    mut v_b_6118_: *mut crate::leanh::LeanObject,
    mut v___y_6119_: *mut crate::leanh::LeanObject,
    mut v___y_6120_: *mut crate::leanh::LeanObject,
    mut v___y_6121_: *mut crate::leanh::LeanObject,
    mut v___y_6122_: *mut crate::leanh::LeanObject,
    mut v___y_6123_: *mut crate::leanh::LeanObject,
    mut v___y_6124_: *mut crate::leanh::LeanObject,
    mut v___y_6125_: *mut crate::leanh::LeanObject,
    mut v___y_6126_: *mut crate::leanh::LeanObject,
    mut v___y_6127_: *mut crate::leanh::LeanObject,
    mut v___y_6128_: *mut crate::leanh::LeanObject,
    mut v___y_6129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_15840__boxed_6130_: u8 = 0;
    let mut v_res_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15840__boxed_6130_ = (crate::leanh::lean_unbox(v___x_6116_) as u8);
    v_res_6131_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_6115_, v___x_15840__boxed_6130_, v_a_6117_, v_b_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
    crate::leanh::lean_dec(v___y_6128_);
    crate::leanh::lean_dec_ref(v___y_6127_);
    crate::leanh::lean_dec(v___y_6126_);
    crate::leanh::lean_dec_ref(v___y_6125_);
    crate::leanh::lean_dec(v___y_6124_);
    crate::leanh::lean_dec_ref(v___y_6123_);
    crate::leanh::lean_dec(v___y_6122_);
    crate::leanh::lean_dec_ref(v___y_6121_);
    crate::leanh::lean_dec(v___y_6120_);
    crate::leanh::lean_dec(v___y_6119_);
    crate::leanh::lean_dec(v_upperBound_6115_);
    return v_res_6131_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(
    mut v_e_6132_: *mut crate::leanh::LeanObject,
    mut v_a_6133_: *mut crate::leanh::LeanObject,
    mut v_a_6134_: *mut crate::leanh::LeanObject,
    mut v_a_6135_: *mut crate::leanh::LeanObject,
    mut v_a_6136_: *mut crate::leanh::LeanObject,
    mut v_a_6137_: *mut crate::leanh::LeanObject,
    mut v_a_6138_: *mut crate::leanh::LeanObject,
    mut v_a_6139_: *mut crate::leanh::LeanObject,
    mut v_a_6140_: *mut crate::leanh::LeanObject,
    mut v_a_6141_: *mut crate::leanh::LeanObject,
    mut v_a_6142_: *mut crate::leanh::LeanObject,
    mut v_a_6143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6144_ =
        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(
            v_e_6132_, v_a_6133_, v_a_6134_, v_a_6135_, v_a_6136_, v_a_6137_, v_a_6138_, v_a_6139_,
            v_a_6140_, v_a_6141_, v_a_6142_,
        );
    crate::leanh::lean_dec(v_a_6142_);
    crate::leanh::lean_dec_ref(v_a_6141_);
    crate::leanh::lean_dec(v_a_6140_);
    crate::leanh::lean_dec_ref(v_a_6139_);
    crate::leanh::lean_dec(v_a_6138_);
    crate::leanh::lean_dec_ref(v_a_6137_);
    crate::leanh::lean_dec(v_a_6136_);
    crate::leanh::lean_dec_ref(v_a_6135_);
    crate::leanh::lean_dec(v_a_6134_);
    crate::leanh::lean_dec(v_a_6133_);
    return v_res_6144_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(
    mut v_upperBound_6145_: *mut crate::leanh::LeanObject,
    mut v___x_6146_: u8,
    mut v_inst_6147_: *mut crate::leanh::LeanObject,
    mut v_R_6148_: *mut crate::leanh::LeanObject,
    mut v_a_6149_: *mut crate::leanh::LeanObject,
    mut v_b_6150_: *mut crate::leanh::LeanObject,
    mut v_c_6151_: *mut crate::leanh::LeanObject,
    mut v___y_6152_: *mut crate::leanh::LeanObject,
    mut v___y_6153_: *mut crate::leanh::LeanObject,
    mut v___y_6154_: *mut crate::leanh::LeanObject,
    mut v___y_6155_: *mut crate::leanh::LeanObject,
    mut v___y_6156_: *mut crate::leanh::LeanObject,
    mut v___y_6157_: *mut crate::leanh::LeanObject,
    mut v___y_6158_: *mut crate::leanh::LeanObject,
    mut v___y_6159_: *mut crate::leanh::LeanObject,
    mut v___y_6160_: *mut crate::leanh::LeanObject,
    mut v___y_6161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6163_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(v_upperBound_6145_, v___x_6146_, v_a_6149_, v_b_6150_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_);
    return v___x_6163_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_6164_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_6165_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_6166_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_R_6167_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_6168_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_6169_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_c_6170_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_6171_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_6172_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_6173_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_6174_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_6175_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_6176_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6177_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6178_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6179_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6180_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6181_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_16081__boxed_6182_: u8 = 0;
    let mut v_res_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16081__boxed_6182_ = (crate::leanh::lean_unbox(v___x_6165_) as u8);
    v_res_6183_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(v_upperBound_6164_, v___x_16081__boxed_6182_, v_inst_6166_, v_R_6167_, v_a_6168_, v_b_6169_, v_c_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
    crate::leanh::lean_dec(v___y_6180_);
    crate::leanh::lean_dec_ref(v___y_6179_);
    crate::leanh::lean_dec(v___y_6178_);
    crate::leanh::lean_dec_ref(v___y_6177_);
    crate::leanh::lean_dec(v___y_6176_);
    crate::leanh::lean_dec_ref(v___y_6175_);
    crate::leanh::lean_dec(v___y_6174_);
    crate::leanh::lean_dec_ref(v___y_6173_);
    crate::leanh::lean_dec(v___y_6172_);
    crate::leanh::lean_dec(v___y_6171_);
    crate::leanh::lean_dec(v_upperBound_6164_);
    return v_res_6183_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(
    mut v_e_6184_: *mut crate::leanh::LeanObject,
    mut v___y_6185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6187_: u8 = 0;
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6201_: u8 = 0;
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6207_: u8 = 0;
    let mut v_unused_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6187_ = l_Lean_Expr_hasMVar(v_e_6184_);
                if v___x_6187_ == 0 {
                    v___x_6188_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6188_, 0, v_e_6184_);
                    return v___x_6188_;
                } else {
                    v___x_6189_ = lean_st_ref_get(v___y_6185_);
                    v_mctx_6190_ = crate::leanh::lean_ctor_get(v___x_6189_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_6190_);
                    crate::leanh::lean_dec(v___x_6189_);
                    v___x_6191_ = l_Lean_instantiateMVarsCore(v_mctx_6190_, v_e_6184_);
                    v_fst_6192_ = crate::leanh::lean_ctor_get(v___x_6191_, 0);
                    crate::leanh::lean_inc(v_fst_6192_);
                    v_snd_6193_ = crate::leanh::lean_ctor_get(v___x_6191_, 1);
                    crate::leanh::lean_inc(v_snd_6193_);
                    crate::leanh::lean_dec_ref(v___x_6191_);
                    v___x_6194_ = lean_st_ref_take(v___y_6185_);
                    v_cache_6195_ = crate::leanh::lean_ctor_get(v___x_6194_, 1);
                    v_zetaDeltaFVarIds_6196_ = crate::leanh::lean_ctor_get(v___x_6194_, 2);
                    v_postponed_6197_ = crate::leanh::lean_ctor_get(v___x_6194_, 3);
                    v_diag_6198_ = crate::leanh::lean_ctor_get(v___x_6194_, 4);
                    v_isSharedCheck_6207_ = (!crate::leanh::lean_is_exclusive(v___x_6194_)) as u8;
                    if v_isSharedCheck_6207_ == 0 {
                        v_unused_6208_ = crate::leanh::lean_ctor_get(v___x_6194_, 0);
                        crate::leanh::lean_dec(v_unused_6208_);
                        v___x_6200_ = v___x_6194_;
                        v_isShared_6201_ = v_isSharedCheck_6207_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_6198_);
                        crate::leanh::lean_inc(v_postponed_6197_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_6196_);
                        crate::leanh::lean_inc(v_cache_6195_);
                        crate::leanh::lean_dec(v___x_6194_);
                        v___x_6200_ = crate::leanh::lean_box(0);
                        v_isShared_6201_ = v_isSharedCheck_6207_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6200_, 0, v_snd_6193_);
                    v___x_6203_ = v___x_6200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6206_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6206_, 0, v_snd_6193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6206_, 1, v_cache_6195_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6206_,
                        2,
                        v_zetaDeltaFVarIds_6196_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6206_, 3, v_postponed_6197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6206_, 4, v_diag_6198_);
                    v___x_6203_ = v_reuseFailAlloc_6206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6204_ = lean_st_ref_set(v___y_6185_, v___x_6203_);
                v___x_6205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6205_, 0, v_fst_6192_);
                return v___x_6205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg___boxed(
    mut v_e_6209_: *mut crate::leanh::LeanObject,
    mut v___y_6210_: *mut crate::leanh::LeanObject,
    mut v___y_6211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6212_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(
        v_e_6209_,
        v___y_6210_,
    );
    crate::leanh::lean_dec(v___y_6210_);
    return v_res_6212_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(
    mut v_e_6213_: *mut crate::leanh::LeanObject,
    mut v___y_6214_: *mut crate::leanh::LeanObject,
    mut v___y_6215_: *mut crate::leanh::LeanObject,
    mut v___y_6216_: *mut crate::leanh::LeanObject,
    mut v___y_6217_: *mut crate::leanh::LeanObject,
    mut v___y_6218_: *mut crate::leanh::LeanObject,
    mut v___y_6219_: *mut crate::leanh::LeanObject,
    mut v___y_6220_: *mut crate::leanh::LeanObject,
    mut v___y_6221_: *mut crate::leanh::LeanObject,
    mut v___y_6222_: *mut crate::leanh::LeanObject,
    mut v___y_6223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6225_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(
        v_e_6213_,
        v___y_6221_,
    );
    return v___x_6225_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(
    mut v_e_6226_: *mut crate::leanh::LeanObject,
    mut v___y_6227_: *mut crate::leanh::LeanObject,
    mut v___y_6228_: *mut crate::leanh::LeanObject,
    mut v___y_6229_: *mut crate::leanh::LeanObject,
    mut v___y_6230_: *mut crate::leanh::LeanObject,
    mut v___y_6231_: *mut crate::leanh::LeanObject,
    mut v___y_6232_: *mut crate::leanh::LeanObject,
    mut v___y_6233_: *mut crate::leanh::LeanObject,
    mut v___y_6234_: *mut crate::leanh::LeanObject,
    mut v___y_6235_: *mut crate::leanh::LeanObject,
    mut v___y_6236_: *mut crate::leanh::LeanObject,
    mut v___y_6237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6238_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(
        v_e_6226_,
        v___y_6227_,
        v___y_6228_,
        v___y_6229_,
        v___y_6230_,
        v___y_6231_,
        v___y_6232_,
        v___y_6233_,
        v___y_6234_,
        v___y_6235_,
        v___y_6236_,
    );
    crate::leanh::lean_dec(v___y_6236_);
    crate::leanh::lean_dec_ref(v___y_6235_);
    crate::leanh::lean_dec(v___y_6234_);
    crate::leanh::lean_dec_ref(v___y_6233_);
    crate::leanh::lean_dec(v___y_6232_);
    crate::leanh::lean_dec_ref(v___y_6231_);
    crate::leanh::lean_dec(v___y_6230_);
    crate::leanh::lean_dec_ref(v___y_6229_);
    crate::leanh::lean_dec(v___y_6228_);
    crate::leanh::lean_dec(v___y_6227_);
    return v_res_6238_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(
    mut v_k_6239_: *mut crate::leanh::LeanObject,
    mut v___y_6240_: *mut crate::leanh::LeanObject,
    mut v___y_6241_: *mut crate::leanh::LeanObject,
    mut v___y_6242_: *mut crate::leanh::LeanObject,
    mut v___y_6243_: *mut crate::leanh::LeanObject,
    mut v___y_6244_: *mut crate::leanh::LeanObject,
    mut v___y_6245_: *mut crate::leanh::LeanObject,
    mut v___y_6246_: *mut crate::leanh::LeanObject,
    mut v___y_6247_: *mut crate::leanh::LeanObject,
    mut v___y_6248_: *mut crate::leanh::LeanObject,
    mut v___y_6249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_6245_);
    crate::leanh::lean_inc_ref(v___y_6244_);
    crate::leanh::lean_inc(v___y_6243_);
    crate::leanh::lean_inc_ref(v___y_6242_);
    crate::leanh::lean_inc(v___y_6241_);
    crate::leanh::lean_inc(v___y_6240_);
    v___x_6251_ = crate::leanh::lean_apply_11(
        v_k_6239_,
        v___y_6240_,
        v___y_6241_,
        v___y_6242_,
        v___y_6243_,
        v___y_6244_,
        v___y_6245_,
        v___y_6246_,
        v___y_6247_,
        v___y_6248_,
        v___y_6249_,
        crate::leanh::lean_box(0),
    );
    return v___x_6251_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed(
    mut v_k_6252_: *mut crate::leanh::LeanObject,
    mut v___y_6253_: *mut crate::leanh::LeanObject,
    mut v___y_6254_: *mut crate::leanh::LeanObject,
    mut v___y_6255_: *mut crate::leanh::LeanObject,
    mut v___y_6256_: *mut crate::leanh::LeanObject,
    mut v___y_6257_: *mut crate::leanh::LeanObject,
    mut v___y_6258_: *mut crate::leanh::LeanObject,
    mut v___y_6259_: *mut crate::leanh::LeanObject,
    mut v___y_6260_: *mut crate::leanh::LeanObject,
    mut v___y_6261_: *mut crate::leanh::LeanObject,
    mut v___y_6262_: *mut crate::leanh::LeanObject,
    mut v___y_6263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6264_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0(v_k_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_);
    crate::leanh::lean_dec(v___y_6258_);
    crate::leanh::lean_dec_ref(v___y_6257_);
    crate::leanh::lean_dec(v___y_6256_);
    crate::leanh::lean_dec_ref(v___y_6255_);
    crate::leanh::lean_dec(v___y_6254_);
    crate::leanh::lean_dec(v___y_6253_);
    return v_res_6264_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(
    mut v_k_6265_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_6266_: u8,
    mut v___y_6267_: *mut crate::leanh::LeanObject,
    mut v___y_6268_: *mut crate::leanh::LeanObject,
    mut v___y_6269_: *mut crate::leanh::LeanObject,
    mut v___y_6270_: *mut crate::leanh::LeanObject,
    mut v___y_6271_: *mut crate::leanh::LeanObject,
    mut v___y_6272_: *mut crate::leanh::LeanObject,
    mut v___y_6273_: *mut crate::leanh::LeanObject,
    mut v___y_6274_: *mut crate::leanh::LeanObject,
    mut v___y_6275_: *mut crate::leanh::LeanObject,
    mut v___y_6276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6283_: u8 = 0;
    let mut v___x_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_6272_);
                crate::leanh::lean_inc_ref(v___y_6271_);
                crate::leanh::lean_inc(v___y_6270_);
                crate::leanh::lean_inc_ref(v___y_6269_);
                crate::leanh::lean_inc(v___y_6268_);
                crate::leanh::lean_inc(v___y_6267_);
                v___f_6278_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 7);
                crate::leanh::lean_closure_set(v___f_6278_, 0, v_k_6265_);
                crate::leanh::lean_closure_set(v___f_6278_, 1, v___y_6267_);
                crate::leanh::lean_closure_set(v___f_6278_, 2, v___y_6268_);
                crate::leanh::lean_closure_set(v___f_6278_, 3, v___y_6269_);
                crate::leanh::lean_closure_set(v___f_6278_, 4, v___y_6270_);
                crate::leanh::lean_closure_set(v___f_6278_, 5, v___y_6271_);
                crate::leanh::lean_closure_set(v___f_6278_, 6, v___y_6272_);
                v___x_6279_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    crate::leanh::lean_box(0),
                    v_allowLevelAssignments_6266_,
                    v___f_6278_,
                    v___y_6273_,
                    v___y_6274_,
                    v___y_6275_,
                    v___y_6276_,
                );
                if crate::leanh::lean_obj_tag(v___x_6279_) == 0 {
                    return v___x_6279_;
                } else {
                    v_a_6280_ = crate::leanh::lean_ctor_get(v___x_6279_, 0);
                    v_isSharedCheck_6287_ = (!crate::leanh::lean_is_exclusive(v___x_6279_)) as u8;
                    if v_isSharedCheck_6287_ == 0 {
                        v___x_6282_ = v___x_6279_;
                        v_isShared_6283_ = v_isSharedCheck_6287_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6280_);
                        crate::leanh::lean_dec(v___x_6279_);
                        v___x_6282_ = crate::leanh::lean_box(0);
                        v_isShared_6283_ = v_isSharedCheck_6287_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6283_ == 0 {
                    v___x_6285_ = v___x_6282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6286_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6286_, 0, v_a_6280_);
                    v___x_6285_ = v_reuseFailAlloc_6286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg___boxed(
    mut v_k_6288_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_6289_: *mut crate::leanh::LeanObject,
    mut v___y_6290_: *mut crate::leanh::LeanObject,
    mut v___y_6291_: *mut crate::leanh::LeanObject,
    mut v___y_6292_: *mut crate::leanh::LeanObject,
    mut v___y_6293_: *mut crate::leanh::LeanObject,
    mut v___y_6294_: *mut crate::leanh::LeanObject,
    mut v___y_6295_: *mut crate::leanh::LeanObject,
    mut v___y_6296_: *mut crate::leanh::LeanObject,
    mut v___y_6297_: *mut crate::leanh::LeanObject,
    mut v___y_6298_: *mut crate::leanh::LeanObject,
    mut v___y_6299_: *mut crate::leanh::LeanObject,
    mut v___y_6300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_6301_: u8 = 0;
    let mut v_res_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_6301_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_6289_) as u8);
    v_res_6302_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(
            v_k_6288_,
            v_allowLevelAssignments_boxed_6301_,
            v___y_6290_,
            v___y_6291_,
            v___y_6292_,
            v___y_6293_,
            v___y_6294_,
            v___y_6295_,
            v___y_6296_,
            v___y_6297_,
            v___y_6298_,
            v___y_6299_,
        );
    crate::leanh::lean_dec(v___y_6299_);
    crate::leanh::lean_dec_ref(v___y_6298_);
    crate::leanh::lean_dec(v___y_6297_);
    crate::leanh::lean_dec_ref(v___y_6296_);
    crate::leanh::lean_dec(v___y_6295_);
    crate::leanh::lean_dec_ref(v___y_6294_);
    crate::leanh::lean_dec(v___y_6293_);
    crate::leanh::lean_dec_ref(v___y_6292_);
    crate::leanh::lean_dec(v___y_6291_);
    crate::leanh::lean_dec(v___y_6290_);
    return v_res_6302_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(
    mut v_00_u03b1_6303_: *mut crate::leanh::LeanObject,
    mut v_k_6304_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_6305_: u8,
    mut v___y_6306_: *mut crate::leanh::LeanObject,
    mut v___y_6307_: *mut crate::leanh::LeanObject,
    mut v___y_6308_: *mut crate::leanh::LeanObject,
    mut v___y_6309_: *mut crate::leanh::LeanObject,
    mut v___y_6310_: *mut crate::leanh::LeanObject,
    mut v___y_6311_: *mut crate::leanh::LeanObject,
    mut v___y_6312_: *mut crate::leanh::LeanObject,
    mut v___y_6313_: *mut crate::leanh::LeanObject,
    mut v___y_6314_: *mut crate::leanh::LeanObject,
    mut v___y_6315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6317_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(
            v_k_6304_,
            v_allowLevelAssignments_6305_,
            v___y_6306_,
            v___y_6307_,
            v___y_6308_,
            v___y_6309_,
            v___y_6310_,
            v___y_6311_,
            v___y_6312_,
            v___y_6313_,
            v___y_6314_,
            v___y_6315_,
        );
    return v___x_6317_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(
    mut v_00_u03b1_6318_: *mut crate::leanh::LeanObject,
    mut v_k_6319_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_6320_: *mut crate::leanh::LeanObject,
    mut v___y_6321_: *mut crate::leanh::LeanObject,
    mut v___y_6322_: *mut crate::leanh::LeanObject,
    mut v___y_6323_: *mut crate::leanh::LeanObject,
    mut v___y_6324_: *mut crate::leanh::LeanObject,
    mut v___y_6325_: *mut crate::leanh::LeanObject,
    mut v___y_6326_: *mut crate::leanh::LeanObject,
    mut v___y_6327_: *mut crate::leanh::LeanObject,
    mut v___y_6328_: *mut crate::leanh::LeanObject,
    mut v___y_6329_: *mut crate::leanh::LeanObject,
    mut v___y_6330_: *mut crate::leanh::LeanObject,
    mut v___y_6331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_6332_: u8 = 0;
    let mut v_res_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_6332_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_6320_) as u8);
    v_res_6333_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(
        v_00_u03b1_6318_,
        v_k_6319_,
        v_allowLevelAssignments_boxed_6332_,
        v___y_6321_,
        v___y_6322_,
        v___y_6323_,
        v___y_6324_,
        v___y_6325_,
        v___y_6326_,
        v___y_6327_,
        v___y_6328_,
        v___y_6329_,
        v___y_6330_,
    );
    crate::leanh::lean_dec(v___y_6330_);
    crate::leanh::lean_dec_ref(v___y_6329_);
    crate::leanh::lean_dec(v___y_6328_);
    crate::leanh::lean_dec_ref(v___y_6327_);
    crate::leanh::lean_dec(v___y_6326_);
    crate::leanh::lean_dec_ref(v___y_6325_);
    crate::leanh::lean_dec(v___y_6324_);
    crate::leanh::lean_dec_ref(v___y_6323_);
    crate::leanh::lean_dec(v___y_6322_);
    crate::leanh::lean_dec(v___y_6321_);
    return v_res_6333_;
}
pub unsafe fn l_Lean_Meta_Grind_tryToProveFalse___lam__0(
    mut v_cls_6334_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6335_: *mut crate::leanh::LeanObject,
    mut v___y_6336_: *mut crate::leanh::LeanObject,
    mut v___y_6337_: *mut crate::leanh::LeanObject,
    mut v___y_6338_: *mut crate::leanh::LeanObject,
    mut v___y_6339_: *mut crate::leanh::LeanObject,
    mut v___y_6340_: *mut crate::leanh::LeanObject,
    mut v___y_6341_: *mut crate::leanh::LeanObject,
    mut v___y_6342_: *mut crate::leanh::LeanObject,
    mut v___y_6343_: *mut crate::leanh::LeanObject,
    mut v___y_6344_: *mut crate::leanh::LeanObject,
    mut v___y_6345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6348_: u8 = 0;
    v_options_6347_ = crate::leanh::lean_ctor_get(v___y_6344_, 2);
    v_hasTrace_6348_ = crate::leanh::lean_ctor_get_uint8(
        v_options_6347_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_6348_ == 0 {
        let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_cls_6334_);
        v___x_6349_ = crate::leanh::lean_box((v_hasTrace_6348_) as usize);
        v___x_6350_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6350_, 0, v___x_6349_);
        return v___x_6350_;
    } else {
        let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6353_: u8 = 0;
        let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6351_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5;
        v___x_6352_ = l_Lean_Name_append(v___x_6351_, v_cls_6334_);
        v___x_6353_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_6335_,
            v_options_6347_,
            v___x_6352_,
        );
        crate::leanh::lean_dec(v___x_6352_);
        v___x_6354_ = crate::leanh::lean_box((v___x_6353_) as usize);
        v___x_6355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6355_, 0, v___x_6354_);
        return v___x_6355_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(
    mut v_cls_6356_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6357_: *mut crate::leanh::LeanObject,
    mut v___y_6358_: *mut crate::leanh::LeanObject,
    mut v___y_6359_: *mut crate::leanh::LeanObject,
    mut v___y_6360_: *mut crate::leanh::LeanObject,
    mut v___y_6361_: *mut crate::leanh::LeanObject,
    mut v___y_6362_: *mut crate::leanh::LeanObject,
    mut v___y_6363_: *mut crate::leanh::LeanObject,
    mut v___y_6364_: *mut crate::leanh::LeanObject,
    mut v___y_6365_: *mut crate::leanh::LeanObject,
    mut v___y_6366_: *mut crate::leanh::LeanObject,
    mut v___y_6367_: *mut crate::leanh::LeanObject,
    mut v___y_6368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6369_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(
        v_cls_6356_,
        v_____do__lift_6357_,
        v___y_6358_,
        v___y_6359_,
        v___y_6360_,
        v___y_6361_,
        v___y_6362_,
        v___y_6363_,
        v___y_6364_,
        v___y_6365_,
        v___y_6366_,
        v___y_6367_,
    );
    crate::leanh::lean_dec(v___y_6367_);
    crate::leanh::lean_dec_ref(v___y_6366_);
    crate::leanh::lean_dec(v___y_6365_);
    crate::leanh::lean_dec_ref(v___y_6364_);
    crate::leanh::lean_dec(v___y_6363_);
    crate::leanh::lean_dec_ref(v___y_6362_);
    crate::leanh::lean_dec(v___y_6361_);
    crate::leanh::lean_dec_ref(v___y_6360_);
    crate::leanh::lean_dec(v___y_6359_);
    crate::leanh::lean_dec(v___y_6358_);
    crate::leanh::lean_dec_ref(v_____do__lift_6357_);
    return v_res_6369_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_6378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2;
    v___x_6379_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__5;
    v___x_6380_ = l_Lean_Name_append(v___x_6379_, v_cls_6378_);
    return v___x_6380_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__4;
    v___x_6383_ = l_Lean_stringToMessageData(v___x_6382_);
    return v___x_6383_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(
    mut v_as_6384_: *mut crate::leanh::LeanObject,
    mut v_sz_6385_: usize,
    mut v_i_6386_: usize,
    mut v_b_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
    mut v___y_6391_: *mut crate::leanh::LeanObject,
    mut v___y_6392_: *mut crate::leanh::LeanObject,
    mut v___y_6393_: *mut crate::leanh::LeanObject,
    mut v___y_6394_: *mut crate::leanh::LeanObject,
    mut v___y_6395_: *mut crate::leanh::LeanObject,
    mut v___y_6396_: *mut crate::leanh::LeanObject,
    mut v___y_6397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: usize = 0;
    let mut v___x_6402_: usize = 0;
    let mut v___x_6404_: u8 = 0;
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6409_: u8 = 0;
    let mut v_array_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: u8 = 0;
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6421_: u8 = 0;
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: u8 = 0;
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_____x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6443_: u8 = 0;
    let mut v___x_6444_: u8 = 0;
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6455_: u8 = 0;
    let mut v_a_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6459_: u8 = 0;
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6463_: u8 = 0;
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6473_: u8 = 0;
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6480_: u8 = 0;
    let mut v_fst_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6503_: u8 = 0;
    let mut v___x_6504_: u8 = 0;
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: u8 = 0;
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6518_: u8 = 0;
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6522_: u8 = 0;
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6528_: u8 = 0;
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6532_: u8 = 0;
    let mut v_isSharedCheck_6533_: u8 = 0;
    let mut v_a_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6537_: u8 = 0;
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6541_: u8 = 0;
    let mut v_options_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6543_: u8 = 0;
    let mut v_inheritedTraceOptions_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: u8 = 0;
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6558_: u8 = 0;
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6562_: u8 = 0;
    let mut v_reuseFailAlloc_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6567_: u8 = 0;
    let mut v___x_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6571_: u8 = 0;
    let mut v_isSharedCheck_6572_: u8 = 0;
    let mut v_isSharedCheck_6573_: u8 = 0;
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6579_: u8 = 0;
    let mut v_a_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6583_: u8 = 0;
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6587_: u8 = 0;
    let mut v_reuseFailAlloc_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6589_: u8 = 0;
    let mut v_unused_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6593_: u8 = 0;
    let mut v_unused_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6404_ = lean_usize_dec_lt(v_i_6386_, v_sz_6385_);
                if v___x_6404_ == 0 {
                    v___x_6405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6405_, 0, v_b_6387_);
                    return v___x_6405_;
                } else {
                    v_snd_6406_ = crate::leanh::lean_ctor_get(v_b_6387_, 1);
                    v_isSharedCheck_6593_ = (!crate::leanh::lean_is_exclusive(v_b_6387_)) as u8;
                    if v_isSharedCheck_6593_ == 0 {
                        v_unused_6594_ = crate::leanh::lean_ctor_get(v_b_6387_, 0);
                        crate::leanh::lean_dec(v_unused_6594_);
                        v___x_6408_ = v_b_6387_;
                        v_isShared_6409_ = v_isSharedCheck_6593_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6406_);
                        crate::leanh::lean_dec(v_b_6387_);
                        v___x_6408_ = crate::leanh::lean_box(0);
                        v_isShared_6409_ = v_isSharedCheck_6593_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6401_ = 1usize;
                v___x_6402_ = lean_usize_add(v_i_6386_, v___x_6401_);
                v_i_6386_ = v___x_6402_;
                v_b_6387_ = v_a_6400_;
                state = 0;
                continue;
            }
            2 => {
                v_array_6410_ = crate::leanh::lean_ctor_get(v_snd_6406_, 0);
                v_start_6411_ = crate::leanh::lean_ctor_get(v_snd_6406_, 1);
                v_stop_6412_ = crate::leanh::lean_ctor_get(v_snd_6406_, 2);
                v___x_6413_ = crate::leanh::lean_box(0);
                v___x_6414_ = lean_nat_dec_lt(v_start_6411_, v_stop_6412_);
                if v___x_6414_ == 0 {
                    if v_isShared_6409_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6408_, 0, v___x_6413_);
                        v___x_6416_ = v___x_6408_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6418_, 0, v___x_6413_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6418_, 1, v_snd_6406_);
                        v___x_6416_ = v_reuseFailAlloc_6418_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_6412_);
                    crate::leanh::lean_inc(v_start_6411_);
                    crate::leanh::lean_inc_ref(v_array_6410_);
                    v_isSharedCheck_6589_ = (!crate::leanh::lean_is_exclusive(v_snd_6406_)) as u8;
                    if v_isSharedCheck_6589_ == 0 {
                        v_unused_6590_ = crate::leanh::lean_ctor_get(v_snd_6406_, 2);
                        crate::leanh::lean_dec(v_unused_6590_);
                        v_unused_6591_ = crate::leanh::lean_ctor_get(v_snd_6406_, 1);
                        crate::leanh::lean_dec(v_unused_6591_);
                        v_unused_6592_ = crate::leanh::lean_ctor_get(v_snd_6406_, 0);
                        crate::leanh::lean_dec(v_unused_6592_);
                        v___x_6420_ = v_snd_6406_;
                        v_isShared_6421_ = v_isSharedCheck_6589_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_6406_);
                        v___x_6420_ = crate::leanh::lean_box(0);
                        v_isShared_6421_ = v_isSharedCheck_6589_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6417_, 0, v___x_6416_);
                return v___x_6417_;
            }
            4 => {
                v___x_6422_ = lean_array_fget(v_array_6410_, v_start_6411_);
                v___x_6423_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6424_ = lean_nat_add(v_start_6411_, v___x_6423_);
                crate::leanh::lean_dec(v_start_6411_);
                if v_isShared_6421_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6420_, 1, v___x_6424_);
                    v___x_6426_ = v___x_6420_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6588_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6588_, 0, v_array_6410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6588_, 1, v___x_6424_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6588_, 2, v_stop_6412_);
                    v___x_6426_ = v_reuseFailAlloc_6588_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6427_ = (crate::leanh::lean_unbox(v___x_6422_) as u8);
                crate::leanh::lean_dec(v___x_6422_);
                if v___x_6427_ == 0 {
                    if v_isShared_6409_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6408_, 1, v___x_6426_);
                        crate::leanh::lean_ctor_set(v___x_6408_, 0, v___x_6413_);
                        v___x_6429_ = v___x_6408_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6430_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6430_, 0, v___x_6413_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6430_, 1, v___x_6426_);
                        v___x_6429_ = v_reuseFailAlloc_6430_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_6431_ = lean_array_uget_borrowed(v_as_6384_, v_i_6386_);
                    crate::leanh::lean_inc(v___y_6397_);
                    crate::leanh::lean_inc_ref(v___y_6396_);
                    crate::leanh::lean_inc(v___y_6395_);
                    crate::leanh::lean_inc_ref(v___y_6394_);
                    crate::leanh::lean_inc(v_a_6431_);
                    v___x_6469_ = lean_infer_type(
                        v_a_6431_,
                        v___y_6394_,
                        v___y_6395_,
                        v___y_6396_,
                        v___y_6397_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6469_) == 0 {
                        v_a_6470_ = crate::leanh::lean_ctor_get(v___x_6469_, 0);
                        v_isSharedCheck_6579_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6469_)) as u8;
                        if v_isSharedCheck_6579_ == 0 {
                            v___x_6472_ = v___x_6469_;
                            v_isShared_6473_ = v_isSharedCheck_6579_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6470_);
                            crate::leanh::lean_dec(v___x_6469_);
                            v___x_6472_ = crate::leanh::lean_box(0);
                            v_isShared_6473_ = v_isSharedCheck_6579_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6426_);
                        crate::leanh::lean_del_object(v___x_6408_);
                        v_a_6580_ = crate::leanh::lean_ctor_get(v___x_6469_, 0);
                        v_isSharedCheck_6587_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6469_)) as u8;
                        if v_isSharedCheck_6587_ == 0 {
                            v___x_6582_ = v___x_6469_;
                            v_isShared_6583_ = v_isSharedCheck_6587_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6580_);
                            crate::leanh::lean_dec(v___x_6469_);
                            v___x_6582_ = crate::leanh::lean_box(0);
                            v_isShared_6583_ = v_isSharedCheck_6587_;
                            state = 34;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v_a_6400_ = v___x_6429_;
                state = 1;
                continue;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_____x_6433_) == 1 {
                    v_val_6438_ = crate::leanh::lean_ctor_get(v_____x_6433_, 0);
                    crate::leanh::lean_inc(v_val_6438_);
                    crate::leanh::lean_dec_ref_known(v_____x_6433_, 1);
                    crate::leanh::lean_inc(v_a_6431_);
                    v___x_6439_ = l_Lean_Meta_isExprDefEq(
                        v_a_6431_,
                        v_val_6438_,
                        v___y_6434_,
                        v___y_6435_,
                        v___y_6436_,
                        v___y_6437_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6439_) == 0 {
                        v_a_6440_ = crate::leanh::lean_ctor_get(v___x_6439_, 0);
                        v_isSharedCheck_6455_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6439_)) as u8;
                        if v_isSharedCheck_6455_ == 0 {
                            v___x_6442_ = v___x_6439_;
                            v_isShared_6443_ = v_isSharedCheck_6455_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6440_);
                            crate::leanh::lean_dec(v___x_6439_);
                            v___x_6442_ = crate::leanh::lean_box(0);
                            v_isShared_6443_ = v_isSharedCheck_6455_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6426_);
                        crate::leanh::lean_del_object(v___x_6408_);
                        v_a_6456_ = crate::leanh::lean_ctor_get(v___x_6439_, 0);
                        v_isSharedCheck_6463_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6439_)) as u8;
                        if v_isSharedCheck_6463_ == 0 {
                            v___x_6458_ = v___x_6439_;
                            v_isShared_6459_ = v_isSharedCheck_6463_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6456_);
                            crate::leanh::lean_dec(v___x_6439_);
                            v___x_6458_ = crate::leanh::lean_box(0);
                            v_isShared_6459_ = v_isSharedCheck_6463_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_____x_6433_);
                    v___x_6464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0;
                    if v_isShared_6409_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6408_, 1, v___x_6426_);
                        crate::leanh::lean_ctor_set(v___x_6408_, 0, v___x_6464_);
                        v___x_6466_ = v___x_6408_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_6468_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6468_, 0, v___x_6464_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6468_, 1, v___x_6426_);
                        v___x_6466_ = v_reuseFailAlloc_6468_;
                        state = 14;
                        continue;
                    }
                }
            }
            8 => {
                v___x_6444_ = (crate::leanh::lean_unbox(v_a_6440_) as u8);
                crate::leanh::lean_dec(v_a_6440_);
                if v___x_6444_ == 0 {
                    v___x_6445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0;
                    if v_isShared_6409_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6408_, 1, v___x_6426_);
                        crate::leanh::lean_ctor_set(v___x_6408_, 0, v___x_6445_);
                        v___x_6447_ = v___x_6408_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_6451_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6451_, 0, v___x_6445_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6451_, 1, v___x_6426_);
                        v___x_6447_ = v_reuseFailAlloc_6451_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6442_);
                    if v_isShared_6409_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6408_, 1, v___x_6426_);
                        crate::leanh::lean_ctor_set(v___x_6408_, 0, v___x_6413_);
                        v___x_6453_ = v___x_6408_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_6454_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6454_, 0, v___x_6413_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6454_, 1, v___x_6426_);
                        v___x_6453_ = v_reuseFailAlloc_6454_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_6443_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6442_, 0, v___x_6447_);
                    v___x_6449_ = v___x_6442_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6450_, 0, v___x_6447_);
                    v___x_6449_ = v_reuseFailAlloc_6450_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6449_;
            }
            11 => {
                v_a_6400_ = v___x_6453_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_6459_ == 0 {
                    v___x_6461_ = v___x_6458_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6462_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6462_, 0, v_a_6456_);
                    v___x_6461_ = v_reuseFailAlloc_6462_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6461_;
            }
            14 => {
                v___x_6467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6467_, 0, v___x_6466_);
                return v___x_6467_;
            }
            15 => {
                v___x_6474_ =
                    l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(
                        v_a_6470_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6474_) == 1 {
                    crate::leanh::lean_del_object(v___x_6472_);
                    v_val_6475_ = crate::leanh::lean_ctor_get(v___x_6474_, 0);
                    crate::leanh::lean_inc(v_val_6475_);
                    crate::leanh::lean_dec_ref_known(v___x_6474_, 1);
                    v_snd_6476_ = crate::leanh::lean_ctor_get(v_val_6475_, 1);
                    v_fst_6477_ = crate::leanh::lean_ctor_get(v_val_6475_, 0);
                    v_isSharedCheck_6573_ = (!crate::leanh::lean_is_exclusive(v_val_6475_)) as u8;
                    if v_isSharedCheck_6573_ == 0 {
                        v___x_6479_ = v_val_6475_;
                        v_isShared_6480_ = v_isSharedCheck_6573_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6476_);
                        crate::leanh::lean_inc(v_fst_6477_);
                        crate::leanh::lean_dec(v_val_6475_);
                        v___x_6479_ = crate::leanh::lean_box(0);
                        v_isShared_6480_ = v_isSharedCheck_6573_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6474_);
                    crate::leanh::lean_del_object(v___x_6408_);
                    v___x_6574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0;
                    v___x_6575_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6575_, 0, v___x_6574_);
                    crate::leanh::lean_ctor_set(v___x_6575_, 1, v___x_6426_);
                    if v_isShared_6473_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6472_, 0, v___x_6575_);
                        v___x_6577_ = v___x_6472_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_6578_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6578_, 0, v___x_6575_);
                        v___x_6577_ = v_reuseFailAlloc_6578_;
                        state = 33;
                        continue;
                    }
                }
            }
            16 => {
                v_fst_6481_ = crate::leanh::lean_ctor_get(v_snd_6476_, 0);
                v_snd_6482_ = crate::leanh::lean_ctor_get(v_snd_6476_, 1);
                v_isSharedCheck_6572_ = (!crate::leanh::lean_is_exclusive(v_snd_6476_)) as u8;
                if v_isSharedCheck_6572_ == 0 {
                    v___x_6484_ = v_snd_6476_;
                    v_isShared_6485_ = v_isSharedCheck_6572_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6482_);
                    crate::leanh::lean_inc(v_fst_6481_);
                    crate::leanh::lean_dec(v_snd_6476_);
                    v___x_6484_ = crate::leanh::lean_box(0);
                    v_isShared_6485_ = v_isSharedCheck_6572_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                crate::leanh::lean_inc(v_fst_6481_);
                v___x_6486_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(v_fst_6481_, v___y_6388_, v___y_6389_, v___y_6390_, v___y_6391_, v___y_6392_, v___y_6393_, v___y_6394_, v___y_6395_, v___y_6396_, v___y_6397_);
                if crate::leanh::lean_obj_tag(v___x_6486_) == 0 {
                    v_a_6487_ = crate::leanh::lean_ctor_get(v___x_6486_, 0);
                    crate::leanh::lean_inc(v_a_6487_);
                    crate::leanh::lean_dec_ref_known(v___x_6486_, 1);
                    v_options_6542_ = crate::leanh::lean_ctor_get(v___y_6396_, 2);
                    v_hasTrace_6543_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_6542_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6543_ == 0 {
                        crate::leanh::lean_del_object(v___x_6479_);
                        v___y_6489_ = v___y_6388_;
                        v___y_6490_ = v___y_6389_;
                        v___y_6491_ = v___y_6390_;
                        v___y_6492_ = v___y_6391_;
                        v___y_6493_ = v___y_6392_;
                        v___y_6494_ = v___y_6393_;
                        v___y_6495_ = v___y_6394_;
                        v___y_6496_ = v___y_6395_;
                        v___y_6497_ = v___y_6396_;
                        v___y_6498_ = v___y_6397_;
                        state = 18;
                        continue;
                    } else {
                        v_inheritedTraceOptions_6544_ =
                            crate::leanh::lean_ctor_get(v___y_6396_, 13);
                        v_cls_6545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2;
                        v___x_6546_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__3);
                        v___x_6547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_6544_,
                            v_options_6542_,
                            v___x_6546_,
                        );
                        if v___x_6547_ == 0 {
                            crate::leanh::lean_del_object(v___x_6479_);
                            v___y_6489_ = v___y_6388_;
                            v___y_6490_ = v___y_6389_;
                            v___y_6491_ = v___y_6390_;
                            v___y_6492_ = v___y_6391_;
                            v___y_6493_ = v___y_6392_;
                            v___y_6494_ = v___y_6393_;
                            v___y_6495_ = v___y_6394_;
                            v___y_6496_ = v___y_6395_;
                            v___y_6497_ = v___y_6396_;
                            v___y_6498_ = v___y_6397_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6487_);
                            v___x_6548_ = l_Lean_MessageData_ofExpr(v_a_6487_);
                            v___x_6549_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__5);
                            if v_isShared_6480_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_6479_, 7);
                                crate::leanh::lean_ctor_set(v___x_6479_, 1, v___x_6549_);
                                crate::leanh::lean_ctor_set(v___x_6479_, 0, v___x_6548_);
                                v___x_6551_ = v___x_6479_;
                                state = 28;
                                continue;
                            } else {
                                v_reuseFailAlloc_6563_ =
                                    crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6563_, 0, v___x_6548_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6563_, 1, v___x_6549_);
                                v___x_6551_ = v_reuseFailAlloc_6563_;
                                state = 28;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6484_);
                    crate::leanh::lean_dec(v_snd_6482_);
                    crate::leanh::lean_dec(v_fst_6481_);
                    crate::leanh::lean_del_object(v___x_6479_);
                    crate::leanh::lean_dec(v_fst_6477_);
                    crate::leanh::lean_dec_ref(v___x_6426_);
                    crate::leanh::lean_del_object(v___x_6408_);
                    v_a_6564_ = crate::leanh::lean_ctor_get(v___x_6486_, 0);
                    v_isSharedCheck_6571_ = (!crate::leanh::lean_is_exclusive(v___x_6486_)) as u8;
                    if v_isSharedCheck_6571_ == 0 {
                        v___x_6566_ = v___x_6486_;
                        v_isShared_6567_ = v_isSharedCheck_6571_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6564_);
                        crate::leanh::lean_dec(v___x_6486_);
                        v___x_6566_ = crate::leanh::lean_box(0);
                        v_isShared_6567_ = v_isSharedCheck_6571_;
                        state = 31;
                        continue;
                    }
                }
            }
            18 => {
                crate::leanh::lean_inc(v_a_6487_);
                v___x_6499_ = l_Lean_Meta_isDefEqD(
                    v_a_6487_,
                    v_snd_6482_,
                    v___y_6495_,
                    v___y_6496_,
                    v___y_6497_,
                    v___y_6498_,
                );
                if crate::leanh::lean_obj_tag(v___x_6499_) == 0 {
                    v_a_6500_ = crate::leanh::lean_ctor_get(v___x_6499_, 0);
                    v_isSharedCheck_6533_ = (!crate::leanh::lean_is_exclusive(v___x_6499_)) as u8;
                    if v_isSharedCheck_6533_ == 0 {
                        v___x_6502_ = v___x_6499_;
                        v_isShared_6503_ = v_isSharedCheck_6533_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6500_);
                        crate::leanh::lean_dec(v___x_6499_);
                        v___x_6502_ = crate::leanh::lean_box(0);
                        v_isShared_6503_ = v_isSharedCheck_6533_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6487_);
                    crate::leanh::lean_del_object(v___x_6484_);
                    crate::leanh::lean_dec(v_fst_6481_);
                    crate::leanh::lean_dec(v_fst_6477_);
                    crate::leanh::lean_dec_ref(v___x_6426_);
                    crate::leanh::lean_del_object(v___x_6408_);
                    v_a_6534_ = crate::leanh::lean_ctor_get(v___x_6499_, 0);
                    v_isSharedCheck_6541_ = (!crate::leanh::lean_is_exclusive(v___x_6499_)) as u8;
                    if v_isSharedCheck_6541_ == 0 {
                        v___x_6536_ = v___x_6499_;
                        v_isShared_6537_ = v_isSharedCheck_6541_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6534_);
                        crate::leanh::lean_dec(v___x_6499_);
                        v___x_6536_ = crate::leanh::lean_box(0);
                        v_isShared_6537_ = v_isSharedCheck_6541_;
                        state = 26;
                        continue;
                    }
                }
            }
            19 => {
                v___x_6504_ = (crate::leanh::lean_unbox(v_a_6500_) as u8);
                crate::leanh::lean_dec(v_a_6500_);
                if v___x_6504_ == 0 {
                    crate::leanh::lean_dec(v_a_6487_);
                    crate::leanh::lean_dec(v_fst_6481_);
                    crate::leanh::lean_dec(v_fst_6477_);
                    crate::leanh::lean_del_object(v___x_6408_);
                    v___x_6505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__0;
                    if v_isShared_6485_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6484_, 1, v___x_6426_);
                        crate::leanh::lean_ctor_set(v___x_6484_, 0, v___x_6505_);
                        v___x_6507_ = v___x_6484_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_6511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6511_, 0, v___x_6505_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6511_, 1, v___x_6426_);
                        v___x_6507_ = v_reuseFailAlloc_6511_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6502_);
                    crate::leanh::lean_del_object(v___x_6484_);
                    if crate::leanh::lean_obj_tag(v_fst_6477_) == 0 {
                        v___x_6512_ = 0;
                        v___x_6513_ = l_Lean_Meta_Grind_proveEq_x3f(
                            v_fst_6481_,
                            v_a_6487_,
                            v___x_6512_,
                            v___y_6489_,
                            v___y_6490_,
                            v___y_6491_,
                            v___y_6492_,
                            v___y_6493_,
                            v___y_6494_,
                            v___y_6495_,
                            v___y_6496_,
                            v___y_6497_,
                            v___y_6498_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6513_) == 0 {
                            v_a_6514_ = crate::leanh::lean_ctor_get(v___x_6513_, 0);
                            crate::leanh::lean_inc(v_a_6514_);
                            crate::leanh::lean_dec_ref_known(v___x_6513_, 1);
                            v_____x_6433_ = v_a_6514_;
                            v___y_6434_ = v___y_6495_;
                            v___y_6435_ = v___y_6496_;
                            v___y_6436_ = v___y_6497_;
                            v___y_6437_ = v___y_6498_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_6426_);
                            crate::leanh::lean_del_object(v___x_6408_);
                            v_a_6515_ = crate::leanh::lean_ctor_get(v___x_6513_, 0);
                            v_isSharedCheck_6522_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6513_)) as u8;
                            if v_isSharedCheck_6522_ == 0 {
                                v___x_6517_ = v___x_6513_;
                                v_isShared_6518_ = v_isSharedCheck_6522_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6515_);
                                crate::leanh::lean_dec(v___x_6513_);
                                v___x_6517_ = crate::leanh::lean_box(0);
                                v_isShared_6518_ = v_isSharedCheck_6522_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_fst_6477_, 1);
                        v___x_6523_ = l_Lean_Meta_Grind_proveHEq_x3f(
                            v_fst_6481_,
                            v_a_6487_,
                            v___y_6489_,
                            v___y_6490_,
                            v___y_6491_,
                            v___y_6492_,
                            v___y_6493_,
                            v___y_6494_,
                            v___y_6495_,
                            v___y_6496_,
                            v___y_6497_,
                            v___y_6498_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6523_) == 0 {
                            v_a_6524_ = crate::leanh::lean_ctor_get(v___x_6523_, 0);
                            crate::leanh::lean_inc(v_a_6524_);
                            crate::leanh::lean_dec_ref_known(v___x_6523_, 1);
                            v_____x_6433_ = v_a_6524_;
                            v___y_6434_ = v___y_6495_;
                            v___y_6435_ = v___y_6496_;
                            v___y_6436_ = v___y_6497_;
                            v___y_6437_ = v___y_6498_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_6426_);
                            crate::leanh::lean_del_object(v___x_6408_);
                            v_a_6525_ = crate::leanh::lean_ctor_get(v___x_6523_, 0);
                            v_isSharedCheck_6532_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6523_)) as u8;
                            if v_isSharedCheck_6532_ == 0 {
                                v___x_6527_ = v___x_6523_;
                                v_isShared_6528_ = v_isSharedCheck_6532_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6525_);
                                crate::leanh::lean_dec(v___x_6523_);
                                v___x_6527_ = crate::leanh::lean_box(0);
                                v_isShared_6528_ = v_isSharedCheck_6532_;
                                state = 24;
                                continue;
                            }
                        }
                    }
                }
            }
            20 => {
                if v_isShared_6503_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6502_, 0, v___x_6507_);
                    v___x_6509_ = v___x_6502_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6510_, 0, v___x_6507_);
                    v___x_6509_ = v_reuseFailAlloc_6510_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6509_;
            }
            22 => {
                if v_isShared_6518_ == 0 {
                    v___x_6520_ = v___x_6517_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6521_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6521_, 0, v_a_6515_);
                    v___x_6520_ = v_reuseFailAlloc_6521_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6520_;
            }
            24 => {
                if v_isShared_6528_ == 0 {
                    v___x_6530_ = v___x_6527_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6531_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6531_, 0, v_a_6525_);
                    v___x_6530_ = v_reuseFailAlloc_6531_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6530_;
            }
            26 => {
                if v_isShared_6537_ == 0 {
                    v___x_6539_ = v___x_6536_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6540_, 0, v_a_6534_);
                    v___x_6539_ = v_reuseFailAlloc_6540_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_6539_;
            }
            28 => {
                crate::leanh::lean_inc(v_snd_6482_);
                v___x_6552_ = l_Lean_MessageData_ofExpr(v_snd_6482_);
                v___x_6553_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6553_, 0, v___x_6551_);
                crate::leanh::lean_ctor_set(v___x_6553_, 1, v___x_6552_);
                v___x_6554_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_6545_, v___x_6553_, v___y_6394_, v___y_6395_, v___y_6396_, v___y_6397_);
                if crate::leanh::lean_obj_tag(v___x_6554_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6554_, 1);
                    v___y_6489_ = v___y_6388_;
                    v___y_6490_ = v___y_6389_;
                    v___y_6491_ = v___y_6390_;
                    v___y_6492_ = v___y_6391_;
                    v___y_6493_ = v___y_6392_;
                    v___y_6494_ = v___y_6393_;
                    v___y_6495_ = v___y_6394_;
                    v___y_6496_ = v___y_6395_;
                    v___y_6497_ = v___y_6396_;
                    v___y_6498_ = v___y_6397_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_6487_);
                    crate::leanh::lean_del_object(v___x_6484_);
                    crate::leanh::lean_dec(v_snd_6482_);
                    crate::leanh::lean_dec(v_fst_6481_);
                    crate::leanh::lean_dec(v_fst_6477_);
                    crate::leanh::lean_dec_ref(v___x_6426_);
                    crate::leanh::lean_del_object(v___x_6408_);
                    v_a_6555_ = crate::leanh::lean_ctor_get(v___x_6554_, 0);
                    v_isSharedCheck_6562_ = (!crate::leanh::lean_is_exclusive(v___x_6554_)) as u8;
                    if v_isSharedCheck_6562_ == 0 {
                        v___x_6557_ = v___x_6554_;
                        v_isShared_6558_ = v_isSharedCheck_6562_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6555_);
                        crate::leanh::lean_dec(v___x_6554_);
                        v___x_6557_ = crate::leanh::lean_box(0);
                        v_isShared_6558_ = v_isSharedCheck_6562_;
                        state = 29;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_6558_ == 0 {
                    v___x_6560_ = v___x_6557_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6561_, 0, v_a_6555_);
                    v___x_6560_ = v_reuseFailAlloc_6561_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_6560_;
            }
            31 => {
                if v_isShared_6567_ == 0 {
                    v___x_6569_ = v___x_6566_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6570_, 0, v_a_6564_);
                    v___x_6569_ = v_reuseFailAlloc_6570_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_6569_;
            }
            33 => {
                return v___x_6577_;
            }
            34 => {
                if v_isShared_6583_ == 0 {
                    v___x_6585_ = v___x_6582_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_6586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6586_, 0, v_a_6580_);
                    v___x_6585_ = v_reuseFailAlloc_6586_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_6585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(
    mut v_as_6595_: *mut crate::leanh::LeanObject,
    mut v_sz_6596_: *mut crate::leanh::LeanObject,
    mut v_i_6597_: *mut crate::leanh::LeanObject,
    mut v_b_6598_: *mut crate::leanh::LeanObject,
    mut v___y_6599_: *mut crate::leanh::LeanObject,
    mut v___y_6600_: *mut crate::leanh::LeanObject,
    mut v___y_6601_: *mut crate::leanh::LeanObject,
    mut v___y_6602_: *mut crate::leanh::LeanObject,
    mut v___y_6603_: *mut crate::leanh::LeanObject,
    mut v___y_6604_: *mut crate::leanh::LeanObject,
    mut v___y_6605_: *mut crate::leanh::LeanObject,
    mut v___y_6606_: *mut crate::leanh::LeanObject,
    mut v___y_6607_: *mut crate::leanh::LeanObject,
    mut v___y_6608_: *mut crate::leanh::LeanObject,
    mut v___y_6609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6610_: usize = 0;
    let mut v_i_boxed_6611_: usize = 0;
    let mut v_res_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6610_ = crate::leanh::lean_unbox_usize(v_sz_6596_);
    crate::leanh::lean_dec(v_sz_6596_);
    v_i_boxed_6611_ = crate::leanh::lean_unbox_usize(v_i_6597_);
    crate::leanh::lean_dec(v_i_6597_);
    v_res_6612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_as_6595_, v_sz_boxed_6610_, v_i_boxed_6611_, v_b_6598_, v___y_6599_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_);
    crate::leanh::lean_dec(v___y_6608_);
    crate::leanh::lean_dec_ref(v___y_6607_);
    crate::leanh::lean_dec(v___y_6606_);
    crate::leanh::lean_dec_ref(v___y_6605_);
    crate::leanh::lean_dec(v___y_6604_);
    crate::leanh::lean_dec_ref(v___y_6603_);
    crate::leanh::lean_dec(v___y_6602_);
    crate::leanh::lean_dec_ref(v___y_6601_);
    crate::leanh::lean_dec(v___y_6600_);
    crate::leanh::lean_dec(v___y_6599_);
    crate::leanh::lean_dec_ref(v_as_6595_);
    return v_res_6612_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6614_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__0;
    v___x_6615_ = l_Lean_stringToMessageData(v___x_6614_);
    return v___x_6615_;
}
pub unsafe fn l_Lean_Meta_Grind_tryToProveFalse___lam__1(
    mut v_arg_6616_: *mut crate::leanh::LeanObject,
    mut v___x_6617_: u8,
    mut v_e_6618_: *mut crate::leanh::LeanObject,
    mut v___f_6619_: *mut crate::leanh::LeanObject,
    mut v_cls_6620_: *mut crate::leanh::LeanObject,
    mut v___y_6621_: *mut crate::leanh::LeanObject,
    mut v___y_6622_: *mut crate::leanh::LeanObject,
    mut v___y_6623_: *mut crate::leanh::LeanObject,
    mut v___y_6624_: *mut crate::leanh::LeanObject,
    mut v___y_6625_: *mut crate::leanh::LeanObject,
    mut v___y_6626_: *mut crate::leanh::LeanObject,
    mut v___y_6627_: *mut crate::leanh::LeanObject,
    mut v___y_6628_: *mut crate::leanh::LeanObject,
    mut v___y_6629_: *mut crate::leanh::LeanObject,
    mut v___y_6630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6637_: u8 = 0;
    let mut v___x_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6645_: usize = 0;
    let mut v___x_6646_: usize = 0;
    let mut v___x_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v_fst_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6655_: u8 = 0;
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6664_: u8 = 0;
    let mut v___x_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6674_: u8 = 0;
    let mut v___x_6675_: u8 = 0;
    let mut v_inheritedTraceOptions_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: u8 = 0;
    let mut v___x_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6692_: u8 = 0;
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6696_: u8 = 0;
    let mut v_reuseFailAlloc_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6701_: u8 = 0;
    let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6705_: u8 = 0;
    let mut v_a_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6709_: u8 = 0;
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6713_: u8 = 0;
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6717_: u8 = 0;
    let mut v_a_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6721_: u8 = 0;
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6725_: u8 = 0;
    let mut v_isSharedCheck_6726_: u8 = 0;
    let mut v_a_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6730_: u8 = 0;
    let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6734_: u8 = 0;
    let mut v_val_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6739_: u8 = 0;
    let mut v_unused_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6741_: u8 = 0;
    let mut v_a_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6745_: u8 = 0;
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6749_: u8 = 0;
    let mut v_reuseFailAlloc_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6751_: u8 = 0;
    let mut v_unused_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6756_: u8 = 0;
    let mut v___x_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_arg_6616_);
                v___x_6632_ = l_Lean_Meta_forallMetaTelescope(
                    v_arg_6616_,
                    v___x_6617_,
                    v___y_6627_,
                    v___y_6628_,
                    v___y_6629_,
                    v___y_6630_,
                );
                if crate::leanh::lean_obj_tag(v___x_6632_) == 0 {
                    v_a_6633_ = crate::leanh::lean_ctor_get(v___x_6632_, 0);
                    crate::leanh::lean_inc(v_a_6633_);
                    crate::leanh::lean_dec_ref_known(v___x_6632_, 1);
                    v_fst_6634_ = crate::leanh::lean_ctor_get(v_a_6633_, 0);
                    v_isSharedCheck_6751_ = (!crate::leanh::lean_is_exclusive(v_a_6633_)) as u8;
                    if v_isSharedCheck_6751_ == 0 {
                        v_unused_6752_ = crate::leanh::lean_ctor_get(v_a_6633_, 1);
                        crate::leanh::lean_dec(v_unused_6752_);
                        v___x_6636_ = v_a_6633_;
                        v_isShared_6637_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_6634_);
                        crate::leanh::lean_dec(v_a_6633_);
                        v___x_6636_ = crate::leanh::lean_box(0);
                        v_isShared_6637_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_cls_6620_);
                    crate::leanh::lean_dec_ref(v___f_6619_);
                    crate::leanh::lean_dec_ref(v_e_6618_);
                    crate::leanh::lean_dec_ref(v_arg_6616_);
                    v_a_6753_ = crate::leanh::lean_ctor_get(v___x_6632_, 0);
                    v_isSharedCheck_6760_ = (!crate::leanh::lean_is_exclusive(v___x_6632_)) as u8;
                    if v_isSharedCheck_6760_ == 0 {
                        v___x_6755_ = v___x_6632_;
                        v_isShared_6756_ = v_isSharedCheck_6760_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6753_);
                        crate::leanh::lean_dec(v___x_6632_);
                        v___x_6755_ = crate::leanh::lean_box(0);
                        v_isShared_6756_ = v_isSharedCheck_6760_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6638_ = l_Lean_Meta_mkGenDiseqMask(v_arg_6616_);
                crate::leanh::lean_dec_ref(v_arg_6616_);
                v___x_6639_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6640_ = lean_array_get_size(v___x_6638_);
                v___x_6641_ = l_Array_toSubarray___redArg(v___x_6638_, v___x_6639_, v___x_6640_);
                v___x_6642_ = crate::leanh::lean_box(0);
                if v_isShared_6637_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6636_, 1, v___x_6641_);
                    crate::leanh::lean_ctor_set(v___x_6636_, 0, v___x_6642_);
                    v___x_6644_ = v___x_6636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 0, v___x_6642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 1, v___x_6641_);
                    v___x_6644_ = v_reuseFailAlloc_6750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_6645_ = lean_array_size(v_fst_6634_);
                v___x_6646_ = 0usize;
                v___x_6647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(v_fst_6634_, v_sz_6645_, v___x_6646_, v___x_6644_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_, v___y_6630_);
                if crate::leanh::lean_obj_tag(v___x_6647_) == 0 {
                    v_a_6648_ = crate::leanh::lean_ctor_get(v___x_6647_, 0);
                    v_isSharedCheck_6741_ = (!crate::leanh::lean_is_exclusive(v___x_6647_)) as u8;
                    if v_isSharedCheck_6741_ == 0 {
                        v___x_6650_ = v___x_6647_;
                        v_isShared_6651_ = v_isSharedCheck_6741_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6648_);
                        crate::leanh::lean_dec(v___x_6647_);
                        v___x_6650_ = crate::leanh::lean_box(0);
                        v_isShared_6651_ = v_isSharedCheck_6741_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6634_);
                    crate::leanh::lean_dec(v_cls_6620_);
                    crate::leanh::lean_dec_ref(v___f_6619_);
                    crate::leanh::lean_dec_ref(v_e_6618_);
                    v_a_6742_ = crate::leanh::lean_ctor_get(v___x_6647_, 0);
                    v_isSharedCheck_6749_ = (!crate::leanh::lean_is_exclusive(v___x_6647_)) as u8;
                    if v_isSharedCheck_6749_ == 0 {
                        v___x_6744_ = v___x_6647_;
                        v_isShared_6745_ = v_isSharedCheck_6749_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6742_);
                        crate::leanh::lean_dec(v___x_6647_);
                        v___x_6744_ = crate::leanh::lean_box(0);
                        v_isShared_6745_ = v_isSharedCheck_6749_;
                        state = 22;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_6652_ = crate::leanh::lean_ctor_get(v_a_6648_, 0);
                v_isSharedCheck_6739_ = (!crate::leanh::lean_is_exclusive(v_a_6648_)) as u8;
                if v_isSharedCheck_6739_ == 0 {
                    v_unused_6740_ = crate::leanh::lean_ctor_get(v_a_6648_, 1);
                    crate::leanh::lean_dec(v_unused_6740_);
                    v___x_6654_ = v_a_6648_;
                    v_isShared_6655_ = v_isSharedCheck_6739_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_6652_);
                    crate::leanh::lean_dec(v_a_6648_);
                    v___x_6654_ = crate::leanh::lean_box(0);
                    v_isShared_6655_ = v_isSharedCheck_6739_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_fst_6652_) == 0 {
                    crate::leanh::lean_del_object(v___x_6650_);
                    crate::leanh::lean_inc_ref(v_e_6618_);
                    v___x_6656_ = l_Lean_Meta_Grind_mkEqTrueProof(
                        v_e_6618_,
                        v___y_6621_,
                        v___y_6622_,
                        v___y_6623_,
                        v___y_6624_,
                        v___y_6625_,
                        v___y_6626_,
                        v___y_6627_,
                        v___y_6628_,
                        v___y_6629_,
                        v___y_6630_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6656_) == 0 {
                        v_a_6657_ = crate::leanh::lean_ctor_get(v___x_6656_, 0);
                        crate::leanh::lean_inc(v_a_6657_);
                        crate::leanh::lean_dec_ref_known(v___x_6656_, 1);
                        v___x_6658_ = l_Lean_Meta_mkOfEqTrueCore(v_e_6618_, v_a_6657_);
                        v___x_6659_ = l_Lean_mkAppN(v___x_6658_, v_fst_6634_);
                        crate::leanh::lean_dec(v_fst_6634_);
                        v___x_6660_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(v___x_6659_, v___y_6628_);
                        v_a_6661_ = crate::leanh::lean_ctor_get(v___x_6660_, 0);
                        v_isSharedCheck_6726_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6660_)) as u8;
                        if v_isSharedCheck_6726_ == 0 {
                            v___x_6663_ = v___x_6660_;
                            v_isShared_6664_ = v_isSharedCheck_6726_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6661_);
                            crate::leanh::lean_dec(v___x_6660_);
                            v___x_6663_ = crate::leanh::lean_box(0);
                            v_isShared_6664_ = v_isSharedCheck_6726_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6654_);
                        crate::leanh::lean_dec(v_fst_6634_);
                        crate::leanh::lean_dec(v_cls_6620_);
                        crate::leanh::lean_dec_ref(v___f_6619_);
                        crate::leanh::lean_dec_ref(v_e_6618_);
                        v_a_6727_ = crate::leanh::lean_ctor_get(v___x_6656_, 0);
                        v_isSharedCheck_6734_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6656_)) as u8;
                        if v_isSharedCheck_6734_ == 0 {
                            v___x_6729_ = v___x_6656_;
                            v_isShared_6730_ = v_isSharedCheck_6734_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6727_);
                            crate::leanh::lean_dec(v___x_6656_);
                            v___x_6729_ = crate::leanh::lean_box(0);
                            v_isShared_6730_ = v_isSharedCheck_6734_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6654_);
                    crate::leanh::lean_dec(v_fst_6634_);
                    crate::leanh::lean_dec(v_cls_6620_);
                    crate::leanh::lean_dec_ref(v___f_6619_);
                    crate::leanh::lean_dec_ref(v_e_6618_);
                    v_val_6735_ = crate::leanh::lean_ctor_get(v_fst_6652_, 0);
                    crate::leanh::lean_inc(v_val_6735_);
                    crate::leanh::lean_dec_ref_known(v_fst_6652_, 1);
                    if v_isShared_6651_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6650_, 0, v_val_6735_);
                        v___x_6737_ = v___x_6650_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_6738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6738_, 0, v_val_6735_);
                        v___x_6737_ = v_reuseFailAlloc_6738_;
                        state = 21;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_6661_);
                v___x_6670_ = l_Lean_Meta_hasAssignableMVar(
                    v_a_6661_,
                    v___y_6627_,
                    v___y_6628_,
                    v___y_6629_,
                    v___y_6630_,
                );
                if crate::leanh::lean_obj_tag(v___x_6670_) == 0 {
                    v_a_6671_ = crate::leanh::lean_ctor_get(v___x_6670_, 0);
                    v_isSharedCheck_6717_ = (!crate::leanh::lean_is_exclusive(v___x_6670_)) as u8;
                    if v_isSharedCheck_6717_ == 0 {
                        v___x_6673_ = v___x_6670_;
                        v_isShared_6674_ = v_isSharedCheck_6717_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6671_);
                        crate::leanh::lean_dec(v___x_6670_);
                        v___x_6673_ = crate::leanh::lean_box(0);
                        v_isShared_6674_ = v_isSharedCheck_6717_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6663_);
                    crate::leanh::lean_dec(v_a_6661_);
                    crate::leanh::lean_del_object(v___x_6654_);
                    crate::leanh::lean_dec(v_cls_6620_);
                    crate::leanh::lean_dec_ref(v___f_6619_);
                    v_a_6718_ = crate::leanh::lean_ctor_get(v___x_6670_, 0);
                    v_isSharedCheck_6725_ = (!crate::leanh::lean_is_exclusive(v___x_6670_)) as u8;
                    if v_isSharedCheck_6725_ == 0 {
                        v___x_6720_ = v___x_6670_;
                        v_isShared_6721_ = v_isSharedCheck_6725_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6718_);
                        crate::leanh::lean_dec(v___x_6670_);
                        v___x_6720_ = crate::leanh::lean_box(0);
                        v_isShared_6721_ = v_isSharedCheck_6725_;
                        state = 17;
                        continue;
                    }
                }
            }
            6 => {
                v___x_6666_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6666_, 0, v_a_6661_);
                if v_isShared_6664_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6663_, 0, v___x_6666_);
                    v___x_6668_ = v___x_6663_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6669_, 0, v___x_6666_);
                    v___x_6668_ = v_reuseFailAlloc_6669_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6668_;
            }
            8 => {
                v___x_6675_ = (crate::leanh::lean_unbox(v_a_6671_) as u8);
                crate::leanh::lean_dec(v_a_6671_);
                if v___x_6675_ == 0 {
                    crate::leanh::lean_del_object(v___x_6673_);
                    v_inheritedTraceOptions_6676_ = crate::leanh::lean_ctor_get(v___y_6629_, 13);
                    crate::leanh::lean_inc(v___y_6630_);
                    crate::leanh::lean_inc_ref(v___y_6629_);
                    crate::leanh::lean_inc(v___y_6628_);
                    crate::leanh::lean_inc_ref(v___y_6627_);
                    crate::leanh::lean_inc(v___y_6626_);
                    crate::leanh::lean_inc_ref(v___y_6625_);
                    crate::leanh::lean_inc(v___y_6624_);
                    crate::leanh::lean_inc_ref(v___y_6623_);
                    crate::leanh::lean_inc(v___y_6622_);
                    crate::leanh::lean_inc(v___y_6621_);
                    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_6676_);
                    v___x_6677_ = crate::leanh::lean_apply_12(
                        v___f_6619_,
                        v_inheritedTraceOptions_6676_,
                        v___y_6621_,
                        v___y_6622_,
                        v___y_6623_,
                        v___y_6624_,
                        v___y_6625_,
                        v___y_6626_,
                        v___y_6627_,
                        v___y_6628_,
                        v___y_6629_,
                        v___y_6630_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6677_) == 0 {
                        v_a_6678_ = crate::leanh::lean_ctor_get(v___x_6677_, 0);
                        crate::leanh::lean_inc(v_a_6678_);
                        crate::leanh::lean_dec_ref_known(v___x_6677_, 1);
                        v___x_6679_ = (crate::leanh::lean_unbox(v_a_6678_) as u8);
                        crate::leanh::lean_dec(v_a_6678_);
                        if v___x_6679_ == 0 {
                            crate::leanh::lean_del_object(v___x_6654_);
                            crate::leanh::lean_dec(v_cls_6620_);
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v___y_6630_);
                            crate::leanh::lean_inc_ref(v___y_6629_);
                            crate::leanh::lean_inc(v___y_6628_);
                            crate::leanh::lean_inc_ref(v___y_6627_);
                            crate::leanh::lean_inc(v_a_6661_);
                            v___x_6680_ = lean_infer_type(
                                v_a_6661_,
                                v___y_6627_,
                                v___y_6628_,
                                v___y_6629_,
                                v___y_6630_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6680_) == 0 {
                                v_a_6681_ = crate::leanh::lean_ctor_get(v___x_6680_, 0);
                                crate::leanh::lean_inc(v_a_6681_);
                                crate::leanh::lean_dec_ref_known(v___x_6680_, 1);
                                crate::leanh::lean_inc(v_a_6661_);
                                v___x_6682_ = l_Lean_MessageData_ofExpr(v_a_6661_);
                                v___x_6683_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1_once
                                    ),
                                    _init_l_Lean_Meta_Grind_tryToProveFalse___lam__1___closed__1,
                                );
                                if v_isShared_6655_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_6654_, 7);
                                    crate::leanh::lean_ctor_set(v___x_6654_, 1, v___x_6683_);
                                    crate::leanh::lean_ctor_set(v___x_6654_, 0, v___x_6682_);
                                    v___x_6685_ = v___x_6654_;
                                    state = 9;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6697_ =
                                        crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6697_,
                                        0,
                                        v___x_6682_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6697_,
                                        1,
                                        v___x_6683_,
                                    );
                                    v___x_6685_ = v_reuseFailAlloc_6697_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_6663_);
                                crate::leanh::lean_dec(v_a_6661_);
                                crate::leanh::lean_del_object(v___x_6654_);
                                crate::leanh::lean_dec(v_cls_6620_);
                                v_a_6698_ = crate::leanh::lean_ctor_get(v___x_6680_, 0);
                                v_isSharedCheck_6705_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6680_)) as u8;
                                if v_isSharedCheck_6705_ == 0 {
                                    v___x_6700_ = v___x_6680_;
                                    v_isShared_6701_ = v_isSharedCheck_6705_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6698_);
                                    crate::leanh::lean_dec(v___x_6680_);
                                    v___x_6700_ = crate::leanh::lean_box(0);
                                    v_isShared_6701_ = v_isSharedCheck_6705_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6663_);
                        crate::leanh::lean_dec(v_a_6661_);
                        crate::leanh::lean_del_object(v___x_6654_);
                        crate::leanh::lean_dec(v_cls_6620_);
                        v_a_6706_ = crate::leanh::lean_ctor_get(v___x_6677_, 0);
                        v_isSharedCheck_6713_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6677_)) as u8;
                        if v_isSharedCheck_6713_ == 0 {
                            v___x_6708_ = v___x_6677_;
                            v_isShared_6709_ = v_isSharedCheck_6713_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6706_);
                            crate::leanh::lean_dec(v___x_6677_);
                            v___x_6708_ = crate::leanh::lean_box(0);
                            v_isShared_6709_ = v_isSharedCheck_6713_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6663_);
                    crate::leanh::lean_dec(v_a_6661_);
                    crate::leanh::lean_del_object(v___x_6654_);
                    crate::leanh::lean_dec(v_cls_6620_);
                    crate::leanh::lean_dec_ref(v___f_6619_);
                    if v_isShared_6674_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6673_, 0, v___x_6642_);
                        v___x_6715_ = v___x_6673_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_6716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 0, v___x_6642_);
                        v___x_6715_ = v_reuseFailAlloc_6716_;
                        state = 16;
                        continue;
                    }
                }
            }
            9 => {
                v___x_6686_ = l_Lean_MessageData_ofExpr(v_a_6681_);
                v___x_6687_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6687_, 0, v___x_6685_);
                crate::leanh::lean_ctor_set(v___x_6687_, 1, v___x_6686_);
                v___x_6688_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_6620_, v___x_6687_, v___y_6627_, v___y_6628_, v___y_6629_, v___y_6630_);
                if crate::leanh::lean_obj_tag(v___x_6688_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6688_, 1);
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_6663_);
                    crate::leanh::lean_dec(v_a_6661_);
                    v_a_6689_ = crate::leanh::lean_ctor_get(v___x_6688_, 0);
                    v_isSharedCheck_6696_ = (!crate::leanh::lean_is_exclusive(v___x_6688_)) as u8;
                    if v_isSharedCheck_6696_ == 0 {
                        v___x_6691_ = v___x_6688_;
                        v_isShared_6692_ = v_isSharedCheck_6696_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6689_);
                        crate::leanh::lean_dec(v___x_6688_);
                        v___x_6691_ = crate::leanh::lean_box(0);
                        v_isShared_6692_ = v_isSharedCheck_6696_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_6692_ == 0 {
                    v___x_6694_ = v___x_6691_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6695_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6695_, 0, v_a_6689_);
                    v___x_6694_ = v_reuseFailAlloc_6695_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6694_;
            }
            12 => {
                if v_isShared_6701_ == 0 {
                    v___x_6703_ = v___x_6700_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6704_, 0, v_a_6698_);
                    v___x_6703_ = v_reuseFailAlloc_6704_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6703_;
            }
            14 => {
                if v_isShared_6709_ == 0 {
                    v___x_6711_ = v___x_6708_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6712_, 0, v_a_6706_);
                    v___x_6711_ = v_reuseFailAlloc_6712_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6711_;
            }
            16 => {
                return v___x_6715_;
            }
            17 => {
                if v_isShared_6721_ == 0 {
                    v___x_6723_ = v___x_6720_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 0, v_a_6718_);
                    v___x_6723_ = v_reuseFailAlloc_6724_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6723_;
            }
            19 => {
                if v_isShared_6730_ == 0 {
                    v___x_6732_ = v___x_6729_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6733_, 0, v_a_6727_);
                    v___x_6732_ = v_reuseFailAlloc_6733_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6732_;
            }
            21 => {
                return v___x_6737_;
            }
            22 => {
                if v_isShared_6745_ == 0 {
                    v___x_6747_ = v___x_6744_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6748_, 0, v_a_6742_);
                    v___x_6747_ = v_reuseFailAlloc_6748_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6747_;
            }
            24 => {
                if v_isShared_6756_ == 0 {
                    v___x_6758_ = v___x_6755_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6759_, 0, v_a_6753_);
                    v___x_6758_ = v_reuseFailAlloc_6759_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed(
    mut v_arg_6761_: *mut crate::leanh::LeanObject,
    mut v___x_6762_: *mut crate::leanh::LeanObject,
    mut v_e_6763_: *mut crate::leanh::LeanObject,
    mut v___f_6764_: *mut crate::leanh::LeanObject,
    mut v_cls_6765_: *mut crate::leanh::LeanObject,
    mut v___y_6766_: *mut crate::leanh::LeanObject,
    mut v___y_6767_: *mut crate::leanh::LeanObject,
    mut v___y_6768_: *mut crate::leanh::LeanObject,
    mut v___y_6769_: *mut crate::leanh::LeanObject,
    mut v___y_6770_: *mut crate::leanh::LeanObject,
    mut v___y_6771_: *mut crate::leanh::LeanObject,
    mut v___y_6772_: *mut crate::leanh::LeanObject,
    mut v___y_6773_: *mut crate::leanh::LeanObject,
    mut v___y_6774_: *mut crate::leanh::LeanObject,
    mut v___y_6775_: *mut crate::leanh::LeanObject,
    mut v___y_6776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_91763__boxed_6777_: u8 = 0;
    let mut v_res_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_91763__boxed_6777_ = (crate::leanh::lean_unbox(v___x_6762_) as u8);
    v_res_6778_ = l_Lean_Meta_Grind_tryToProveFalse___lam__1(
        v_arg_6761_,
        v___x_91763__boxed_6777_,
        v_e_6763_,
        v___f_6764_,
        v_cls_6765_,
        v___y_6766_,
        v___y_6767_,
        v___y_6768_,
        v___y_6769_,
        v___y_6770_,
        v___y_6771_,
        v___y_6772_,
        v___y_6773_,
        v___y_6774_,
        v___y_6775_,
    );
    crate::leanh::lean_dec(v___y_6775_);
    crate::leanh::lean_dec_ref(v___y_6774_);
    crate::leanh::lean_dec(v___y_6773_);
    crate::leanh::lean_dec_ref(v___y_6772_);
    crate::leanh::lean_dec(v___y_6771_);
    crate::leanh::lean_dec_ref(v___y_6770_);
    crate::leanh::lean_dec(v___y_6769_);
    crate::leanh::lean_dec_ref(v___y_6768_);
    crate::leanh::lean_dec(v___y_6767_);
    crate::leanh::lean_dec(v___y_6766_);
    return v_res_6778_;
}
pub unsafe fn l_Lean_Meta_Grind_tryToProveFalse(
    mut v_e_6781_: *mut crate::leanh::LeanObject,
    mut v_a_6782_: *mut crate::leanh::LeanObject,
    mut v_a_6783_: *mut crate::leanh::LeanObject,
    mut v_a_6784_: *mut crate::leanh::LeanObject,
    mut v_a_6785_: *mut crate::leanh::LeanObject,
    mut v_a_6786_: *mut crate::leanh::LeanObject,
    mut v_a_6787_: *mut crate::leanh::LeanObject,
    mut v_a_6788_: *mut crate::leanh::LeanObject,
    mut v_a_6789_: *mut crate::leanh::LeanObject,
    mut v_a_6790_: *mut crate::leanh::LeanObject,
    mut v_a_6791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: u8 = 0;
    let mut v_arg_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: u8 = 0;
    let mut v___x_6818_: u8 = 0;
    let mut v___x_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: u8 = 0;
    let mut v___x_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6826_: u8 = 0;
    let mut v_val_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6833_: u8 = 0;
    let mut v_a_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6837_: u8 = 0;
    let mut v___x_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6841_: u8 = 0;
    let mut v_a_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6845_: u8 = 0;
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6849_: u8 = 0;
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: u8 = 0;
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inheritedTraceOptions_6796_ = crate::leanh::lean_ctor_get(v_a_6790_, 13);
                v_cls_6797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___closed__2;
                v___f_6798_ = l_Lean_Meta_Grind_tryToProveFalse___closed__0;
                v___x_6850_ = l_Lean_Meta_Grind_tryToProveFalse___lam__0(
                    v_cls_6797_,
                    v_inheritedTraceOptions_6796_,
                    v_a_6782_,
                    v_a_6783_,
                    v_a_6784_,
                    v_a_6785_,
                    v_a_6786_,
                    v_a_6787_,
                    v_a_6788_,
                    v_a_6789_,
                    v_a_6790_,
                    v_a_6791_,
                );
                v_a_6851_ = crate::leanh::lean_ctor_get(v___x_6850_, 0);
                crate::leanh::lean_inc(v_a_6851_);
                crate::leanh::lean_dec_ref(v___x_6850_);
                v___x_6852_ = (crate::leanh::lean_unbox(v_a_6851_) as u8);
                crate::leanh::lean_dec(v_a_6851_);
                if v___x_6852_ == 0 {
                    v___y_6800_ = v_a_6782_;
                    v___y_6801_ = v_a_6783_;
                    v___y_6802_ = v_a_6784_;
                    v___y_6803_ = v_a_6785_;
                    v___y_6804_ = v_a_6786_;
                    v___y_6805_ = v_a_6787_;
                    v___y_6806_ = v_a_6788_;
                    v___y_6807_ = v_a_6789_;
                    v___y_6808_ = v_a_6790_;
                    v___y_6809_ = v_a_6791_;
                    state = 2;
                    continue;
                } else {
                    v___x_6853_ = l_Lean_Meta_Grind_updateLastTag(
                        v_a_6782_, v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_,
                        v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6853_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6853_, 1);
                        crate::leanh::lean_inc_ref(v_e_6781_);
                        v___x_6854_ = l_Lean_MessageData_ofExpr(v_e_6781_);
                        v___x_6855_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_6797_, v___x_6854_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_);
                        if crate::leanh::lean_obj_tag(v___x_6855_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6855_, 1);
                            v___y_6800_ = v_a_6782_;
                            v___y_6801_ = v_a_6783_;
                            v___y_6802_ = v_a_6784_;
                            v___y_6803_ = v_a_6785_;
                            v___y_6804_ = v_a_6786_;
                            v___y_6805_ = v_a_6787_;
                            v___y_6806_ = v_a_6788_;
                            v___y_6807_ = v_a_6789_;
                            v___y_6808_ = v_a_6790_;
                            v___y_6809_ = v_a_6791_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_e_6781_);
                            return v___x_6855_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6781_);
                        return v___x_6853_;
                    }
                }
            }
            1 => {
                v___x_6794_ = crate::leanh::lean_box(0);
                v___x_6795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6795_, 0, v___x_6794_);
                return v___x_6795_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_e_6781_);
                v___x_6810_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_6781_, v___y_6807_);
                if crate::leanh::lean_obj_tag(v___x_6810_) == 0 {
                    v_a_6811_ = crate::leanh::lean_ctor_get(v___x_6810_, 0);
                    crate::leanh::lean_inc(v_a_6811_);
                    crate::leanh::lean_dec_ref_known(v___x_6810_, 1);
                    v___x_6812_ = l_Lean_Expr_cleanupAnnotations(v_a_6811_);
                    v___x_6813_ = l_Lean_Expr_isApp(v___x_6812_);
                    if v___x_6813_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_6812_);
                        crate::leanh::lean_dec_ref(v_e_6781_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_6814_ = crate::leanh::lean_ctor_get(v___x_6812_, 1);
                        crate::leanh::lean_inc_ref(v_arg_6814_);
                        v___x_6815_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6812_);
                        v___x_6816_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4;
                        v___x_6817_ = l_Lean_Expr_isConstOf(v___x_6815_, v___x_6816_);
                        crate::leanh::lean_dec_ref(v___x_6815_);
                        if v___x_6817_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_6814_);
                            crate::leanh::lean_dec_ref(v_e_6781_);
                            state = 1;
                            continue;
                        } else {
                            v___x_6818_ = 0;
                            v___x_6819_ = crate::leanh::lean_box((v___x_6818_) as usize);
                            v___f_6820_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Meta_Grind_tryToProveFalse___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                16,
                                5,
                            );
                            crate::leanh::lean_closure_set(v___f_6820_, 0, v_arg_6814_);
                            crate::leanh::lean_closure_set(v___f_6820_, 1, v___x_6819_);
                            crate::leanh::lean_closure_set(v___f_6820_, 2, v_e_6781_);
                            crate::leanh::lean_closure_set(v___f_6820_, 3, v___f_6798_);
                            crate::leanh::lean_closure_set(v___f_6820_, 4, v_cls_6797_);
                            v___x_6821_ = 0;
                            v___x_6822_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___redArg(v___f_6820_, v___x_6821_, v___y_6800_, v___y_6801_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_, v___y_6809_);
                            if crate::leanh::lean_obj_tag(v___x_6822_) == 0 {
                                v_a_6823_ = crate::leanh::lean_ctor_get(v___x_6822_, 0);
                                v_isSharedCheck_6833_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6822_)) as u8;
                                if v_isSharedCheck_6833_ == 0 {
                                    v___x_6825_ = v___x_6822_;
                                    v_isShared_6826_ = v_isSharedCheck_6833_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6823_);
                                    crate::leanh::lean_dec(v___x_6822_);
                                    v___x_6825_ = crate::leanh::lean_box(0);
                                    v_isShared_6826_ = v_isSharedCheck_6833_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v_a_6834_ = crate::leanh::lean_ctor_get(v___x_6822_, 0);
                                v_isSharedCheck_6841_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6822_)) as u8;
                                if v_isSharedCheck_6841_ == 0 {
                                    v___x_6836_ = v___x_6822_;
                                    v_isShared_6837_ = v_isSharedCheck_6841_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6834_);
                                    crate::leanh::lean_dec(v___x_6822_);
                                    v___x_6836_ = crate::leanh::lean_box(0);
                                    v_isShared_6837_ = v_isSharedCheck_6841_;
                                    state = 5;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6781_);
                    v_a_6842_ = crate::leanh::lean_ctor_get(v___x_6810_, 0);
                    v_isSharedCheck_6849_ = (!crate::leanh::lean_is_exclusive(v___x_6810_)) as u8;
                    if v_isSharedCheck_6849_ == 0 {
                        v___x_6844_ = v___x_6810_;
                        v_isShared_6845_ = v_isSharedCheck_6849_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6842_);
                        crate::leanh::lean_dec(v___x_6810_);
                        v___x_6844_ = crate::leanh::lean_box(0);
                        v_isShared_6845_ = v_isSharedCheck_6849_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_6823_) == 1 {
                    crate::leanh::lean_del_object(v___x_6825_);
                    v_val_6827_ = crate::leanh::lean_ctor_get(v_a_6823_, 0);
                    crate::leanh::lean_inc(v_val_6827_);
                    crate::leanh::lean_dec_ref_known(v_a_6823_, 1);
                    v___x_6828_ = l_Lean_Meta_Grind_closeGoal(
                        v_val_6827_,
                        v___y_6800_,
                        v___y_6801_,
                        v___y_6802_,
                        v___y_6803_,
                        v___y_6804_,
                        v___y_6805_,
                        v___y_6806_,
                        v___y_6807_,
                        v___y_6808_,
                        v___y_6809_,
                    );
                    return v___x_6828_;
                } else {
                    crate::leanh::lean_dec(v_a_6823_);
                    v___x_6829_ = crate::leanh::lean_box(0);
                    if v_isShared_6826_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6825_, 0, v___x_6829_);
                        v___x_6831_ = v___x_6825_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6832_, 0, v___x_6829_);
                        v___x_6831_ = v_reuseFailAlloc_6832_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_6831_;
            }
            5 => {
                if v_isShared_6837_ == 0 {
                    v___x_6839_ = v___x_6836_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6840_, 0, v_a_6834_);
                    v___x_6839_ = v_reuseFailAlloc_6840_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6839_;
            }
            7 => {
                if v_isShared_6845_ == 0 {
                    v___x_6847_ = v___x_6844_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6848_, 0, v_a_6842_);
                    v___x_6847_ = v_reuseFailAlloc_6848_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_tryToProveFalse___boxed(
    mut v_e_6856_: *mut crate::leanh::LeanObject,
    mut v_a_6857_: *mut crate::leanh::LeanObject,
    mut v_a_6858_: *mut crate::leanh::LeanObject,
    mut v_a_6859_: *mut crate::leanh::LeanObject,
    mut v_a_6860_: *mut crate::leanh::LeanObject,
    mut v_a_6861_: *mut crate::leanh::LeanObject,
    mut v_a_6862_: *mut crate::leanh::LeanObject,
    mut v_a_6863_: *mut crate::leanh::LeanObject,
    mut v_a_6864_: *mut crate::leanh::LeanObject,
    mut v_a_6865_: *mut crate::leanh::LeanObject,
    mut v_a_6866_: *mut crate::leanh::LeanObject,
    mut v_a_6867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6868_ = l_Lean_Meta_Grind_tryToProveFalse(
        v_e_6856_, v_a_6857_, v_a_6858_, v_a_6859_, v_a_6860_, v_a_6861_, v_a_6862_, v_a_6863_,
        v_a_6864_, v_a_6865_, v_a_6866_,
    );
    crate::leanh::lean_dec(v_a_6866_);
    crate::leanh::lean_dec_ref(v_a_6865_);
    crate::leanh::lean_dec(v_a_6864_);
    crate::leanh::lean_dec_ref(v_a_6863_);
    crate::leanh::lean_dec(v_a_6862_);
    crate::leanh::lean_dec_ref(v_a_6861_);
    crate::leanh::lean_dec(v_a_6860_);
    crate::leanh::lean_dec_ref(v_a_6859_);
    crate::leanh::lean_dec(v_a_6858_);
    crate::leanh::lean_dec(v_a_6857_);
    return v_res_6868_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6870_ = l_Lean_Meta_Grind_propagateMatchCondUp___closed__0;
    v___x_6871_ = l_Lean_stringToMessageData(v___x_6870_);
    return v___x_6871_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6873_ = l_Lean_Meta_Grind_propagateMatchCondUp___closed__2;
    v___x_6874_ = l_Lean_stringToMessageData(v___x_6873_);
    return v___x_6874_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateMatchCondUp(
    mut v_e_6875_: *mut crate::leanh::LeanObject,
    mut v_a_6876_: *mut crate::leanh::LeanObject,
    mut v_a_6877_: *mut crate::leanh::LeanObject,
    mut v_a_6878_: *mut crate::leanh::LeanObject,
    mut v_a_6879_: *mut crate::leanh::LeanObject,
    mut v_a_6880_: *mut crate::leanh::LeanObject,
    mut v_a_6881_: *mut crate::leanh::LeanObject,
    mut v_a_6882_: *mut crate::leanh::LeanObject,
    mut v_a_6883_: *mut crate::leanh::LeanObject,
    mut v_a_6884_: *mut crate::leanh::LeanObject,
    mut v_a_6885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6903_: u8 = 0;
    let mut v_cls_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: u8 = 0;
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6923_: u8 = 0;
    let mut v___x_6924_: u8 = 0;
    let mut v___x_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6932_: u8 = 0;
    let mut v_val_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: u8 = 0;
    let mut v___x_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6946_: u8 = 0;
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6950_: u8 = 0;
    let mut v___x_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: u8 = 0;
    let mut v___x_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6961_: u8 = 0;
    let mut v___x_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6965_: u8 = 0;
    let mut v_a_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6969_: u8 = 0;
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6973_: u8 = 0;
    let mut v_isSharedCheck_6974_: u8 = 0;
    let mut v_a_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6978_: u8 = 0;
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6982_: u8 = 0;
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6987_: u8 = 0;
    let mut v___x_6988_: u8 = 0;
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6994_: u8 = 0;
    let mut v_a_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6998_: u8 = 0;
    let mut v___x_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7002_: u8 = 0;
    let mut v_a_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7006_: u8 = 0;
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7010_: u8 = 0;
    let mut v___x_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: u8 = 0;
    let mut v___x_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_6901_ = crate::leanh::lean_ctor_get(v_a_6884_, 2);
                v_inheritedTraceOptions_6902_ = crate::leanh::lean_ctor_get(v_a_6884_, 13);
                v_hasTrace_6903_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_6901_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_cls_6904_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__3;
                if v_hasTrace_6903_ == 0 {
                    v___y_6906_ = v_a_6876_;
                    v___y_6907_ = v_a_6877_;
                    v___y_6908_ = v_a_6878_;
                    v___y_6909_ = v_a_6879_;
                    v___y_6910_ = v_a_6880_;
                    v___y_6911_ = v_a_6881_;
                    v___y_6912_ = v_a_6882_;
                    v___y_6913_ = v_a_6883_;
                    v___y_6914_ = v_a_6884_;
                    v___y_6915_ = v_a_6885_;
                    state = 3;
                    continue;
                } else {
                    v___x_7011_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
                    v___x_7012_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6902_,
                        v_options_6901_,
                        v___x_7011_,
                    );
                    if v___x_7012_ == 0 {
                        v___y_6906_ = v_a_6876_;
                        v___y_6907_ = v_a_6877_;
                        v___y_6908_ = v_a_6878_;
                        v___y_6909_ = v_a_6879_;
                        v___y_6910_ = v_a_6880_;
                        v___y_6911_ = v_a_6881_;
                        v___y_6912_ = v_a_6882_;
                        v___y_6913_ = v_a_6883_;
                        v___y_6914_ = v_a_6884_;
                        v___y_6915_ = v_a_6885_;
                        state = 3;
                        continue;
                    } else {
                        v___x_7013_ = l_Lean_Meta_Grind_updateLastTag(
                            v_a_6876_, v_a_6877_, v_a_6878_, v_a_6879_, v_a_6880_, v_a_6881_,
                            v_a_6882_, v_a_6883_, v_a_6884_, v_a_6885_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7013_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_7013_, 1);
                            v___x_7014_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_propagateMatchCondUp___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_propagateMatchCondUp___closed__3_once
                                ),
                                _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3,
                            );
                            crate::leanh::lean_inc_ref(v_e_6875_);
                            v___x_7015_ = l_Lean_indentExpr(v_e_6875_);
                            v___x_7016_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7016_, 0, v___x_7014_);
                            crate::leanh::lean_ctor_set(v___x_7016_, 1, v___x_7015_);
                            v___x_7017_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_6904_, v___x_7016_, v_a_6882_, v_a_6883_, v_a_6884_, v_a_6885_);
                            if crate::leanh::lean_obj_tag(v___x_7017_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7017_, 1);
                                v___y_6906_ = v_a_6876_;
                                v___y_6907_ = v_a_6877_;
                                v___y_6908_ = v_a_6878_;
                                v___y_6909_ = v_a_6879_;
                                v___y_6910_ = v_a_6880_;
                                v___y_6911_ = v_a_6881_;
                                v___y_6912_ = v_a_6882_;
                                v___y_6913_ = v_a_6883_;
                                v___y_6914_ = v_a_6884_;
                                v___y_6915_ = v_a_6885_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_e_6875_);
                                return v___x_7017_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_6875_);
                            return v___x_7013_;
                        }
                    }
                }
            }
            1 => {
                v___x_6888_ = crate::leanh::lean_box(0);
                v___x_6889_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6889_, 0, v___x_6888_);
                return v___x_6889_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_e_6875_);
                v___x_6899_ = l_Lean_Meta_mkEqTrueCore(v_e_6875_, v___y_6891_);
                v___x_6900_ = l_Lean_Meta_Grind_pushEqTrue___redArg(
                    v_e_6875_,
                    v___x_6899_,
                    v___y_6892_,
                    v___y_6893_,
                    v___y_6894_,
                    v___y_6895_,
                    v___y_6896_,
                    v___y_6897_,
                    v___y_6898_,
                );
                return v___x_6900_;
            }
            3 => {
                crate::leanh::lean_inc_ref(v_e_6875_);
                v___x_6916_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                    v_e_6875_,
                    v___y_6906_,
                    v___y_6910_,
                    v___y_6912_,
                    v___y_6913_,
                    v___y_6914_,
                    v___y_6915_,
                );
                if crate::leanh::lean_obj_tag(v___x_6916_) == 0 {
                    v_a_6917_ = crate::leanh::lean_ctor_get(v___x_6916_, 0);
                    crate::leanh::lean_inc(v_a_6917_);
                    crate::leanh::lean_dec_ref_known(v___x_6916_, 1);
                    v___x_6918_ = (crate::leanh::lean_unbox(v_a_6917_) as u8);
                    crate::leanh::lean_dec(v_a_6917_);
                    if v___x_6918_ == 0 {
                        crate::leanh::lean_inc_ref(v_e_6875_);
                        v___x_6919_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_6875_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_, v___y_6910_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_);
                        if crate::leanh::lean_obj_tag(v___x_6919_) == 0 {
                            v_a_6920_ = crate::leanh::lean_ctor_get(v___x_6919_, 0);
                            v_isSharedCheck_6974_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6919_)) as u8;
                            if v_isSharedCheck_6974_ == 0 {
                                v___x_6922_ = v___x_6919_;
                                v_isShared_6923_ = v_isSharedCheck_6974_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6920_);
                                crate::leanh::lean_dec(v___x_6919_);
                                v___x_6922_ = crate::leanh::lean_box(0);
                                v_isShared_6923_ = v_isSharedCheck_6974_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_6875_);
                            v_a_6975_ = crate::leanh::lean_ctor_get(v___x_6919_, 0);
                            v_isSharedCheck_6982_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6919_)) as u8;
                            if v_isSharedCheck_6982_ == 0 {
                                v___x_6977_ = v___x_6919_;
                                v_isShared_6978_ = v_isSharedCheck_6982_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6975_);
                                crate::leanh::lean_dec(v___x_6919_);
                                v___x_6977_ = crate::leanh::lean_box(0);
                                v_isShared_6978_ = v_isSharedCheck_6982_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v_e_6875_);
                        v___x_6983_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(v_e_6875_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_, v___y_6910_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_);
                        if crate::leanh::lean_obj_tag(v___x_6983_) == 0 {
                            v_a_6984_ = crate::leanh::lean_ctor_get(v___x_6983_, 0);
                            v_isSharedCheck_6994_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6983_)) as u8;
                            if v_isSharedCheck_6994_ == 0 {
                                v___x_6986_ = v___x_6983_;
                                v_isShared_6987_ = v_isSharedCheck_6994_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6984_);
                                crate::leanh::lean_dec(v___x_6983_);
                                v___x_6986_ = crate::leanh::lean_box(0);
                                v_isShared_6987_ = v_isSharedCheck_6994_;
                                state = 14;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_6875_);
                            v_a_6995_ = crate::leanh::lean_ctor_get(v___x_6983_, 0);
                            v_isSharedCheck_7002_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6983_)) as u8;
                            if v_isSharedCheck_7002_ == 0 {
                                v___x_6997_ = v___x_6983_;
                                v_isShared_6998_ = v_isSharedCheck_7002_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6995_);
                                crate::leanh::lean_dec(v___x_6983_);
                                v___x_6997_ = crate::leanh::lean_box(0);
                                v_isShared_6998_ = v_isSharedCheck_7002_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6875_);
                    v_a_7003_ = crate::leanh::lean_ctor_get(v___x_6916_, 0);
                    v_isSharedCheck_7010_ = (!crate::leanh::lean_is_exclusive(v___x_6916_)) as u8;
                    if v_isSharedCheck_7010_ == 0 {
                        v___x_7005_ = v___x_6916_;
                        v_isShared_7006_ = v_isSharedCheck_7010_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7003_);
                        crate::leanh::lean_dec(v___x_6916_);
                        v___x_7005_ = crate::leanh::lean_box(0);
                        v_isShared_7006_ = v_isSharedCheck_7010_;
                        state = 18;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6924_ = (crate::leanh::lean_unbox(v_a_6920_) as u8);
                crate::leanh::lean_dec(v_a_6920_);
                if v___x_6924_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_6875_);
                    v___x_6925_ = crate::leanh::lean_box(0);
                    if v_isShared_6923_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6922_, 0, v___x_6925_);
                        v___x_6927_ = v___x_6922_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6928_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6928_, 0, v___x_6925_);
                        v___x_6927_ = v_reuseFailAlloc_6928_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6922_);
                    crate::leanh::lean_inc_ref(v_e_6875_);
                    v___x_6929_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(v_e_6875_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_, v___y_6910_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_);
                    if crate::leanh::lean_obj_tag(v___x_6929_) == 0 {
                        v_a_6930_ = crate::leanh::lean_ctor_get(v___x_6929_, 0);
                        crate::leanh::lean_inc(v_a_6930_);
                        crate::leanh::lean_dec_ref_known(v___x_6929_, 1);
                        if crate::leanh::lean_obj_tag(v_a_6930_) == 1 {
                            v_options_6931_ = crate::leanh::lean_ctor_get(v___y_6914_, 2);
                            v_hasTrace_6932_ = crate::leanh::lean_ctor_get_uint8(
                                v_options_6931_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            );
                            if v_hasTrace_6932_ == 0 {
                                v_val_6933_ = crate::leanh::lean_ctor_get(v_a_6930_, 0);
                                crate::leanh::lean_inc(v_val_6933_);
                                crate::leanh::lean_dec_ref_known(v_a_6930_, 1);
                                v___y_6891_ = v_val_6933_;
                                v___y_6892_ = v___y_6906_;
                                v___y_6893_ = v___y_6908_;
                                v___y_6894_ = v___y_6910_;
                                v___y_6895_ = v___y_6912_;
                                v___y_6896_ = v___y_6913_;
                                v___y_6897_ = v___y_6914_;
                                v___y_6898_ = v___y_6915_;
                                state = 2;
                                continue;
                            } else {
                                v_val_6934_ = crate::leanh::lean_ctor_get(v_a_6930_, 0);
                                crate::leanh::lean_inc(v_val_6934_);
                                crate::leanh::lean_dec_ref_known(v_a_6930_, 1);
                                v_inheritedTraceOptions_6935_ =
                                    crate::leanh::lean_ctor_get(v___y_6914_, 13);
                                v___x_6936_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__6);
                                v___x_6937_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_6935_,
                                        v_options_6931_,
                                        v___x_6936_,
                                    );
                                if v___x_6937_ == 0 {
                                    v___y_6891_ = v_val_6934_;
                                    v___y_6892_ = v___y_6906_;
                                    v___y_6893_ = v___y_6908_;
                                    v___y_6894_ = v___y_6910_;
                                    v___y_6895_ = v___y_6912_;
                                    v___y_6896_ = v___y_6913_;
                                    v___y_6897_ = v___y_6914_;
                                    v___y_6898_ = v___y_6915_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_6938_ = l_Lean_Meta_Grind_updateLastTag(
                                        v___y_6906_,
                                        v___y_6907_,
                                        v___y_6908_,
                                        v___y_6909_,
                                        v___y_6910_,
                                        v___y_6911_,
                                        v___y_6912_,
                                        v___y_6913_,
                                        v___y_6914_,
                                        v___y_6915_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_6938_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_6938_, 1);
                                        crate::leanh::lean_inc(v___y_6915_);
                                        crate::leanh::lean_inc_ref(v___y_6914_);
                                        crate::leanh::lean_inc(v___y_6913_);
                                        crate::leanh::lean_inc_ref(v___y_6912_);
                                        crate::leanh::lean_inc(v_val_6934_);
                                        v___x_6939_ = lean_infer_type(
                                            v_val_6934_,
                                            v___y_6912_,
                                            v___y_6913_,
                                            v___y_6914_,
                                            v___y_6915_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_6939_) == 0 {
                                            v_a_6940_ = crate::leanh::lean_ctor_get(v___x_6939_, 0);
                                            crate::leanh::lean_inc(v_a_6940_);
                                            crate::leanh::lean_dec_ref_known(v___x_6939_, 1);
                                            v___x_6941_ = l_Lean_MessageData_ofExpr(v_a_6940_);
                                            v___x_6942_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(v_cls_6904_, v___x_6941_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_);
                                            if crate::leanh::lean_obj_tag(v___x_6942_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_6942_, 1);
                                                v___y_6891_ = v_val_6934_;
                                                v___y_6892_ = v___y_6906_;
                                                v___y_6893_ = v___y_6908_;
                                                v___y_6894_ = v___y_6910_;
                                                v___y_6895_ = v___y_6912_;
                                                v___y_6896_ = v___y_6913_;
                                                v___y_6897_ = v___y_6914_;
                                                v___y_6898_ = v___y_6915_;
                                                state = 2;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v_val_6934_);
                                                crate::leanh::lean_dec_ref(v_e_6875_);
                                                return v___x_6942_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_val_6934_);
                                            crate::leanh::lean_dec_ref(v_e_6875_);
                                            v_a_6943_ = crate::leanh::lean_ctor_get(v___x_6939_, 0);
                                            v_isSharedCheck_6950_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_6939_))
                                                    as u8;
                                            if v_isSharedCheck_6950_ == 0 {
                                                v___x_6945_ = v___x_6939_;
                                                v_isShared_6946_ = v_isSharedCheck_6950_;
                                                state = 6;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_6943_);
                                                crate::leanh::lean_dec(v___x_6939_);
                                                v___x_6945_ = crate::leanh::lean_box(0);
                                                v_isShared_6946_ = v_isSharedCheck_6950_;
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_val_6934_);
                                        crate::leanh::lean_dec_ref(v_e_6875_);
                                        return v___x_6938_;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6930_);
                            v___x_6951_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_6910_);
                            if crate::leanh::lean_obj_tag(v___x_6951_) == 0 {
                                v_a_6952_ = crate::leanh::lean_ctor_get(v___x_6951_, 0);
                                crate::leanh::lean_inc(v_a_6952_);
                                crate::leanh::lean_dec_ref_known(v___x_6951_, 1);
                                v___x_6953_ = (crate::leanh::lean_unbox(v_a_6952_) as u8);
                                crate::leanh::lean_dec(v_a_6952_);
                                if v___x_6953_ == 0 {
                                    crate::leanh::lean_dec_ref(v_e_6875_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_6954_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Grind_propagateMatchCondUp___closed__1
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Grind_propagateMatchCondUp___closed__1_once
                                        ),
                                        _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1,
                                    );
                                    v___x_6955_ = l_Lean_indentExpr(v_e_6875_);
                                    v___x_6956_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6956_, 0, v___x_6954_);
                                    crate::leanh::lean_ctor_set(v___x_6956_, 1, v___x_6955_);
                                    v___x_6957_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_6956_,
                                        v___y_6910_,
                                        v___y_6911_,
                                        v___y_6912_,
                                        v___y_6913_,
                                        v___y_6914_,
                                        v___y_6915_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_6957_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_6957_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_6957_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_6875_);
                                v_a_6958_ = crate::leanh::lean_ctor_get(v___x_6951_, 0);
                                v_isSharedCheck_6965_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6951_)) as u8;
                                if v_isSharedCheck_6965_ == 0 {
                                    v___x_6960_ = v___x_6951_;
                                    v_isShared_6961_ = v_isSharedCheck_6965_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6958_);
                                    crate::leanh::lean_dec(v___x_6951_);
                                    v___x_6960_ = crate::leanh::lean_box(0);
                                    v_isShared_6961_ = v_isSharedCheck_6965_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_6875_);
                        v_a_6966_ = crate::leanh::lean_ctor_get(v___x_6929_, 0);
                        v_isSharedCheck_6973_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6929_)) as u8;
                        if v_isSharedCheck_6973_ == 0 {
                            v___x_6968_ = v___x_6929_;
                            v_isShared_6969_ = v_isSharedCheck_6973_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6966_);
                            crate::leanh::lean_dec(v___x_6929_);
                            v___x_6968_ = crate::leanh::lean_box(0);
                            v_isShared_6969_ = v_isSharedCheck_6973_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_6927_;
            }
            6 => {
                if v_isShared_6946_ == 0 {
                    v___x_6948_ = v___x_6945_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6949_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6949_, 0, v_a_6943_);
                    v___x_6948_ = v_reuseFailAlloc_6949_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6948_;
            }
            8 => {
                if v_isShared_6961_ == 0 {
                    v___x_6963_ = v___x_6960_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6964_, 0, v_a_6958_);
                    v___x_6963_ = v_reuseFailAlloc_6964_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6963_;
            }
            10 => {
                if v_isShared_6969_ == 0 {
                    v___x_6971_ = v___x_6968_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6972_, 0, v_a_6966_);
                    v___x_6971_ = v_reuseFailAlloc_6972_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6971_;
            }
            12 => {
                if v_isShared_6978_ == 0 {
                    v___x_6980_ = v___x_6977_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6981_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6981_, 0, v_a_6975_);
                    v___x_6980_ = v_reuseFailAlloc_6981_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6980_;
            }
            14 => {
                v___x_6988_ = (crate::leanh::lean_unbox(v_a_6984_) as u8);
                crate::leanh::lean_dec(v_a_6984_);
                if v___x_6988_ == 0 {
                    crate::leanh::lean_del_object(v___x_6986_);
                    v___x_6989_ = l_Lean_Meta_Grind_tryToProveFalse(
                        v_e_6875_,
                        v___y_6906_,
                        v___y_6907_,
                        v___y_6908_,
                        v___y_6909_,
                        v___y_6910_,
                        v___y_6911_,
                        v___y_6912_,
                        v___y_6913_,
                        v___y_6914_,
                        v___y_6915_,
                    );
                    return v___x_6989_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_6875_);
                    v___x_6990_ = crate::leanh::lean_box(0);
                    if v_isShared_6987_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6986_, 0, v___x_6990_);
                        v___x_6992_ = v___x_6986_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_6993_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6993_, 0, v___x_6990_);
                        v___x_6992_ = v_reuseFailAlloc_6993_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                return v___x_6992_;
            }
            16 => {
                if v_isShared_6998_ == 0 {
                    v___x_7000_ = v___x_6997_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7001_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7001_, 0, v_a_6995_);
                    v___x_7000_ = v_reuseFailAlloc_7001_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7000_;
            }
            18 => {
                if v_isShared_7006_ == 0 {
                    v___x_7008_ = v___x_7005_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7009_, 0, v_a_7003_);
                    v___x_7008_ = v_reuseFailAlloc_7009_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_7008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateMatchCondUp___boxed(
    mut v_e_7018_: *mut crate::leanh::LeanObject,
    mut v_a_7019_: *mut crate::leanh::LeanObject,
    mut v_a_7020_: *mut crate::leanh::LeanObject,
    mut v_a_7021_: *mut crate::leanh::LeanObject,
    mut v_a_7022_: *mut crate::leanh::LeanObject,
    mut v_a_7023_: *mut crate::leanh::LeanObject,
    mut v_a_7024_: *mut crate::leanh::LeanObject,
    mut v_a_7025_: *mut crate::leanh::LeanObject,
    mut v_a_7026_: *mut crate::leanh::LeanObject,
    mut v_a_7027_: *mut crate::leanh::LeanObject,
    mut v_a_7028_: *mut crate::leanh::LeanObject,
    mut v_a_7029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7030_ = l_Lean_Meta_Grind_propagateMatchCondUp(
        v_e_7018_, v_a_7019_, v_a_7020_, v_a_7021_, v_a_7022_, v_a_7023_, v_a_7024_, v_a_7025_,
        v_a_7026_, v_a_7027_, v_a_7028_,
    );
    crate::leanh::lean_dec(v_a_7028_);
    crate::leanh::lean_dec_ref(v_a_7027_);
    crate::leanh::lean_dec(v_a_7026_);
    crate::leanh::lean_dec_ref(v_a_7025_);
    crate::leanh::lean_dec(v_a_7024_);
    crate::leanh::lean_dec_ref(v_a_7023_);
    crate::leanh::lean_dec(v_a_7022_);
    crate::leanh::lean_dec_ref(v_a_7021_);
    crate::leanh::lean_dec(v_a_7020_);
    crate::leanh::lean_dec(v_a_7019_);
    return v_res_7030_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7032_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4;
    v___x_7033_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_propagateMatchCondUp___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_7034_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_7032_, v___x_7033_);
    return v___x_7034_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8____boxed(
    mut v_a_7035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7036_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
    return v_res_7036_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateMatchCondDown(
    mut v_e_7037_: *mut crate::leanh::LeanObject,
    mut v_a_7038_: *mut crate::leanh::LeanObject,
    mut v_a_7039_: *mut crate::leanh::LeanObject,
    mut v_a_7040_: *mut crate::leanh::LeanObject,
    mut v_a_7041_: *mut crate::leanh::LeanObject,
    mut v_a_7042_: *mut crate::leanh::LeanObject,
    mut v_a_7043_: *mut crate::leanh::LeanObject,
    mut v_a_7044_: *mut crate::leanh::LeanObject,
    mut v_a_7045_: *mut crate::leanh::LeanObject,
    mut v_a_7046_: *mut crate::leanh::LeanObject,
    mut v_a_7047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7053_: u8 = 0;
    let mut v___x_7054_: u8 = 0;
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7063_: u8 = 0;
    let mut v___x_7064_: u8 = 0;
    let mut v___x_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7070_: u8 = 0;
    let mut v_a_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7074_: u8 = 0;
    let mut v___x_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7078_: u8 = 0;
    let mut v_isSharedCheck_7079_: u8 = 0;
    let mut v_a_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7083_: u8 = 0;
    let mut v___x_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7087_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_7037_);
                v___x_7049_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                    v_e_7037_, v_a_7038_, v_a_7042_, v_a_7044_, v_a_7045_, v_a_7046_, v_a_7047_,
                );
                if crate::leanh::lean_obj_tag(v___x_7049_) == 0 {
                    v_a_7050_ = crate::leanh::lean_ctor_get(v___x_7049_, 0);
                    v_isSharedCheck_7079_ = (!crate::leanh::lean_is_exclusive(v___x_7049_)) as u8;
                    if v_isSharedCheck_7079_ == 0 {
                        v___x_7052_ = v___x_7049_;
                        v_isShared_7053_ = v_isSharedCheck_7079_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7050_);
                        crate::leanh::lean_dec(v___x_7049_);
                        v___x_7052_ = crate::leanh::lean_box(0);
                        v_isShared_7053_ = v_isSharedCheck_7079_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_7037_);
                    v_a_7080_ = crate::leanh::lean_ctor_get(v___x_7049_, 0);
                    v_isSharedCheck_7087_ = (!crate::leanh::lean_is_exclusive(v___x_7049_)) as u8;
                    if v_isSharedCheck_7087_ == 0 {
                        v___x_7082_ = v___x_7049_;
                        v_isShared_7083_ = v_isSharedCheck_7087_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7080_);
                        crate::leanh::lean_dec(v___x_7049_);
                        v___x_7082_ = crate::leanh::lean_box(0);
                        v_isShared_7083_ = v_isSharedCheck_7087_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7054_ = (crate::leanh::lean_unbox(v_a_7050_) as u8);
                crate::leanh::lean_dec(v_a_7050_);
                if v___x_7054_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_7037_);
                    v___x_7055_ = crate::leanh::lean_box(0);
                    if v_isShared_7053_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7052_, 0, v___x_7055_);
                        v___x_7057_ = v___x_7052_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7058_, 0, v___x_7055_);
                        v___x_7057_ = v_reuseFailAlloc_7058_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7052_);
                    crate::leanh::lean_inc_ref(v_e_7037_);
                    v___x_7059_ =
                        l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(
                            v_e_7037_, v_a_7038_, v_a_7039_, v_a_7040_, v_a_7041_, v_a_7042_,
                            v_a_7043_, v_a_7044_, v_a_7045_, v_a_7046_, v_a_7047_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_7059_) == 0 {
                        v_a_7060_ = crate::leanh::lean_ctor_get(v___x_7059_, 0);
                        v_isSharedCheck_7070_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7059_)) as u8;
                        if v_isSharedCheck_7070_ == 0 {
                            v___x_7062_ = v___x_7059_;
                            v_isShared_7063_ = v_isSharedCheck_7070_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7060_);
                            crate::leanh::lean_dec(v___x_7059_);
                            v___x_7062_ = crate::leanh::lean_box(0);
                            v_isShared_7063_ = v_isSharedCheck_7070_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_7037_);
                        v_a_7071_ = crate::leanh::lean_ctor_get(v___x_7059_, 0);
                        v_isSharedCheck_7078_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7059_)) as u8;
                        if v_isSharedCheck_7078_ == 0 {
                            v___x_7073_ = v___x_7059_;
                            v_isShared_7074_ = v_isSharedCheck_7078_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7071_);
                            crate::leanh::lean_dec(v___x_7059_);
                            v___x_7073_ = crate::leanh::lean_box(0);
                            v_isShared_7074_ = v_isSharedCheck_7078_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7057_;
            }
            3 => {
                v___x_7064_ = (crate::leanh::lean_unbox(v_a_7060_) as u8);
                crate::leanh::lean_dec(v_a_7060_);
                if v___x_7064_ == 0 {
                    crate::leanh::lean_del_object(v___x_7062_);
                    v___x_7065_ = l_Lean_Meta_Grind_tryToProveFalse(
                        v_e_7037_, v_a_7038_, v_a_7039_, v_a_7040_, v_a_7041_, v_a_7042_,
                        v_a_7043_, v_a_7044_, v_a_7045_, v_a_7046_, v_a_7047_,
                    );
                    return v___x_7065_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_7037_);
                    v___x_7066_ = crate::leanh::lean_box(0);
                    if v_isShared_7063_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7062_, 0, v___x_7066_);
                        v___x_7068_ = v___x_7062_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7069_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7069_, 0, v___x_7066_);
                        v___x_7068_ = v_reuseFailAlloc_7069_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_7068_;
            }
            5 => {
                if v_isShared_7074_ == 0 {
                    v___x_7076_ = v___x_7073_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7077_, 0, v_a_7071_);
                    v___x_7076_ = v_reuseFailAlloc_7077_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7076_;
            }
            7 => {
                if v_isShared_7083_ == 0 {
                    v___x_7085_ = v___x_7082_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7086_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7086_, 0, v_a_7080_);
                    v___x_7085_ = v_reuseFailAlloc_7086_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateMatchCondDown___boxed(
    mut v_e_7088_: *mut crate::leanh::LeanObject,
    mut v_a_7089_: *mut crate::leanh::LeanObject,
    mut v_a_7090_: *mut crate::leanh::LeanObject,
    mut v_a_7091_: *mut crate::leanh::LeanObject,
    mut v_a_7092_: *mut crate::leanh::LeanObject,
    mut v_a_7093_: *mut crate::leanh::LeanObject,
    mut v_a_7094_: *mut crate::leanh::LeanObject,
    mut v_a_7095_: *mut crate::leanh::LeanObject,
    mut v_a_7096_: *mut crate::leanh::LeanObject,
    mut v_a_7097_: *mut crate::leanh::LeanObject,
    mut v_a_7098_: *mut crate::leanh::LeanObject,
    mut v_a_7099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7100_ = l_Lean_Meta_Grind_propagateMatchCondDown(
        v_e_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_, v_a_7093_, v_a_7094_, v_a_7095_,
        v_a_7096_, v_a_7097_, v_a_7098_,
    );
    crate::leanh::lean_dec(v_a_7098_);
    crate::leanh::lean_dec_ref(v_a_7097_);
    crate::leanh::lean_dec(v_a_7096_);
    crate::leanh::lean_dec_ref(v_a_7095_);
    crate::leanh::lean_dec(v_a_7094_);
    crate::leanh::lean_dec_ref(v_a_7093_);
    crate::leanh::lean_dec(v_a_7092_);
    crate::leanh::lean_dec_ref(v_a_7091_);
    crate::leanh::lean_dec(v_a_7090_);
    crate::leanh::lean_dec(v_a_7089_);
    return v_res_7100_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7102_ = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4;
    v___x_7103_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_propagateMatchCondDown___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_7104_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_7102_, v___x_7103_);
    return v___x_7104_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8____boxed(
    mut v_a_7105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7106_ = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
    return v_res_7106_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_MatchCond(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_MatchCond(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_MatchCond(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin);
}
