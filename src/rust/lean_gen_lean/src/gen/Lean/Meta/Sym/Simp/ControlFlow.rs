// Lean compiler output
// Module: Lean.Meta.Sym.Simp.ControlFlow
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.AlphaShareBuilder Lean.Meta.Sym.InferType Lean.Meta.Sym.Simp.App Lean.Meta.Sym.Util Lean.Meta.WHNF Lean.Meta.AppBuilder Init.Sym.Lemmas
use crate::r#gen::Init::Sym::Lemmas::{
    initialize_Init_Sym_Lemmas, runtime_initialize_Init_Sym_Lemmas,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_betaRev,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getBoundedAppFn, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_Expr_replaceFn, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkAppB,
    l_Lean_mkBVar, l_Lean_mkConst, l_Lean_mkLambda, l_Lean_mkNot,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkOfEqFalseCore, l_Lean_Meta_mkOfEqTrueCore,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Match::MatcherInfo::l_Lean_Meta_Match_Extension_getMatcherInfo_x3f;
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, l_Lean_Meta_Sym_Internal_Sym_assertShared,
    l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
    runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::InferType::{
    initialize_Lean_Meta_Sym_InferType, l_Lean_Meta_Sym_mkEqRefl___redArg,
    runtime_initialize_Lean_Meta_Sym_InferType,
};
use crate::r#gen::Lean::Meta::Sym::Simp::App::{
    initialize_Lean_Meta_Sym_Simp_App, l_Lean_Meta_Sym_Simp_propagateOverApplied,
    l_Lean_Meta_Sym_Simp_simpAppArgRange, runtime_initialize_Lean_Meta_Sym_Simp_App,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, l_Lean_Meta_Sym_Simp_mkRflResult,
    runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getBoolFalseExpr___redArg, l_Lean_Meta_Sym_getBoolTrueExpr___redArg,
    l_Lean_Meta_Sym_isFalseExpr___redArg, l_Lean_Meta_Sym_isTrueExpr___redArg,
    l_Lean_Meta_Sym_shareCommon___redArg, l_Lean_Meta_Sym_shareCommonInc___redArg,
};
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_foldProjs, runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_trySynthInstance;
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_reduceRecMatcher_x3f, runtime_initialize_Lean_Meta_WHNF,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_lt, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Sym::Simp::SimpM::lean_sym_simp;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18356704233129443855 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 116, 101, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,2772357888408479705 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 116, 101, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,7092435127666596636 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6_value) as *mut crate::leanh::LeanObject,4342836574150310743 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 116, 101, 95, 99, 111, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value) as *mut crate::leanh::LeanObject,3782814055319769887 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11_value) as *mut crate::leanh::LeanObject,6903251136980284309 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13_value) as *mut crate::leanh::LeanObject,15684782314253460228 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15_value) as *mut crate::leanh::LeanObject,7490975742882862809 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,8391571994004792969 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 111, 116, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,9941313967319291291 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 105, 116, 101, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6_value) as *mut crate::leanh::LeanObject,557460064797095758 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 110, 116, 114, 111, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8_value) as *mut crate::leanh::LeanObject,11870096045526947150 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,18067798339771668657 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 116, 101, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13_value) as *mut crate::leanh::LeanObject,15199346438430382657 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 112, 114, 95, 112, 114, 111, 112, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18_value) as *mut crate::leanh::LeanObject,15841710565803995561 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 112, 114, 95, 110, 111, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22_value) as *mut crate::leanh::LeanObject,13082247772038117497 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [100, 105, 116, 101, 95, 99, 111, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value) as *mut crate::leanh::LeanObject,3782814055319769887 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25_value) as *mut crate::leanh::LeanObject,3329307374202973768 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [100, 105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27_value) as *mut crate::leanh::LeanObject,15303888708270464921 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29_value) as *mut crate::leanh::LeanObject,187051596005140493 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0_value:
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
    m_data: [99, 111, 110, 100, 0],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        105488867511536770 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2_value:
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
    m_data: [99, 111, 110, 100, 95, 102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16603749333725961314 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4_value:
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
    m_data: [99, 111, 110, 100, 95, 116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4_value)
            as *mut crate::leanh::LeanObject,
        6495813663925495455 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        99, 111, 110, 100, 95, 99, 111, 110, 100, 95, 99, 111, 110, 103, 114, 0,
    ],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value) as *mut crate::leanh::LeanObject,3782814055319769887 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6_value)
            as *mut crate::leanh::LeanObject,
        1858992001746592809 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        99, 111, 110, 100, 95, 99, 111, 110, 100, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0,
    ],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value) as *mut crate::leanh::LeanObject,3782814055319769887 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8_value)
            as *mut crate::leanh::LeanObject,
        16206333800707745046 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10_value:
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
        99, 111, 110, 100, 95, 99, 111, 110, 100, 95, 101, 113, 95, 116, 114, 117, 101, 0,
    ],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value) as *mut crate::leanh::LeanObject,3782814055319769887 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10_value)
            as *mut crate::leanh::LeanObject,
        10653762770444086580 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(
    mut v_f_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
    mut v___y_1301_: *mut crate::leanh::LeanObject,
    mut v___y_1302_: *mut crate::leanh::LeanObject,
    mut v___y_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1313_: u8 = 0;
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut v_a_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1327_: u8 = 0;
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1312_ = lean_st_ref_get(v___y_1302_);
                v_debug_1313_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1312_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_1312_);
                if v_debug_1313_ == 0 {
                    v___y_1309_ = v___y_1302_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_1299_);
                    v___x_1314_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_1299_,
                        v___y_1301_,
                        v___y_1302_,
                        v___y_1303_,
                        v___y_1304_,
                        v___y_1305_,
                        v___y_1306_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1314_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1314_, 1);
                        crate::leanh::lean_inc_ref(v_a_1300_);
                        v___x_1315_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_1300_,
                            v___y_1301_,
                            v___y_1302_,
                            v___y_1303_,
                            v___y_1304_,
                            v___y_1305_,
                            v___y_1306_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1315_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1315_, 1);
                            v___y_1309_ = v___y_1302_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_1300_);
                            crate::leanh::lean_dec_ref(v_f_1299_);
                            v_a_1316_ = crate::leanh::lean_ctor_get(v___x_1315_, 0);
                            v_isSharedCheck_1323_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1315_)) as u8;
                            if v_isSharedCheck_1323_ == 0 {
                                v___x_1318_ = v___x_1315_;
                                v_isShared_1319_ = v_isSharedCheck_1323_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1316_);
                                crate::leanh::lean_dec(v___x_1315_);
                                v___x_1318_ = crate::leanh::lean_box(0);
                                v_isShared_1319_ = v_isSharedCheck_1323_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_1300_);
                        crate::leanh::lean_dec_ref(v_f_1299_);
                        v_a_1324_ = crate::leanh::lean_ctor_get(v___x_1314_, 0);
                        v_isSharedCheck_1331_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1314_)) as u8;
                        if v_isSharedCheck_1331_ == 0 {
                            v___x_1326_ = v___x_1314_;
                            v_isShared_1327_ = v_isSharedCheck_1331_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1324_);
                            crate::leanh::lean_dec(v___x_1314_);
                            v___x_1326_ = crate::leanh::lean_box(0);
                            v_isShared_1327_ = v_isSharedCheck_1331_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1310_ = l_Lean_Expr_app___override(v_f_1299_, v_a_1300_);
                v___x_1311_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1310_, v___y_1309_);
                return v___x_1311_;
            }
            2 => {
                if v_isShared_1319_ == 0 {
                    v___x_1321_ = v___x_1318_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
                    v___x_1321_ = v_reuseFailAlloc_1322_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1321_;
            }
            4 => {
                if v_isShared_1327_ == 0 {
                    v___x_1329_ = v___x_1326_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
                    v___x_1329_ = v_reuseFailAlloc_1330_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg___boxed(
    mut v_f_1332_: *mut crate::leanh::LeanObject,
    mut v_a_1333_: *mut crate::leanh::LeanObject,
    mut v___y_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1341_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_f_1332_, v_a_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
    crate::leanh::lean_dec(v___y_1339_);
    crate::leanh::lean_dec_ref(v___y_1338_);
    crate::leanh::lean_dec(v___y_1337_);
    crate::leanh::lean_dec_ref(v___y_1336_);
    crate::leanh::lean_dec(v___y_1335_);
    crate::leanh::lean_dec_ref(v___y_1334_);
    return v_res_1341_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(
    mut v_f_1342_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_1343_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_1344_: *mut crate::leanh::LeanObject,
    mut v___y_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
    mut v___y_1349_: *mut crate::leanh::LeanObject,
    mut v___y_1350_: *mut crate::leanh::LeanObject,
    mut v___y_1351_: *mut crate::leanh::LeanObject,
    mut v___y_1352_: *mut crate::leanh::LeanObject,
    mut v___y_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_f_1342_, v_a_u2081_1343_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
    if crate::leanh::lean_obj_tag(v___x_1355_) == 0 {
        let mut v_a_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1356_ = crate::leanh::lean_ctor_get(v___x_1355_, 0);
        crate::leanh::lean_inc(v_a_1356_);
        crate::leanh::lean_dec_ref_known(v___x_1355_, 1);
        v___x_1357_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_a_1356_, v_a_u2082_1344_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
        return v___x_1357_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2082_1344_);
        return v___x_1355_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1___boxed(
    mut v_f_1358_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_1359_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
    mut v___y_1366_: *mut crate::leanh::LeanObject,
    mut v___y_1367_: *mut crate::leanh::LeanObject,
    mut v___y_1368_: *mut crate::leanh::LeanObject,
    mut v___y_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1371_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(v_f_1358_, v_a_u2081_1359_, v_a_u2082_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
    crate::leanh::lean_dec(v___y_1369_);
    crate::leanh::lean_dec_ref(v___y_1368_);
    crate::leanh::lean_dec(v___y_1367_);
    crate::leanh::lean_dec_ref(v___y_1366_);
    crate::leanh::lean_dec(v___y_1365_);
    crate::leanh::lean_dec_ref(v___y_1364_);
    crate::leanh::lean_dec(v___y_1363_);
    crate::leanh::lean_dec_ref(v___y_1362_);
    crate::leanh::lean_dec(v___y_1361_);
    return v_res_1371_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(
    mut v_f_1372_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_1373_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_1374_: *mut crate::leanh::LeanObject,
    mut v_a_u2083_1375_: *mut crate::leanh::LeanObject,
    mut v___y_1376_: *mut crate::leanh::LeanObject,
    mut v___y_1377_: *mut crate::leanh::LeanObject,
    mut v___y_1378_: *mut crate::leanh::LeanObject,
    mut v___y_1379_: *mut crate::leanh::LeanObject,
    mut v___y_1380_: *mut crate::leanh::LeanObject,
    mut v___y_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(v_f_1372_, v_a_u2081_1373_, v_a_u2082_1374_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
    if crate::leanh::lean_obj_tag(v___x_1386_) == 0 {
        let mut v_a_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1387_ = crate::leanh::lean_ctor_get(v___x_1386_, 0);
        crate::leanh::lean_inc(v_a_1387_);
        crate::leanh::lean_dec_ref_known(v___x_1386_, 1);
        v___x_1388_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_a_1387_, v_a_u2083_1375_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
        return v___x_1388_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2083_1375_);
        return v___x_1386_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0___boxed(
    mut v_f_1389_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_1390_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_1391_: *mut crate::leanh::LeanObject,
    mut v_a_u2083_1392_: *mut crate::leanh::LeanObject,
    mut v___y_1393_: *mut crate::leanh::LeanObject,
    mut v___y_1394_: *mut crate::leanh::LeanObject,
    mut v___y_1395_: *mut crate::leanh::LeanObject,
    mut v___y_1396_: *mut crate::leanh::LeanObject,
    mut v___y_1397_: *mut crate::leanh::LeanObject,
    mut v___y_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
    mut v___y_1400_: *mut crate::leanh::LeanObject,
    mut v___y_1401_: *mut crate::leanh::LeanObject,
    mut v___y_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(v_f_1389_, v_a_u2081_1390_, v_a_u2082_1391_, v_a_u2083_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
    crate::leanh::lean_dec(v___y_1401_);
    crate::leanh::lean_dec_ref(v___y_1400_);
    crate::leanh::lean_dec(v___y_1399_);
    crate::leanh::lean_dec_ref(v___y_1398_);
    crate::leanh::lean_dec(v___y_1397_);
    crate::leanh::lean_dec_ref(v___y_1396_);
    crate::leanh::lean_dec(v___y_1395_);
    crate::leanh::lean_dec_ref(v___y_1394_);
    crate::leanh::lean_dec(v___y_1393_);
    return v_res_1403_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(
    mut v_f_1404_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_1405_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_1406_: *mut crate::leanh::LeanObject,
    mut v_a_u2083_1407_: *mut crate::leanh::LeanObject,
    mut v_a_u2084_1408_: *mut crate::leanh::LeanObject,
    mut v___y_1409_: *mut crate::leanh::LeanObject,
    mut v___y_1410_: *mut crate::leanh::LeanObject,
    mut v___y_1411_: *mut crate::leanh::LeanObject,
    mut v___y_1412_: *mut crate::leanh::LeanObject,
    mut v___y_1413_: *mut crate::leanh::LeanObject,
    mut v___y_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1419_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(v_f_1404_, v_a_u2081_1405_, v_a_u2082_1406_, v_a_u2083_1407_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
    if crate::leanh::lean_obj_tag(v___x_1419_) == 0 {
        let mut v_a_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1420_ = crate::leanh::lean_ctor_get(v___x_1419_, 0);
        crate::leanh::lean_inc(v_a_1420_);
        crate::leanh::lean_dec_ref_known(v___x_1419_, 1);
        v___x_1421_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_a_1420_, v_a_u2084_1408_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
        return v___x_1421_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2084_1408_);
        return v___x_1419_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0___boxed(
    mut v_f_1422_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_1423_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_1424_: *mut crate::leanh::LeanObject,
    mut v_a_u2083_1425_: *mut crate::leanh::LeanObject,
    mut v_a_u2084_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1437_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(v_f_1422_, v_a_u2081_1423_, v_a_u2082_1424_, v_a_u2083_1425_, v_a_u2084_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
    crate::leanh::lean_dec(v___y_1435_);
    crate::leanh::lean_dec_ref(v___y_1434_);
    crate::leanh::lean_dec(v___y_1433_);
    crate::leanh::lean_dec_ref(v___y_1432_);
    crate::leanh::lean_dec(v___y_1431_);
    crate::leanh::lean_dec_ref(v___y_1430_);
    crate::leanh::lean_dec(v___y_1429_);
    crate::leanh::lean_dec_ref(v___y_1428_);
    crate::leanh::lean_dec(v___y_1427_);
    return v_res_1437_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1450_ = crate::leanh::lean_box(0);
    v___x_1451_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7;
    v___x_1452_ = l_Lean_mkConst(v___x_1451_, v___x_1450_);
    return v___x_1452_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(
    mut v___x_1466_: u8,
    mut v_e_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
    mut v___y_1469_: *mut crate::leanh::LeanObject,
    mut v___y_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
    mut v___y_1473_: *mut crate::leanh::LeanObject,
    mut v___y_1474_: *mut crate::leanh::LeanObject,
    mut v___y_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    let mut v_arg_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: u8 = 0;
    let mut v_arg_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    let mut v_arg_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v_arg_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_1500_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1511_: u8 = 0;
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1526_: u8 = 0;
    let mut v_a_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut v_a_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1547_: u8 = 0;
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1551_: u8 = 0;
    let mut v_e_x27_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_1554_: u8 = 0;
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1557_: u8 = 0;
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1568_: u8 = 0;
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v_a_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1587_: u8 = 0;
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v_a_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1601_: u8 = 0;
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1605_: u8 = 0;
    let mut v_a_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1609_: u8 = 0;
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1613_: u8 = 0;
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_a_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1624_: u8 = 0;
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: u8 = 0;
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut v_a_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1643_: u8 = 0;
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1657_: u8 = 0;
    let mut v_a_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1661_: u8 = 0;
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1467_);
                v___x_1481_ = l_Lean_Expr_cleanupAnnotations(v_e_1467_);
                v___x_1482_ = l_Lean_Expr_isApp(v___x_1481_);
                if v___x_1482_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1481_);
                    crate::leanh::lean_dec_ref(v_e_1467_);
                    state = 1;
                    continue;
                } else {
                    v_arg_1483_ = crate::leanh::lean_ctor_get(v___x_1481_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1483_);
                    v___x_1484_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1481_);
                    v___x_1485_ = l_Lean_Expr_isApp(v___x_1484_);
                    if v___x_1485_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1484_);
                        crate::leanh::lean_dec_ref(v_arg_1483_);
                        crate::leanh::lean_dec_ref(v_e_1467_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_1486_ = crate::leanh::lean_ctor_get(v___x_1484_, 1);
                        crate::leanh::lean_inc_ref(v_arg_1486_);
                        v___x_1487_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1484_);
                        v___x_1488_ = l_Lean_Expr_isApp(v___x_1487_);
                        if v___x_1488_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1487_);
                            crate::leanh::lean_dec_ref(v_arg_1486_);
                            crate::leanh::lean_dec_ref(v_arg_1483_);
                            crate::leanh::lean_dec_ref(v_e_1467_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1489_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1487_);
                            v___x_1490_ = l_Lean_Expr_isApp(v___x_1489_);
                            if v___x_1490_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_1489_);
                                crate::leanh::lean_dec_ref(v_arg_1486_);
                                crate::leanh::lean_dec_ref(v_arg_1483_);
                                crate::leanh::lean_dec_ref(v_e_1467_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_1491_ = crate::leanh::lean_ctor_get(v___x_1489_, 1);
                                crate::leanh::lean_inc_ref(v_arg_1491_);
                                v___x_1492_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1489_);
                                v___x_1493_ = l_Lean_Expr_isApp(v___x_1492_);
                                if v___x_1493_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_1492_);
                                    crate::leanh::lean_dec_ref(v_arg_1491_);
                                    crate::leanh::lean_dec_ref(v_arg_1486_);
                                    crate::leanh::lean_dec_ref(v_arg_1483_);
                                    crate::leanh::lean_dec_ref(v_e_1467_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_1494_ = crate::leanh::lean_ctor_get(v___x_1492_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_1494_);
                                    v___x_1495_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1492_);
                                    v___x_1496_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1;
                                    v___x_1497_ = l_Lean_Expr_isConstOf(v___x_1495_, v___x_1496_);
                                    if v___x_1497_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_1495_);
                                        crate::leanh::lean_dec_ref(v_arg_1494_);
                                        crate::leanh::lean_dec_ref(v_arg_1491_);
                                        crate::leanh::lean_dec_ref(v_arg_1486_);
                                        crate::leanh::lean_dec_ref(v_arg_1483_);
                                        crate::leanh::lean_dec_ref(v_e_1467_);
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v___y_1476_);
                                        crate::leanh::lean_inc_ref(v___y_1475_);
                                        crate::leanh::lean_inc(v___y_1474_);
                                        crate::leanh::lean_inc_ref(v___y_1473_);
                                        crate::leanh::lean_inc(v___y_1472_);
                                        crate::leanh::lean_inc_ref(v___y_1471_);
                                        crate::leanh::lean_inc(v___y_1470_);
                                        crate::leanh::lean_inc_ref(v___y_1469_);
                                        crate::leanh::lean_inc(v___y_1468_);
                                        crate::leanh::lean_inc_ref(v_arg_1491_);
                                        v___x_1498_ = lean_sym_simp(
                                            v_arg_1491_,
                                            v___y_1468_,
                                            v___y_1469_,
                                            v___y_1470_,
                                            v___y_1471_,
                                            v___y_1472_,
                                            v___y_1473_,
                                            v___y_1474_,
                                            v___y_1475_,
                                            v___y_1476_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_1498_) == 0 {
                                            v_a_1499_ = crate::leanh::lean_ctor_get(v___x_1498_, 0);
                                            crate::leanh::lean_inc(v_a_1499_);
                                            crate::leanh::lean_dec_ref_known(v___x_1498_, 1);
                                            if crate::leanh::lean_obj_tag(v_a_1499_) == 0 {
                                                crate::leanh::lean_dec_ref(v_e_1467_);
                                                v_contextDependent_1500_ =
                                                    crate::leanh::lean_ctor_get_uint8(
                                                        v_a_1499_, 1 as u32,
                                                    );
                                                crate::leanh::lean_dec_ref_known(v_a_1499_, 0);
                                                v___x_1501_ = l_Lean_Meta_Sym_isTrueExpr___redArg(
                                                    v_arg_1491_,
                                                    v___y_1471_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_1501_) == 0 {
                                                    v_a_1502_ =
                                                        crate::leanh::lean_ctor_get(v___x_1501_, 0);
                                                    v_isSharedCheck_1543_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_1501_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_1543_ == 0 {
                                                        v___x_1504_ = v___x_1501_;
                                                        v_isShared_1505_ = v_isSharedCheck_1543_;
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_1502_);
                                                        crate::leanh::lean_dec(v___x_1501_);
                                                        v___x_1504_ = crate::leanh::lean_box(0);
                                                        v_isShared_1505_ = v_isSharedCheck_1543_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_1495_);
                                                    crate::leanh::lean_dec_ref(v_arg_1494_);
                                                    crate::leanh::lean_dec_ref(v_arg_1491_);
                                                    crate::leanh::lean_dec_ref(v_arg_1486_);
                                                    crate::leanh::lean_dec_ref(v_arg_1483_);
                                                    v_a_1544_ =
                                                        crate::leanh::lean_ctor_get(v___x_1501_, 0);
                                                    v_isSharedCheck_1551_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_1501_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_1551_ == 0 {
                                                        v___x_1546_ = v___x_1501_;
                                                        v_isShared_1547_ = v_isSharedCheck_1551_;
                                                        state = 9;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_1544_);
                                                        crate::leanh::lean_dec(v___x_1501_);
                                                        v___x_1546_ = crate::leanh::lean_box(0);
                                                        v_isShared_1547_ = v_isSharedCheck_1551_;
                                                        state = 9;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_1495_);
                                                crate::leanh::lean_dec_ref(v_arg_1494_);
                                                crate::leanh::lean_dec_ref(v_arg_1491_);
                                                v_e_x27_1552_ =
                                                    crate::leanh::lean_ctor_get(v_a_1499_, 0);
                                                v_proof_1553_ =
                                                    crate::leanh::lean_ctor_get(v_a_1499_, 1);
                                                v_contextDependent_1554_ =
                                                    crate::leanh::lean_ctor_get_uint8(
                                                        v_a_1499_,
                                                        (core::mem::size_of::<
                                                            *mut crate::leanh::LeanObject,
                                                        >(
                                                        ) * 2
                                                            + 1)
                                                            as u32,
                                                    );
                                                v_isSharedCheck_1666_ =
                                                    (!crate::leanh::lean_is_exclusive(v_a_1499_))
                                                        as u8;
                                                if v_isSharedCheck_1666_ == 0 {
                                                    v___x_1556_ = v_a_1499_;
                                                    v_isShared_1557_ = v_isSharedCheck_1666_;
                                                    state = 11;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_proof_1553_);
                                                    crate::leanh::lean_inc(v_e_x27_1552_);
                                                    crate::leanh::lean_dec(v_a_1499_);
                                                    v___x_1556_ = crate::leanh::lean_box(0);
                                                    v_isShared_1557_ = v_isSharedCheck_1666_;
                                                    state = 11;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_1495_);
                                            crate::leanh::lean_dec_ref(v_arg_1494_);
                                            crate::leanh::lean_dec_ref(v_arg_1491_);
                                            crate::leanh::lean_dec_ref(v_arg_1486_);
                                            crate::leanh::lean_dec_ref(v_arg_1483_);
                                            crate::leanh::lean_dec_ref(v_e_1467_);
                                            return v___x_1498_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1479_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_1479_, 0 as u32, v___x_1466_);
                crate::leanh::lean_ctor_set_uint8(v___x_1479_, 1 as u32, v___x_1466_);
                v___x_1480_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1480_, 0, v___x_1479_);
                return v___x_1480_;
            }
            2 => {
                v___x_1506_ = (crate::leanh::lean_unbox(v_a_1502_) as u8);
                if v___x_1506_ == 0 {
                    crate::leanh::lean_del_object(v___x_1504_);
                    v___x_1507_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_1491_, v___y_1471_);
                    crate::leanh::lean_dec_ref(v_arg_1491_);
                    if crate::leanh::lean_obj_tag(v___x_1507_) == 0 {
                        v_a_1508_ = crate::leanh::lean_ctor_get(v___x_1507_, 0);
                        v_isSharedCheck_1526_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1507_)) as u8;
                        if v_isSharedCheck_1526_ == 0 {
                            v___x_1510_ = v___x_1507_;
                            v_isShared_1511_ = v_isSharedCheck_1526_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1508_);
                            crate::leanh::lean_dec(v___x_1507_);
                            v___x_1510_ = crate::leanh::lean_box(0);
                            v_isShared_1511_ = v_isSharedCheck_1526_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1502_);
                        crate::leanh::lean_dec_ref(v___x_1495_);
                        crate::leanh::lean_dec_ref(v_arg_1494_);
                        crate::leanh::lean_dec_ref(v_arg_1486_);
                        crate::leanh::lean_dec_ref(v_arg_1483_);
                        v_a_1527_ = crate::leanh::lean_ctor_get(v___x_1507_, 0);
                        v_isSharedCheck_1534_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1507_)) as u8;
                        if v_isSharedCheck_1534_ == 0 {
                            v___x_1529_ = v___x_1507_;
                            v_isShared_1530_ = v_isSharedCheck_1534_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1527_);
                            crate::leanh::lean_dec(v___x_1507_);
                            v___x_1529_ = crate::leanh::lean_box(0);
                            v_isShared_1530_ = v_isSharedCheck_1534_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1502_);
                    crate::leanh::lean_dec_ref(v_arg_1491_);
                    v___x_1535_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5;
                    v___x_1536_ = l_Lean_Expr_constLevels_x21(v___x_1495_);
                    crate::leanh::lean_dec_ref(v___x_1495_);
                    v___x_1537_ = l_Lean_mkConst(v___x_1535_, v___x_1536_);
                    crate::leanh::lean_inc_ref(v_arg_1486_);
                    v___x_1538_ = l_Lean_mkApp3(v___x_1537_, v_arg_1494_, v_arg_1486_, v_arg_1483_);
                    v___x_1539_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_1539_, 0, v_arg_1486_);
                    crate::leanh::lean_ctor_set(v___x_1539_, 1, v___x_1538_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1539_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_1466_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1539_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_1500_,
                    );
                    if v_isShared_1505_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1504_, 0, v___x_1539_);
                        v___x_1541_ = v___x_1504_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
                        v___x_1541_ = v_reuseFailAlloc_1542_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1512_ = (crate::leanh::lean_unbox(v_a_1508_) as u8);
                crate::leanh::lean_dec(v_a_1508_);
                if v___x_1512_ == 0 {
                    crate::leanh::lean_dec(v_a_1502_);
                    crate::leanh::lean_dec_ref(v___x_1495_);
                    crate::leanh::lean_dec_ref(v_arg_1494_);
                    crate::leanh::lean_dec_ref(v_arg_1486_);
                    crate::leanh::lean_dec_ref(v_arg_1483_);
                    v___x_1513_ =
                        l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1497_, v_contextDependent_1500_);
                    if v_isShared_1511_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1513_);
                        v___x_1515_ = v___x_1510_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
                        v___x_1515_ = v_reuseFailAlloc_1516_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_1517_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3;
                    v___x_1518_ = l_Lean_Expr_constLevels_x21(v___x_1495_);
                    crate::leanh::lean_dec_ref(v___x_1495_);
                    v___x_1519_ = l_Lean_mkConst(v___x_1517_, v___x_1518_);
                    crate::leanh::lean_inc_ref(v_arg_1483_);
                    v___x_1520_ = l_Lean_mkApp3(v___x_1519_, v_arg_1494_, v_arg_1486_, v_arg_1483_);
                    v___x_1521_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_1521_, 0, v_arg_1483_);
                    crate::leanh::lean_ctor_set(v___x_1521_, 1, v___x_1520_);
                    v___x_1522_ = (crate::leanh::lean_unbox(v_a_1502_) as u8);
                    crate::leanh::lean_dec(v_a_1502_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1521_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_1522_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1521_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_1500_,
                    );
                    if v_isShared_1511_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1510_, 0, v___x_1521_);
                        v___x_1524_ = v___x_1510_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1525_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1521_);
                        v___x_1524_ = v_reuseFailAlloc_1525_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1515_;
            }
            5 => {
                return v___x_1524_;
            }
            6 => {
                if v_isShared_1530_ == 0 {
                    v___x_1532_ = v___x_1529_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1533_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
                    v___x_1532_ = v_reuseFailAlloc_1533_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1532_;
            }
            8 => {
                return v___x_1541_;
            }
            9 => {
                if v_isShared_1547_ == 0 {
                    v___x_1549_ = v___x_1546_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1550_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
                    v___x_1549_ = v_reuseFailAlloc_1550_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1549_;
            }
            11 => {
                v___x_1558_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1552_, v___y_1471_);
                if crate::leanh::lean_obj_tag(v___x_1558_) == 0 {
                    v_a_1559_ = crate::leanh::lean_ctor_get(v___x_1558_, 0);
                    v_isSharedCheck_1657_ = (!crate::leanh::lean_is_exclusive(v___x_1558_)) as u8;
                    if v_isSharedCheck_1657_ == 0 {
                        v___x_1561_ = v___x_1558_;
                        v_isShared_1562_ = v_isSharedCheck_1657_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1559_);
                        crate::leanh::lean_dec(v___x_1558_);
                        v___x_1561_ = crate::leanh::lean_box(0);
                        v_isShared_1562_ = v_isSharedCheck_1657_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1556_);
                    crate::leanh::lean_dec_ref(v_proof_1553_);
                    crate::leanh::lean_dec_ref(v_e_x27_1552_);
                    crate::leanh::lean_dec_ref(v_arg_1486_);
                    crate::leanh::lean_dec_ref(v_arg_1483_);
                    crate::leanh::lean_dec_ref(v_e_1467_);
                    v_a_1658_ = crate::leanh::lean_ctor_get(v___x_1558_, 0);
                    v_isSharedCheck_1665_ = (!crate::leanh::lean_is_exclusive(v___x_1558_)) as u8;
                    if v_isSharedCheck_1665_ == 0 {
                        v___x_1660_ = v___x_1558_;
                        v_isShared_1661_ = v_isSharedCheck_1665_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1658_);
                        crate::leanh::lean_dec(v___x_1558_);
                        v___x_1660_ = crate::leanh::lean_box(0);
                        v_isShared_1661_ = v_isSharedCheck_1665_;
                        state = 31;
                        continue;
                    }
                }
            }
            12 => {
                v___x_1563_ = (crate::leanh::lean_unbox(v_a_1559_) as u8);
                if v___x_1563_ == 0 {
                    crate::leanh::lean_del_object(v___x_1561_);
                    v___x_1564_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_1552_, v___y_1471_);
                    if crate::leanh::lean_obj_tag(v___x_1564_) == 0 {
                        v_a_1565_ = crate::leanh::lean_ctor_get(v___x_1564_, 0);
                        v_isSharedCheck_1639_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1564_)) as u8;
                        if v_isSharedCheck_1639_ == 0 {
                            v___x_1567_ = v___x_1564_;
                            v_isShared_1568_ = v_isSharedCheck_1639_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1565_);
                            crate::leanh::lean_dec(v___x_1564_);
                            v___x_1567_ = crate::leanh::lean_box(0);
                            v_isShared_1568_ = v_isSharedCheck_1639_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1559_);
                        crate::leanh::lean_del_object(v___x_1556_);
                        crate::leanh::lean_dec_ref(v_proof_1553_);
                        crate::leanh::lean_dec_ref(v_e_x27_1552_);
                        crate::leanh::lean_dec_ref(v_arg_1486_);
                        crate::leanh::lean_dec_ref(v_arg_1483_);
                        crate::leanh::lean_dec_ref(v_e_1467_);
                        v_a_1640_ = crate::leanh::lean_ctor_get(v___x_1564_, 0);
                        v_isSharedCheck_1647_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1564_)) as u8;
                        if v_isSharedCheck_1647_ == 0 {
                            v___x_1642_ = v___x_1564_;
                            v_isShared_1643_ = v_isSharedCheck_1647_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1640_);
                            crate::leanh::lean_dec(v___x_1564_);
                            v___x_1642_ = crate::leanh::lean_box(0);
                            v_isShared_1643_ = v_isSharedCheck_1647_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1559_);
                    crate::leanh::lean_dec_ref(v_e_x27_1552_);
                    crate::leanh::lean_dec_ref(v_arg_1483_);
                    v___x_1648_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16;
                    v___x_1649_ = l_Lean_Expr_replaceFn(v_e_1467_, v___x_1648_);
                    v___x_1650_ = l_Lean_Expr_app___override(v___x_1649_, v_proof_1553_);
                    if v_isShared_1557_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1556_, 1, v___x_1650_);
                        crate::leanh::lean_ctor_set(v___x_1556_, 0, v_arg_1486_);
                        v___x_1652_ = v___x_1556_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_1656_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_arg_1486_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___x_1650_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1656_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                            v_contextDependent_1554_,
                        );
                        v___x_1652_ = v_reuseFailAlloc_1656_;
                        state = 29;
                        continue;
                    }
                }
            }
            13 => {
                v___x_1569_ = (crate::leanh::lean_unbox(v_a_1565_) as u8);
                if v___x_1569_ == 0 {
                    crate::leanh::lean_del_object(v___x_1567_);
                    crate::leanh::lean_dec(v_a_1559_);
                    v___x_1570_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8_once), _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8);
                    crate::leanh::lean_inc_ref(v_e_x27_1552_);
                    v___x_1571_ = l_Lean_Expr_app___override(v___x_1570_, v_e_x27_1552_);
                    v___x_1572_ = crate::leanh::lean_box(0);
                    v___x_1573_ = l_Lean_Meta_trySynthInstance(
                        v___x_1571_,
                        v___x_1572_,
                        v___y_1473_,
                        v___y_1474_,
                        v___y_1475_,
                        v___y_1476_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1573_) == 0 {
                        v_a_1574_ = crate::leanh::lean_ctor_get(v___x_1573_, 0);
                        v_isSharedCheck_1620_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1573_)) as u8;
                        if v_isSharedCheck_1620_ == 0 {
                            v___x_1576_ = v___x_1573_;
                            v_isShared_1577_ = v_isSharedCheck_1620_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1574_);
                            crate::leanh::lean_dec(v___x_1573_);
                            v___x_1576_ = crate::leanh::lean_box(0);
                            v_isShared_1577_ = v_isSharedCheck_1620_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1565_);
                        crate::leanh::lean_del_object(v___x_1556_);
                        crate::leanh::lean_dec_ref(v_proof_1553_);
                        crate::leanh::lean_dec_ref(v_e_x27_1552_);
                        crate::leanh::lean_dec_ref(v_arg_1486_);
                        crate::leanh::lean_dec_ref(v_arg_1483_);
                        crate::leanh::lean_dec_ref(v_e_1467_);
                        v_a_1621_ = crate::leanh::lean_ctor_get(v___x_1573_, 0);
                        v_isSharedCheck_1628_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1573_)) as u8;
                        if v_isSharedCheck_1628_ == 0 {
                            v___x_1623_ = v___x_1573_;
                            v_isShared_1624_ = v_isSharedCheck_1628_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1621_);
                            crate::leanh::lean_dec(v___x_1573_);
                            v___x_1623_ = crate::leanh::lean_box(0);
                            v_isShared_1624_ = v_isSharedCheck_1628_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1565_);
                    crate::leanh::lean_dec_ref(v_e_x27_1552_);
                    crate::leanh::lean_dec_ref(v_arg_1486_);
                    v___x_1629_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14;
                    v___x_1630_ = l_Lean_Expr_replaceFn(v_e_1467_, v___x_1629_);
                    v___x_1631_ = l_Lean_Expr_app___override(v___x_1630_, v_proof_1553_);
                    if v_isShared_1557_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1556_, 1, v___x_1631_);
                        crate::leanh::lean_ctor_set(v___x_1556_, 0, v_arg_1483_);
                        v___x_1633_ = v___x_1556_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_1638_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_arg_1483_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 1, v___x_1631_);
                        v___x_1633_ = v_reuseFailAlloc_1638_;
                        state = 25;
                        continue;
                    }
                }
            }
            14 => {
                if crate::leanh::lean_obj_tag(v_a_1574_) == 1 {
                    crate::leanh::lean_del_object(v___x_1576_);
                    crate::leanh::lean_dec(v_a_1565_);
                    v_a_1578_ = crate::leanh::lean_ctor_get(v_a_1574_, 0);
                    crate::leanh::lean_inc(v_a_1578_);
                    crate::leanh::lean_dec_ref_known(v_a_1574_, 1);
                    v___x_1579_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1578_, v___y_1472_);
                    if crate::leanh::lean_obj_tag(v___x_1579_) == 0 {
                        v_a_1580_ = crate::leanh::lean_ctor_get(v___x_1579_, 0);
                        crate::leanh::lean_inc_n(v_a_1580_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1579_, 1);
                        v___x_1581_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_1582_ = l_Lean_Expr_getBoundedAppFn(v___x_1581_, v_e_1467_);
                        crate::leanh::lean_inc_ref(v_e_x27_1552_);
                        v___x_1583_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(v___x_1582_, v_e_x27_1552_, v_a_1580_, v_arg_1486_, v_arg_1483_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
                        if crate::leanh::lean_obj_tag(v___x_1583_) == 0 {
                            v_a_1584_ = crate::leanh::lean_ctor_get(v___x_1583_, 0);
                            v_isSharedCheck_1597_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1583_)) as u8;
                            if v_isSharedCheck_1597_ == 0 {
                                v___x_1586_ = v___x_1583_;
                                v_isShared_1587_ = v_isSharedCheck_1597_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1584_);
                                crate::leanh::lean_dec(v___x_1583_);
                                v___x_1586_ = crate::leanh::lean_box(0);
                                v_isShared_1587_ = v_isSharedCheck_1597_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1580_);
                            crate::leanh::lean_del_object(v___x_1556_);
                            crate::leanh::lean_dec_ref(v_proof_1553_);
                            crate::leanh::lean_dec_ref(v_e_x27_1552_);
                            crate::leanh::lean_dec_ref(v_e_1467_);
                            v_a_1598_ = crate::leanh::lean_ctor_get(v___x_1583_, 0);
                            v_isSharedCheck_1605_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1583_)) as u8;
                            if v_isSharedCheck_1605_ == 0 {
                                v___x_1600_ = v___x_1583_;
                                v_isShared_1601_ = v_isSharedCheck_1605_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1598_);
                                crate::leanh::lean_dec(v___x_1583_);
                                v___x_1600_ = crate::leanh::lean_box(0);
                                v_isShared_1601_ = v_isSharedCheck_1605_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1556_);
                        crate::leanh::lean_dec_ref(v_proof_1553_);
                        crate::leanh::lean_dec_ref(v_e_x27_1552_);
                        crate::leanh::lean_dec_ref(v_arg_1486_);
                        crate::leanh::lean_dec_ref(v_arg_1483_);
                        crate::leanh::lean_dec_ref(v_e_1467_);
                        v_a_1606_ = crate::leanh::lean_ctor_get(v___x_1579_, 0);
                        v_isSharedCheck_1613_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1579_)) as u8;
                        if v_isSharedCheck_1613_ == 0 {
                            v___x_1608_ = v___x_1579_;
                            v_isShared_1609_ = v_isSharedCheck_1613_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1606_);
                            crate::leanh::lean_dec(v___x_1579_);
                            v___x_1608_ = crate::leanh::lean_box(0);
                            v_isShared_1609_ = v_isSharedCheck_1613_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1574_);
                    crate::leanh::lean_del_object(v___x_1556_);
                    crate::leanh::lean_dec_ref(v_proof_1553_);
                    crate::leanh::lean_dec_ref(v_e_x27_1552_);
                    crate::leanh::lean_dec_ref(v_arg_1486_);
                    crate::leanh::lean_dec_ref(v_arg_1483_);
                    crate::leanh::lean_dec_ref(v_e_1467_);
                    v___x_1614_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    v___x_1615_ = (crate::leanh::lean_unbox(v_a_1565_) as u8);
                    crate::leanh::lean_ctor_set_uint8(v___x_1614_, 0 as u32, v___x_1615_);
                    v___x_1616_ = (crate::leanh::lean_unbox(v_a_1565_) as u8);
                    crate::leanh::lean_dec(v_a_1565_);
                    crate::leanh::lean_ctor_set_uint8(v___x_1614_, 1 as u32, v___x_1616_);
                    if v_isShared_1577_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1576_, 0, v___x_1614_);
                        v___x_1618_ = v___x_1576_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_1619_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1614_);
                        v___x_1618_ = v_reuseFailAlloc_1619_;
                        state = 22;
                        continue;
                    }
                }
            }
            15 => {
                v___x_1588_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12;
                v___x_1589_ = l_Lean_Expr_replaceFn(v_e_1467_, v___x_1588_);
                v___x_1590_ = l_Lean_mkApp3(v___x_1589_, v_e_x27_1552_, v_a_1580_, v_proof_1553_);
                if v_isShared_1557_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1556_, 1, v___x_1590_);
                    crate::leanh::lean_ctor_set(v___x_1556_, 0, v_a_1584_);
                    v___x_1592_ = v___x_1556_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1596_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___x_1590_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1596_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_1554_,
                    );
                    v___x_1592_ = v_reuseFailAlloc_1596_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1592_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1497_,
                );
                if v_isShared_1587_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1592_);
                    v___x_1594_ = v___x_1586_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
                    v___x_1594_ = v_reuseFailAlloc_1595_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1594_;
            }
            18 => {
                if v_isShared_1601_ == 0 {
                    v___x_1603_ = v___x_1600_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1604_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
                    v___x_1603_ = v_reuseFailAlloc_1604_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1603_;
            }
            20 => {
                if v_isShared_1609_ == 0 {
                    v___x_1611_ = v___x_1608_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
                    v___x_1611_ = v_reuseFailAlloc_1612_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1611_;
            }
            22 => {
                return v___x_1618_;
            }
            23 => {
                if v_isShared_1624_ == 0 {
                    v___x_1626_ = v___x_1623_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
                    v___x_1626_ = v_reuseFailAlloc_1627_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1626_;
            }
            25 => {
                v___x_1634_ = (crate::leanh::lean_unbox(v_a_1559_) as u8);
                crate::leanh::lean_dec(v_a_1559_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1633_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1634_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1633_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_1554_,
                );
                if v_isShared_1568_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1567_, 0, v___x_1633_);
                    v___x_1636_ = v___x_1567_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1637_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1633_);
                    v___x_1636_ = v_reuseFailAlloc_1637_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1636_;
            }
            27 => {
                if v_isShared_1643_ == 0 {
                    v___x_1645_ = v___x_1642_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1646_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
                    v___x_1645_ = v_reuseFailAlloc_1646_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1645_;
            }
            29 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1652_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1466_,
                );
                if v_isShared_1562_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1652_);
                    v___x_1654_ = v___x_1561_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
                    v___x_1654_ = v_reuseFailAlloc_1655_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_1654_;
            }
            31 => {
                if v_isShared_1661_ == 0 {
                    v___x_1663_ = v___x_1660_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1664_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
                    v___x_1663_ = v_reuseFailAlloc_1664_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_1663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___boxed(
    mut v___x_1667_: *mut crate::leanh::LeanObject,
    mut v_e_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_21630__boxed_1679_: u8 = 0;
    let mut v_res_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_21630__boxed_1679_ = (crate::leanh::lean_unbox(v___x_1667_) as u8);
    v_res_1680_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(
        v___x_21630__boxed_1679_,
        v_e_1668_,
        v___y_1669_,
        v___y_1670_,
        v___y_1671_,
        v___y_1672_,
        v___y_1673_,
        v___y_1674_,
        v___y_1675_,
        v___y_1676_,
        v___y_1677_,
    );
    crate::leanh::lean_dec(v___y_1677_);
    crate::leanh::lean_dec_ref(v___y_1676_);
    crate::leanh::lean_dec(v___y_1675_);
    crate::leanh::lean_dec_ref(v___y_1674_);
    crate::leanh::lean_dec(v___y_1673_);
    crate::leanh::lean_dec_ref(v___y_1672_);
    crate::leanh::lean_dec(v___y_1671_);
    crate::leanh::lean_dec_ref(v___y_1670_);
    crate::leanh::lean_dec(v___y_1669_);
    return v_res_1680_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(
    mut v_e_1681_: *mut crate::leanh::LeanObject,
    mut v_a_1682_: *mut crate::leanh::LeanObject,
    mut v_a_1683_: *mut crate::leanh::LeanObject,
    mut v_a_1684_: *mut crate::leanh::LeanObject,
    mut v_a_1685_: *mut crate::leanh::LeanObject,
    mut v_a_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numArgs_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: u8 = 0;
    v_numArgs_1692_ = l_Lean_Expr_getAppNumArgs(v_e_1681_);
    v___x_1693_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_1694_ = lean_nat_dec_lt(v_numArgs_1692_, v___x_1693_);
    if v___x_1694_ == 0 {
        let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1695_ = crate::leanh::lean_box((v___x_1694_) as usize);
        v___f_1696_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___boxed as *mut core::ffi::c_void, 12, 1);
        crate::leanh::lean_closure_set(v___f_1696_, 0, v___x_1695_);
        v___x_1697_ = lean_nat_sub(v_numArgs_1692_, v___x_1693_);
        crate::leanh::lean_dec(v_numArgs_1692_);
        v___x_1698_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(
            v_e_1681_,
            v___x_1697_,
            v___f_1696_,
            v_a_1682_,
            v_a_1683_,
            v_a_1684_,
            v_a_1685_,
            v_a_1686_,
            v_a_1687_,
            v_a_1688_,
            v_a_1689_,
            v_a_1690_,
        );
        crate::leanh::lean_dec(v___x_1697_);
        return v___x_1698_;
    } else {
        let mut v___x_1699_: u8 = 0;
        let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_numArgs_1692_);
        crate::leanh::lean_dec_ref(v_e_1681_);
        v___x_1699_ = 0;
        v___x_1700_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
        crate::leanh::lean_ctor_set_uint8(v___x_1700_, 0 as u32, v___x_1694_);
        crate::leanh::lean_ctor_set_uint8(v___x_1700_, 1 as u32, v___x_1699_);
        v___x_1701_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1701_, 0, v___x_1700_);
        return v___x_1701_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___boxed(
    mut v_e_1702_: *mut crate::leanh::LeanObject,
    mut v_a_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
    mut v_a_1706_: *mut crate::leanh::LeanObject,
    mut v_a_1707_: *mut crate::leanh::LeanObject,
    mut v_a_1708_: *mut crate::leanh::LeanObject,
    mut v_a_1709_: *mut crate::leanh::LeanObject,
    mut v_a_1710_: *mut crate::leanh::LeanObject,
    mut v_a_1711_: *mut crate::leanh::LeanObject,
    mut v_a_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(
        v_e_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_,
        v_a_1710_, v_a_1711_,
    );
    crate::leanh::lean_dec(v_a_1711_);
    crate::leanh::lean_dec_ref(v_a_1710_);
    crate::leanh::lean_dec(v_a_1709_);
    crate::leanh::lean_dec_ref(v_a_1708_);
    crate::leanh::lean_dec(v_a_1707_);
    crate::leanh::lean_dec_ref(v_a_1706_);
    crate::leanh::lean_dec(v_a_1705_);
    crate::leanh::lean_dec_ref(v_a_1704_);
    crate::leanh::lean_dec(v_a_1703_);
    return v_res_1713_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(
    mut v_f_1714_: *mut crate::leanh::LeanObject,
    mut v_a_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
    mut v___y_1722_: *mut crate::leanh::LeanObject,
    mut v___y_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1726_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_f_1714_, v_a_1715_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
    return v___x_1726_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___boxed(
    mut v_f_1727_: *mut crate::leanh::LeanObject,
    mut v_a_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
    mut v___y_1731_: *mut crate::leanh::LeanObject,
    mut v___y_1732_: *mut crate::leanh::LeanObject,
    mut v___y_1733_: *mut crate::leanh::LeanObject,
    mut v___y_1734_: *mut crate::leanh::LeanObject,
    mut v___y_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
    mut v___y_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1739_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(v_f_1727_, v_a_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
    crate::leanh::lean_dec(v___y_1737_);
    crate::leanh::lean_dec_ref(v___y_1736_);
    crate::leanh::lean_dec(v___y_1735_);
    crate::leanh::lean_dec_ref(v___y_1734_);
    crate::leanh::lean_dec(v___y_1733_);
    crate::leanh::lean_dec_ref(v___y_1732_);
    crate::leanh::lean_dec(v___y_1731_);
    crate::leanh::lean_dec_ref(v___y_1730_);
    crate::leanh::lean_dec(v___y_1729_);
    return v_res_1739_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = crate::leanh::lean_box(0);
    v___x_1747_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3;
    v___x_1748_ = l_Lean_mkConst(v___x_1747_, v___x_1746_);
    return v___x_1748_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1749_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4_once), _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4);
    v___x_1750_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1751_ = lean_mk_empty_array_with_capacity(v___x_1750_);
    v___x_1752_ = lean_array_push(v___x_1751_, v___x_1749_);
    return v___x_1752_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1761_ = crate::leanh::lean_box(0);
    v___x_1762_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10;
    v___x_1763_ = l_Lean_mkConst(v___x_1762_, v___x_1761_);
    return v___x_1763_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1764_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11_once), _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11);
    v___x_1765_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1766_ = lean_mk_empty_array_with_capacity(v___x_1765_);
    v___x_1767_ = lean_array_push(v___x_1766_, v___x_1764_);
    return v___x_1767_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1779_ = crate::leanh::lean_box(0);
    v___x_1780_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19;
    v___x_1781_ = l_Lean_mkConst(v___x_1780_, v___x_1779_);
    return v___x_1781_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1782_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1783_ = l_Lean_mkBVar(v___x_1782_);
    return v___x_1783_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1788_ = crate::leanh::lean_box(0);
    v___x_1789_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23;
    v___x_1790_ = l_Lean_mkConst(v___x_1789_, v___x_1788_);
    return v___x_1790_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(
    mut v___x_1802_: u8,
    mut v_e_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: u8 = 0;
    let mut v_arg_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v_arg_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u8 = 0;
    let mut v_arg_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v_arg_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: u8 = 0;
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_1836_: u8 = 0;
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: u8 = 0;
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1844_: u8 = 0;
    let mut v___x_1845_: u8 = 0;
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v___x_1852_: u8 = 0;
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1868_: u8 = 0;
    let mut v_a_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1872_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_isSharedCheck_1877_: u8 = 0;
    let mut v_a_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1901_: u8 = 0;
    let mut v_a_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1909_: u8 = 0;
    let mut v_a_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut v_e_x27_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_1920_: u8 = 0;
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1923_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: u8 = 0;
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v_a_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: u8 = 0;
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1973_: u8 = 0;
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_a_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1987_: u8 = 0;
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_a_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut v_a_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut v_a_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut v_a_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2023_: u8 = 0;
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2030_: u8 = 0;
    let mut v_a_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2052_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2063_: u8 = 0;
    let mut v_a_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2067_: u8 = 0;
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2071_: u8 = 0;
    let mut v_a_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2079_: u8 = 0;
    let mut v_a_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2083_: u8 = 0;
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2087_: u8 = 0;
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2099_: u8 = 0;
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2109_: u8 = 0;
    let mut v_a_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2117_: u8 = 0;
    let mut v_a_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2121_: u8 = 0;
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut v_a_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2129_: u8 = 0;
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2133_: u8 = 0;
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1803_);
                v___x_1817_ = l_Lean_Expr_cleanupAnnotations(v_e_1803_);
                v___x_1818_ = l_Lean_Expr_isApp(v___x_1817_);
                if v___x_1818_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1817_);
                    crate::leanh::lean_dec_ref(v_e_1803_);
                    state = 1;
                    continue;
                } else {
                    v_arg_1819_ = crate::leanh::lean_ctor_get(v___x_1817_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1819_);
                    v___x_1820_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1817_);
                    v___x_1821_ = l_Lean_Expr_isApp(v___x_1820_);
                    if v___x_1821_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1820_);
                        crate::leanh::lean_dec_ref(v_arg_1819_);
                        crate::leanh::lean_dec_ref(v_e_1803_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_1822_ = crate::leanh::lean_ctor_get(v___x_1820_, 1);
                        crate::leanh::lean_inc_ref(v_arg_1822_);
                        v___x_1823_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1820_);
                        v___x_1824_ = l_Lean_Expr_isApp(v___x_1823_);
                        if v___x_1824_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1823_);
                            crate::leanh::lean_dec_ref(v_arg_1822_);
                            crate::leanh::lean_dec_ref(v_arg_1819_);
                            crate::leanh::lean_dec_ref(v_e_1803_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1825_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1823_);
                            v___x_1826_ = l_Lean_Expr_isApp(v___x_1825_);
                            if v___x_1826_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_1825_);
                                crate::leanh::lean_dec_ref(v_arg_1822_);
                                crate::leanh::lean_dec_ref(v_arg_1819_);
                                crate::leanh::lean_dec_ref(v_e_1803_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_1827_ = crate::leanh::lean_ctor_get(v___x_1825_, 1);
                                crate::leanh::lean_inc_ref(v_arg_1827_);
                                v___x_1828_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1825_);
                                v___x_1829_ = l_Lean_Expr_isApp(v___x_1828_);
                                if v___x_1829_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_1828_);
                                    crate::leanh::lean_dec_ref(v_arg_1827_);
                                    crate::leanh::lean_dec_ref(v_arg_1822_);
                                    crate::leanh::lean_dec_ref(v_arg_1819_);
                                    crate::leanh::lean_dec_ref(v_e_1803_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_1830_ = crate::leanh::lean_ctor_get(v___x_1828_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_1830_);
                                    v___x_1831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1828_);
                                    v___x_1832_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1;
                                    v___x_1833_ = l_Lean_Expr_isConstOf(v___x_1831_, v___x_1832_);
                                    if v___x_1833_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_1831_);
                                        crate::leanh::lean_dec_ref(v_arg_1830_);
                                        crate::leanh::lean_dec_ref(v_arg_1827_);
                                        crate::leanh::lean_dec_ref(v_arg_1822_);
                                        crate::leanh::lean_dec_ref(v_arg_1819_);
                                        crate::leanh::lean_dec_ref(v_e_1803_);
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v___y_1812_);
                                        crate::leanh::lean_inc_ref(v___y_1811_);
                                        crate::leanh::lean_inc(v___y_1810_);
                                        crate::leanh::lean_inc_ref(v___y_1809_);
                                        crate::leanh::lean_inc(v___y_1808_);
                                        crate::leanh::lean_inc_ref(v___y_1807_);
                                        crate::leanh::lean_inc(v___y_1806_);
                                        crate::leanh::lean_inc_ref(v___y_1805_);
                                        crate::leanh::lean_inc(v___y_1804_);
                                        crate::leanh::lean_inc_ref(v_arg_1827_);
                                        v___x_1834_ = lean_sym_simp(
                                            v_arg_1827_,
                                            v___y_1804_,
                                            v___y_1805_,
                                            v___y_1806_,
                                            v___y_1807_,
                                            v___y_1808_,
                                            v___y_1809_,
                                            v___y_1810_,
                                            v___y_1811_,
                                            v___y_1812_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_1834_) == 0 {
                                            v_a_1835_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                                            crate::leanh::lean_inc(v_a_1835_);
                                            crate::leanh::lean_dec_ref_known(v___x_1834_, 1);
                                            if crate::leanh::lean_obj_tag(v_a_1835_) == 0 {
                                                crate::leanh::lean_dec_ref(v_e_1803_);
                                                v_contextDependent_1836_ =
                                                    crate::leanh::lean_ctor_get_uint8(
                                                        v_a_1835_, 1 as u32,
                                                    );
                                                crate::leanh::lean_dec_ref_known(v_a_1835_, 0);
                                                v___x_1837_ = l_Lean_Meta_Sym_isTrueExpr___redArg(
                                                    v_arg_1827_,
                                                    v___y_1807_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_1837_) == 0 {
                                                    v_a_1838_ =
                                                        crate::leanh::lean_ctor_get(v___x_1837_, 0);
                                                    crate::leanh::lean_inc(v_a_1838_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_1837_,
                                                        1,
                                                    );
                                                    v___x_1839_ =
                                                        (crate::leanh::lean_unbox(v_a_1838_) as u8);
                                                    if v___x_1839_ == 0 {
                                                        v___x_1840_ =
                                                            l_Lean_Meta_Sym_isFalseExpr___redArg(
                                                                v_arg_1827_,
                                                                v___y_1807_,
                                                            );
                                                        crate::leanh::lean_dec_ref(v_arg_1827_);
                                                        if crate::leanh::lean_obj_tag(v___x_1840_)
                                                            == 0
                                                        {
                                                            v_a_1841_ = crate::leanh::lean_ctor_get(
                                                                v___x_1840_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_1877_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_1840_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_1877_ == 0 {
                                                                v___x_1843_ = v___x_1840_;
                                                                v_isShared_1844_ =
                                                                    v_isSharedCheck_1877_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_1841_);
                                                                crate::leanh::lean_dec(v___x_1840_);
                                                                v___x_1843_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_1844_ =
                                                                    v_isSharedCheck_1877_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_a_1838_);
                                                            crate::leanh::lean_dec_ref(v___x_1831_);
                                                            crate::leanh::lean_dec_ref(v_arg_1830_);
                                                            crate::leanh::lean_dec_ref(v_arg_1822_);
                                                            crate::leanh::lean_dec_ref(v_arg_1819_);
                                                            v_a_1878_ = crate::leanh::lean_ctor_get(
                                                                v___x_1840_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_1885_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_1840_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_1885_ == 0 {
                                                                v___x_1880_ = v___x_1840_;
                                                                v_isShared_1881_ =
                                                                    v_isSharedCheck_1885_;
                                                                state = 8;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_1878_);
                                                                crate::leanh::lean_dec(v___x_1840_);
                                                                v___x_1880_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_1881_ =
                                                                    v_isSharedCheck_1885_;
                                                                state = 8;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_1838_);
                                                        crate::leanh::lean_dec_ref(v_arg_1827_);
                                                        v___x_1886_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12_once), _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12);
                                                        crate::leanh::lean_inc_ref(v_arg_1822_);
                                                        v___x_1887_ = l_Lean_Expr_betaRev(
                                                            v_arg_1822_,
                                                            v___x_1886_,
                                                            v___x_1802_,
                                                            v___x_1802_,
                                                        );
                                                        v___x_1888_ =
                                                            l_Lean_Meta_Sym_shareCommonInc___redArg(
                                                                v___x_1887_,
                                                                v___y_1808_,
                                                            );
                                                        if crate::leanh::lean_obj_tag(v___x_1888_)
                                                            == 0
                                                        {
                                                            v_a_1889_ = crate::leanh::lean_ctor_get(
                                                                v___x_1888_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_1901_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_1888_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_1901_ == 0 {
                                                                v___x_1891_ = v___x_1888_;
                                                                v_isShared_1892_ =
                                                                    v_isSharedCheck_1901_;
                                                                state = 10;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_1889_);
                                                                crate::leanh::lean_dec(v___x_1888_);
                                                                v___x_1891_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_1892_ =
                                                                    v_isSharedCheck_1901_;
                                                                state = 10;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_1831_);
                                                            crate::leanh::lean_dec_ref(v_arg_1830_);
                                                            crate::leanh::lean_dec_ref(v_arg_1822_);
                                                            crate::leanh::lean_dec_ref(v_arg_1819_);
                                                            v_a_1902_ = crate::leanh::lean_ctor_get(
                                                                v___x_1888_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_1909_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_1888_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_1909_ == 0 {
                                                                v___x_1904_ = v___x_1888_;
                                                                v_isShared_1905_ =
                                                                    v_isSharedCheck_1909_;
                                                                state = 12;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_1902_);
                                                                crate::leanh::lean_dec(v___x_1888_);
                                                                v___x_1904_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_1905_ =
                                                                    v_isSharedCheck_1909_;
                                                                state = 12;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_1831_);
                                                    crate::leanh::lean_dec_ref(v_arg_1830_);
                                                    crate::leanh::lean_dec_ref(v_arg_1827_);
                                                    crate::leanh::lean_dec_ref(v_arg_1822_);
                                                    crate::leanh::lean_dec_ref(v_arg_1819_);
                                                    v_a_1910_ =
                                                        crate::leanh::lean_ctor_get(v___x_1837_, 0);
                                                    v_isSharedCheck_1917_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_1837_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_1917_ == 0 {
                                                        v___x_1912_ = v___x_1837_;
                                                        v_isShared_1913_ = v_isSharedCheck_1917_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_1910_);
                                                        crate::leanh::lean_dec(v___x_1837_);
                                                        v___x_1912_ = crate::leanh::lean_box(0);
                                                        v_isShared_1913_ = v_isSharedCheck_1917_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_1831_);
                                                crate::leanh::lean_dec_ref(v_arg_1830_);
                                                v_e_x27_1918_ =
                                                    crate::leanh::lean_ctor_get(v_a_1835_, 0);
                                                v_proof_1919_ =
                                                    crate::leanh::lean_ctor_get(v_a_1835_, 1);
                                                v_contextDependent_1920_ =
                                                    crate::leanh::lean_ctor_get_uint8(
                                                        v_a_1835_,
                                                        (core::mem::size_of::<
                                                            *mut crate::leanh::LeanObject,
                                                        >(
                                                        ) * 2
                                                            + 1)
                                                            as u32,
                                                    );
                                                v_isSharedCheck_2134_ =
                                                    (!crate::leanh::lean_is_exclusive(v_a_1835_))
                                                        as u8;
                                                if v_isSharedCheck_2134_ == 0 {
                                                    v___x_1922_ = v_a_1835_;
                                                    v_isShared_1923_ = v_isSharedCheck_2134_;
                                                    state = 16;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_proof_1919_);
                                                    crate::leanh::lean_inc(v_e_x27_1918_);
                                                    crate::leanh::lean_dec(v_a_1835_);
                                                    v___x_1922_ = crate::leanh::lean_box(0);
                                                    v_isShared_1923_ = v_isSharedCheck_2134_;
                                                    state = 16;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_1831_);
                                            crate::leanh::lean_dec_ref(v_arg_1830_);
                                            crate::leanh::lean_dec_ref(v_arg_1827_);
                                            crate::leanh::lean_dec_ref(v_arg_1822_);
                                            crate::leanh::lean_dec_ref(v_arg_1819_);
                                            crate::leanh::lean_dec_ref(v_e_1803_);
                                            return v___x_1834_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1815_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_1815_, 0 as u32, v___x_1802_);
                crate::leanh::lean_ctor_set_uint8(v___x_1815_, 1 as u32, v___x_1802_);
                v___x_1816_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1816_, 0, v___x_1815_);
                return v___x_1816_;
            }
            2 => {
                v___x_1845_ = (crate::leanh::lean_unbox(v_a_1841_) as u8);
                crate::leanh::lean_dec(v_a_1841_);
                if v___x_1845_ == 0 {
                    crate::leanh::lean_dec(v_a_1838_);
                    crate::leanh::lean_dec_ref(v___x_1831_);
                    crate::leanh::lean_dec_ref(v_arg_1830_);
                    crate::leanh::lean_dec_ref(v_arg_1822_);
                    crate::leanh::lean_dec_ref(v_arg_1819_);
                    v___x_1846_ =
                        l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1833_, v_contextDependent_1836_);
                    if v_isShared_1844_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1843_, 0, v___x_1846_);
                        v___x_1848_ = v___x_1843_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1849_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
                        v___x_1848_ = v_reuseFailAlloc_1849_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1843_);
                    v___x_1850_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5_once), _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5);
                    v___x_1851_ = (crate::leanh::lean_unbox(v_a_1838_) as u8);
                    v___x_1852_ = (crate::leanh::lean_unbox(v_a_1838_) as u8);
                    crate::leanh::lean_inc_ref(v_arg_1819_);
                    v___x_1853_ =
                        l_Lean_Expr_betaRev(v_arg_1819_, v___x_1850_, v___x_1851_, v___x_1852_);
                    v___x_1854_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1853_, v___y_1808_);
                    if crate::leanh::lean_obj_tag(v___x_1854_) == 0 {
                        v_a_1855_ = crate::leanh::lean_ctor_get(v___x_1854_, 0);
                        v_isSharedCheck_1868_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1854_)) as u8;
                        if v_isSharedCheck_1868_ == 0 {
                            v___x_1857_ = v___x_1854_;
                            v_isShared_1858_ = v_isSharedCheck_1868_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1855_);
                            crate::leanh::lean_dec(v___x_1854_);
                            v___x_1857_ = crate::leanh::lean_box(0);
                            v_isShared_1858_ = v_isSharedCheck_1868_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1838_);
                        crate::leanh::lean_dec_ref(v___x_1831_);
                        crate::leanh::lean_dec_ref(v_arg_1830_);
                        crate::leanh::lean_dec_ref(v_arg_1822_);
                        crate::leanh::lean_dec_ref(v_arg_1819_);
                        v_a_1869_ = crate::leanh::lean_ctor_get(v___x_1854_, 0);
                        v_isSharedCheck_1876_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1854_)) as u8;
                        if v_isSharedCheck_1876_ == 0 {
                            v___x_1871_ = v___x_1854_;
                            v_isShared_1872_ = v_isSharedCheck_1876_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1869_);
                            crate::leanh::lean_dec(v___x_1854_);
                            v___x_1871_ = crate::leanh::lean_box(0);
                            v_isShared_1872_ = v_isSharedCheck_1876_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_1848_;
            }
            4 => {
                v___x_1859_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7;
                v___x_1860_ = l_Lean_Expr_constLevels_x21(v___x_1831_);
                crate::leanh::lean_dec_ref(v___x_1831_);
                v___x_1861_ = l_Lean_mkConst(v___x_1859_, v___x_1860_);
                v___x_1862_ = l_Lean_mkApp3(v___x_1861_, v_arg_1830_, v_arg_1822_, v_arg_1819_);
                v___x_1863_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1863_, 0, v_a_1855_);
                crate::leanh::lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                v___x_1864_ = (crate::leanh::lean_unbox(v_a_1838_) as u8);
                crate::leanh::lean_dec(v_a_1838_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1863_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1864_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1863_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_1836_,
                );
                if v_isShared_1858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1857_, 0, v___x_1863_);
                    v___x_1866_ = v___x_1857_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1867_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1863_);
                    v___x_1866_ = v_reuseFailAlloc_1867_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1866_;
            }
            6 => {
                if v_isShared_1872_ == 0 {
                    v___x_1874_ = v___x_1871_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
                    v___x_1874_ = v_reuseFailAlloc_1875_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1874_;
            }
            8 => {
                if v_isShared_1881_ == 0 {
                    v___x_1883_ = v___x_1880_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
                    v___x_1883_ = v_reuseFailAlloc_1884_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1883_;
            }
            10 => {
                v___x_1893_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14;
                v___x_1894_ = l_Lean_Expr_constLevels_x21(v___x_1831_);
                crate::leanh::lean_dec_ref(v___x_1831_);
                v___x_1895_ = l_Lean_mkConst(v___x_1893_, v___x_1894_);
                v___x_1896_ = l_Lean_mkApp3(v___x_1895_, v_arg_1830_, v_arg_1822_, v_arg_1819_);
                v___x_1897_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_1897_, 0, v_a_1889_);
                crate::leanh::lean_ctor_set(v___x_1897_, 1, v___x_1896_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1897_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1802_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1897_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_1836_,
                );
                if v_isShared_1892_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1891_, 0, v___x_1897_);
                    v___x_1899_ = v___x_1891_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1900_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
                    v___x_1899_ = v_reuseFailAlloc_1900_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1899_;
            }
            12 => {
                if v_isShared_1905_ == 0 {
                    v___x_1907_ = v___x_1904_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1908_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
                    v___x_1907_ = v_reuseFailAlloc_1908_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1907_;
            }
            14 => {
                if v_isShared_1913_ == 0 {
                    v___x_1915_ = v___x_1912_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1916_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
                    v___x_1915_ = v_reuseFailAlloc_1916_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1915_;
            }
            16 => {
                v___x_1924_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1918_, v___y_1807_);
                if crate::leanh::lean_obj_tag(v___x_1924_) == 0 {
                    v_a_1925_ = crate::leanh::lean_ctor_get(v___x_1924_, 0);
                    crate::leanh::lean_inc(v_a_1925_);
                    crate::leanh::lean_dec_ref_known(v___x_1924_, 1);
                    v___x_1926_ = (crate::leanh::lean_unbox(v_a_1925_) as u8);
                    if v___x_1926_ == 0 {
                        v___x_1927_ =
                            l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_1918_, v___y_1807_);
                        if crate::leanh::lean_obj_tag(v___x_1927_) == 0 {
                            v_a_1928_ = crate::leanh::lean_ctor_get(v___x_1927_, 0);
                            crate::leanh::lean_inc(v_a_1928_);
                            crate::leanh::lean_dec_ref_known(v___x_1927_, 1);
                            v___x_1929_ = (crate::leanh::lean_unbox(v_a_1928_) as u8);
                            if v___x_1929_ == 0 {
                                crate::leanh::lean_dec(v_a_1925_);
                                v___x_1930_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8_once), _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8);
                                crate::leanh::lean_inc_ref(v_e_x27_1918_);
                                v___x_1931_ =
                                    l_Lean_Expr_app___override(v___x_1930_, v_e_x27_1918_);
                                v___x_1932_ = crate::leanh::lean_box(0);
                                v___x_1933_ = l_Lean_Meta_trySynthInstance(
                                    v___x_1931_,
                                    v___x_1932_,
                                    v___y_1809_,
                                    v___y_1810_,
                                    v___y_1811_,
                                    v___y_1812_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1933_) == 0 {
                                    v_a_1934_ = crate::leanh::lean_ctor_get(v___x_1933_, 0);
                                    v_isSharedCheck_2030_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1933_)) as u8;
                                    if v_isSharedCheck_2030_ == 0 {
                                        v___x_1936_ = v___x_1933_;
                                        v_isShared_1937_ = v_isSharedCheck_2030_;
                                        state = 17;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1934_);
                                        crate::leanh::lean_dec(v___x_1933_);
                                        v___x_1936_ = crate::leanh::lean_box(0);
                                        v_isShared_1937_ = v_isSharedCheck_2030_;
                                        state = 17;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1928_);
                                    crate::leanh::lean_del_object(v___x_1922_);
                                    crate::leanh::lean_dec_ref(v_proof_1919_);
                                    crate::leanh::lean_dec_ref(v_e_x27_1918_);
                                    crate::leanh::lean_dec_ref(v_arg_1827_);
                                    crate::leanh::lean_dec_ref(v_arg_1822_);
                                    crate::leanh::lean_dec_ref(v_arg_1819_);
                                    crate::leanh::lean_dec_ref(v_e_1803_);
                                    v_a_2031_ = crate::leanh::lean_ctor_get(v___x_1933_, 0);
                                    v_isSharedCheck_2038_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1933_)) as u8;
                                    if v_isSharedCheck_2038_ == 0 {
                                        v___x_2033_ = v___x_1933_;
                                        v_isShared_2034_ = v_isSharedCheck_2038_;
                                        state = 32;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2031_);
                                        crate::leanh::lean_dec(v___x_1933_);
                                        v___x_2033_ = crate::leanh::lean_box(0);
                                        v_isShared_2034_ = v_isSharedCheck_2038_;
                                        state = 32;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1928_);
                                crate::leanh::lean_dec_ref(v_e_x27_1918_);
                                crate::leanh::lean_dec_ref(v_arg_1822_);
                                crate::leanh::lean_inc_ref(v_proof_1919_);
                                v___x_2039_ =
                                    l_Lean_Meta_mkOfEqFalseCore(v_arg_1827_, v_proof_1919_);
                                v___x_2040_ =
                                    l_Lean_Meta_Sym_shareCommon___redArg(v___x_2039_, v___y_1808_);
                                if crate::leanh::lean_obj_tag(v___x_2040_) == 0 {
                                    v_a_2041_ = crate::leanh::lean_ctor_get(v___x_2040_, 0);
                                    crate::leanh::lean_inc(v_a_2041_);
                                    crate::leanh::lean_dec_ref_known(v___x_2040_, 1);
                                    v___x_2042_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_2043_ = lean_mk_empty_array_with_capacity(v___x_2042_);
                                    v___x_2044_ = lean_array_push(v___x_2043_, v_a_2041_);
                                    v___x_2045_ = (crate::leanh::lean_unbox(v_a_1925_) as u8);
                                    v___x_2046_ = (crate::leanh::lean_unbox(v_a_1925_) as u8);
                                    v___x_2047_ = l_Lean_Expr_betaRev(
                                        v_arg_1819_,
                                        v___x_2044_,
                                        v___x_2045_,
                                        v___x_2046_,
                                    );
                                    crate::leanh::lean_dec_ref(v___x_2044_);
                                    v___x_2048_ = l_Lean_Meta_Sym_shareCommonInc___redArg(
                                        v___x_2047_,
                                        v___y_1808_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2048_) == 0 {
                                        v_a_2049_ = crate::leanh::lean_ctor_get(v___x_2048_, 0);
                                        v_isSharedCheck_2063_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2048_)) as u8;
                                        if v_isSharedCheck_2063_ == 0 {
                                            v___x_2051_ = v___x_2048_;
                                            v_isShared_2052_ = v_isSharedCheck_2063_;
                                            state = 34;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2049_);
                                            crate::leanh::lean_dec(v___x_2048_);
                                            v___x_2051_ = crate::leanh::lean_box(0);
                                            v_isShared_2052_ = v_isSharedCheck_2063_;
                                            state = 34;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1925_);
                                        crate::leanh::lean_del_object(v___x_1922_);
                                        crate::leanh::lean_dec_ref(v_proof_1919_);
                                        crate::leanh::lean_dec_ref(v_e_1803_);
                                        v_a_2064_ = crate::leanh::lean_ctor_get(v___x_2048_, 0);
                                        v_isSharedCheck_2071_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2048_)) as u8;
                                        if v_isSharedCheck_2071_ == 0 {
                                            v___x_2066_ = v___x_2048_;
                                            v_isShared_2067_ = v_isSharedCheck_2071_;
                                            state = 37;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2064_);
                                            crate::leanh::lean_dec(v___x_2048_);
                                            v___x_2066_ = crate::leanh::lean_box(0);
                                            v_isShared_2067_ = v_isSharedCheck_2071_;
                                            state = 37;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1925_);
                                    crate::leanh::lean_del_object(v___x_1922_);
                                    crate::leanh::lean_dec_ref(v_proof_1919_);
                                    crate::leanh::lean_dec_ref(v_arg_1819_);
                                    crate::leanh::lean_dec_ref(v_e_1803_);
                                    v_a_2072_ = crate::leanh::lean_ctor_get(v___x_2040_, 0);
                                    v_isSharedCheck_2079_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2040_)) as u8;
                                    if v_isSharedCheck_2079_ == 0 {
                                        v___x_2074_ = v___x_2040_;
                                        v_isShared_2075_ = v_isSharedCheck_2079_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2072_);
                                        crate::leanh::lean_dec(v___x_2040_);
                                        v___x_2074_ = crate::leanh::lean_box(0);
                                        v_isShared_2075_ = v_isSharedCheck_2079_;
                                        state = 39;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1925_);
                            crate::leanh::lean_del_object(v___x_1922_);
                            crate::leanh::lean_dec_ref(v_proof_1919_);
                            crate::leanh::lean_dec_ref(v_e_x27_1918_);
                            crate::leanh::lean_dec_ref(v_arg_1827_);
                            crate::leanh::lean_dec_ref(v_arg_1822_);
                            crate::leanh::lean_dec_ref(v_arg_1819_);
                            crate::leanh::lean_dec_ref(v_e_1803_);
                            v_a_2080_ = crate::leanh::lean_ctor_get(v___x_1927_, 0);
                            v_isSharedCheck_2087_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1927_)) as u8;
                            if v_isSharedCheck_2087_ == 0 {
                                v___x_2082_ = v___x_1927_;
                                v_isShared_2083_ = v_isSharedCheck_2087_;
                                state = 41;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2080_);
                                crate::leanh::lean_dec(v___x_1927_);
                                v___x_2082_ = crate::leanh::lean_box(0);
                                v_isShared_2083_ = v_isSharedCheck_2087_;
                                state = 41;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1925_);
                        crate::leanh::lean_dec_ref(v_e_x27_1918_);
                        crate::leanh::lean_dec_ref(v_arg_1819_);
                        crate::leanh::lean_inc_ref(v_proof_1919_);
                        v___x_2088_ = l_Lean_Meta_mkOfEqTrueCore(v_arg_1827_, v_proof_1919_);
                        v___x_2089_ =
                            l_Lean_Meta_Sym_shareCommon___redArg(v___x_2088_, v___y_1808_);
                        if crate::leanh::lean_obj_tag(v___x_2089_) == 0 {
                            v_a_2090_ = crate::leanh::lean_ctor_get(v___x_2089_, 0);
                            crate::leanh::lean_inc(v_a_2090_);
                            crate::leanh::lean_dec_ref_known(v___x_2089_, 1);
                            v___x_2091_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2092_ = lean_mk_empty_array_with_capacity(v___x_2091_);
                            v___x_2093_ = lean_array_push(v___x_2092_, v_a_2090_);
                            v___x_2094_ = l_Lean_Expr_betaRev(
                                v_arg_1822_,
                                v___x_2093_,
                                v___x_1802_,
                                v___x_1802_,
                            );
                            crate::leanh::lean_dec_ref(v___x_2093_);
                            v___x_2095_ =
                                l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_2094_, v___y_1808_);
                            if crate::leanh::lean_obj_tag(v___x_2095_) == 0 {
                                v_a_2096_ = crate::leanh::lean_ctor_get(v___x_2095_, 0);
                                v_isSharedCheck_2109_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2095_)) as u8;
                                if v_isSharedCheck_2109_ == 0 {
                                    v___x_2098_ = v___x_2095_;
                                    v_isShared_2099_ = v_isSharedCheck_2109_;
                                    state = 43;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2096_);
                                    crate::leanh::lean_dec(v___x_2095_);
                                    v___x_2098_ = crate::leanh::lean_box(0);
                                    v_isShared_2099_ = v_isSharedCheck_2109_;
                                    state = 43;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_1922_);
                                crate::leanh::lean_dec_ref(v_proof_1919_);
                                crate::leanh::lean_dec_ref(v_e_1803_);
                                v_a_2110_ = crate::leanh::lean_ctor_get(v___x_2095_, 0);
                                v_isSharedCheck_2117_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2095_)) as u8;
                                if v_isSharedCheck_2117_ == 0 {
                                    v___x_2112_ = v___x_2095_;
                                    v_isShared_2113_ = v_isSharedCheck_2117_;
                                    state = 46;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2110_);
                                    crate::leanh::lean_dec(v___x_2095_);
                                    v___x_2112_ = crate::leanh::lean_box(0);
                                    v_isShared_2113_ = v_isSharedCheck_2117_;
                                    state = 46;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1922_);
                            crate::leanh::lean_dec_ref(v_proof_1919_);
                            crate::leanh::lean_dec_ref(v_arg_1822_);
                            crate::leanh::lean_dec_ref(v_e_1803_);
                            v_a_2118_ = crate::leanh::lean_ctor_get(v___x_2089_, 0);
                            v_isSharedCheck_2125_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2089_)) as u8;
                            if v_isSharedCheck_2125_ == 0 {
                                v___x_2120_ = v___x_2089_;
                                v_isShared_2121_ = v_isSharedCheck_2125_;
                                state = 48;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2118_);
                                crate::leanh::lean_dec(v___x_2089_);
                                v___x_2120_ = crate::leanh::lean_box(0);
                                v_isShared_2121_ = v_isSharedCheck_2125_;
                                state = 48;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1922_);
                    crate::leanh::lean_dec_ref(v_proof_1919_);
                    crate::leanh::lean_dec_ref(v_e_x27_1918_);
                    crate::leanh::lean_dec_ref(v_arg_1827_);
                    crate::leanh::lean_dec_ref(v_arg_1822_);
                    crate::leanh::lean_dec_ref(v_arg_1819_);
                    crate::leanh::lean_dec_ref(v_e_1803_);
                    v_a_2126_ = crate::leanh::lean_ctor_get(v___x_1924_, 0);
                    v_isSharedCheck_2133_ = (!crate::leanh::lean_is_exclusive(v___x_1924_)) as u8;
                    if v_isSharedCheck_2133_ == 0 {
                        v___x_2128_ = v___x_1924_;
                        v_isShared_2129_ = v_isSharedCheck_2133_;
                        state = 50;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2126_);
                        crate::leanh::lean_dec(v___x_1924_);
                        v___x_2128_ = crate::leanh::lean_box(0);
                        v_isShared_2129_ = v_isSharedCheck_2133_;
                        state = 50;
                        continue;
                    }
                }
            }
            17 => {
                if crate::leanh::lean_obj_tag(v_a_1934_) == 1 {
                    crate::leanh::lean_del_object(v___x_1936_);
                    v_a_1938_ = crate::leanh::lean_ctor_get(v_a_1934_, 0);
                    crate::leanh::lean_inc(v_a_1938_);
                    crate::leanh::lean_dec_ref_known(v_a_1934_, 1);
                    v___x_1939_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1938_, v___y_1808_);
                    if crate::leanh::lean_obj_tag(v___x_1939_) == 0 {
                        v_a_1940_ = crate::leanh::lean_ctor_get(v___x_1939_, 0);
                        crate::leanh::lean_inc(v_a_1940_);
                        crate::leanh::lean_dec_ref_known(v___x_1939_, 1);
                        v___x_1941_ =
                            l_Lean_Meta_Sym_shareCommon___redArg(v_proof_1919_, v___y_1808_);
                        if crate::leanh::lean_obj_tag(v___x_1941_) == 0 {
                            v_a_1942_ = crate::leanh::lean_ctor_get(v___x_1941_, 0);
                            crate::leanh::lean_inc_n(v_a_1942_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_1941_, 1);
                            v___x_1943_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16;
                            v___x_1944_ = 0;
                            v___x_1945_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20_once), _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20);
                            v___x_1946_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21_once), _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21);
                            crate::leanh::lean_inc_ref_n(v_e_x27_1918_, 2);
                            crate::leanh::lean_inc_ref(v_arg_1827_);
                            v___x_1947_ = l_Lean_mkApp4(
                                v___x_1945_,
                                v_arg_1827_,
                                v_e_x27_1918_,
                                v_a_1942_,
                                v___x_1946_,
                            );
                            v___x_1948_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1949_ = lean_mk_empty_array_with_capacity(v___x_1948_);
                            crate::leanh::lean_inc_ref(v___x_1949_);
                            v___x_1950_ = lean_array_push(v___x_1949_, v___x_1947_);
                            v___x_1951_ = (crate::leanh::lean_unbox(v_a_1928_) as u8);
                            v___x_1952_ = (crate::leanh::lean_unbox(v_a_1928_) as u8);
                            v___x_1953_ = l_Lean_Expr_betaRev(
                                v_arg_1822_,
                                v___x_1950_,
                                v___x_1951_,
                                v___x_1952_,
                            );
                            crate::leanh::lean_dec_ref(v___x_1950_);
                            v___x_1954_ = l_Lean_mkLambda(
                                v___x_1943_,
                                v___x_1944_,
                                v_e_x27_1918_,
                                v___x_1953_,
                            );
                            v___x_1955_ =
                                l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1954_, v___y_1808_);
                            if crate::leanh::lean_obj_tag(v___x_1955_) == 0 {
                                v_a_1956_ = crate::leanh::lean_ctor_get(v___x_1955_, 0);
                                crate::leanh::lean_inc(v_a_1956_);
                                crate::leanh::lean_dec_ref_known(v___x_1955_, 1);
                                crate::leanh::lean_inc_ref_n(v_e_x27_1918_, 2);
                                v___x_1957_ = l_Lean_mkNot(v_e_x27_1918_);
                                v___x_1958_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24_once), _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24);
                                crate::leanh::lean_inc(v_a_1942_);
                                v___x_1959_ = l_Lean_mkApp4(
                                    v___x_1958_,
                                    v_arg_1827_,
                                    v_e_x27_1918_,
                                    v_a_1942_,
                                    v___x_1946_,
                                );
                                v___x_1960_ = lean_array_push(v___x_1949_, v___x_1959_);
                                v___x_1961_ = (crate::leanh::lean_unbox(v_a_1928_) as u8);
                                v___x_1962_ = (crate::leanh::lean_unbox(v_a_1928_) as u8);
                                crate::leanh::lean_dec(v_a_1928_);
                                v___x_1963_ = l_Lean_Expr_betaRev(
                                    v_arg_1819_,
                                    v___x_1960_,
                                    v___x_1961_,
                                    v___x_1962_,
                                );
                                crate::leanh::lean_dec_ref(v___x_1960_);
                                v___x_1964_ = l_Lean_mkLambda(
                                    v___x_1943_,
                                    v___x_1944_,
                                    v___x_1957_,
                                    v___x_1963_,
                                );
                                v___x_1965_ = l_Lean_Meta_Sym_shareCommonInc___redArg(
                                    v___x_1964_,
                                    v___y_1808_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1965_) == 0 {
                                    v_a_1966_ = crate::leanh::lean_ctor_get(v___x_1965_, 0);
                                    crate::leanh::lean_inc(v_a_1966_);
                                    crate::leanh::lean_dec_ref_known(v___x_1965_, 1);
                                    v___x_1967_ = crate::leanh::lean_unsigned_to_nat(4);
                                    v___x_1968_ =
                                        l_Lean_Expr_getBoundedAppFn(v___x_1967_, v_e_1803_);
                                    crate::leanh::lean_inc(v_a_1940_);
                                    crate::leanh::lean_inc_ref(v_e_x27_1918_);
                                    v___x_1969_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(v___x_1968_, v_e_x27_1918_, v_a_1940_, v_a_1956_, v_a_1966_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
                                    if crate::leanh::lean_obj_tag(v___x_1969_) == 0 {
                                        v_a_1970_ = crate::leanh::lean_ctor_get(v___x_1969_, 0);
                                        v_isSharedCheck_1983_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1969_)) as u8;
                                        if v_isSharedCheck_1983_ == 0 {
                                            v___x_1972_ = v___x_1969_;
                                            v_isShared_1973_ = v_isSharedCheck_1983_;
                                            state = 18;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1970_);
                                            crate::leanh::lean_dec(v___x_1969_);
                                            v___x_1972_ = crate::leanh::lean_box(0);
                                            v_isShared_1973_ = v_isSharedCheck_1983_;
                                            state = 18;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1942_);
                                        crate::leanh::lean_dec(v_a_1940_);
                                        crate::leanh::lean_del_object(v___x_1922_);
                                        crate::leanh::lean_dec_ref(v_e_x27_1918_);
                                        crate::leanh::lean_dec_ref(v_e_1803_);
                                        v_a_1984_ = crate::leanh::lean_ctor_get(v___x_1969_, 0);
                                        v_isSharedCheck_1991_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1969_)) as u8;
                                        if v_isSharedCheck_1991_ == 0 {
                                            v___x_1986_ = v___x_1969_;
                                            v_isShared_1987_ = v_isSharedCheck_1991_;
                                            state = 21;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1984_);
                                            crate::leanh::lean_dec(v___x_1969_);
                                            v___x_1986_ = crate::leanh::lean_box(0);
                                            v_isShared_1987_ = v_isSharedCheck_1991_;
                                            state = 21;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1956_);
                                    crate::leanh::lean_dec(v_a_1942_);
                                    crate::leanh::lean_dec(v_a_1940_);
                                    crate::leanh::lean_del_object(v___x_1922_);
                                    crate::leanh::lean_dec_ref(v_e_x27_1918_);
                                    crate::leanh::lean_dec_ref(v_e_1803_);
                                    v_a_1992_ = crate::leanh::lean_ctor_get(v___x_1965_, 0);
                                    v_isSharedCheck_1999_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1965_)) as u8;
                                    if v_isSharedCheck_1999_ == 0 {
                                        v___x_1994_ = v___x_1965_;
                                        v_isShared_1995_ = v_isSharedCheck_1999_;
                                        state = 23;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1992_);
                                        crate::leanh::lean_dec(v___x_1965_);
                                        v___x_1994_ = crate::leanh::lean_box(0);
                                        v_isShared_1995_ = v_isSharedCheck_1999_;
                                        state = 23;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1949_);
                                crate::leanh::lean_dec(v_a_1942_);
                                crate::leanh::lean_dec(v_a_1940_);
                                crate::leanh::lean_dec(v_a_1928_);
                                crate::leanh::lean_del_object(v___x_1922_);
                                crate::leanh::lean_dec_ref(v_e_x27_1918_);
                                crate::leanh::lean_dec_ref(v_arg_1827_);
                                crate::leanh::lean_dec_ref(v_arg_1819_);
                                crate::leanh::lean_dec_ref(v_e_1803_);
                                v_a_2000_ = crate::leanh::lean_ctor_get(v___x_1955_, 0);
                                v_isSharedCheck_2007_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1955_)) as u8;
                                if v_isSharedCheck_2007_ == 0 {
                                    v___x_2002_ = v___x_1955_;
                                    v_isShared_2003_ = v_isSharedCheck_2007_;
                                    state = 25;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2000_);
                                    crate::leanh::lean_dec(v___x_1955_);
                                    v___x_2002_ = crate::leanh::lean_box(0);
                                    v_isShared_2003_ = v_isSharedCheck_2007_;
                                    state = 25;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1940_);
                            crate::leanh::lean_dec(v_a_1928_);
                            crate::leanh::lean_del_object(v___x_1922_);
                            crate::leanh::lean_dec_ref(v_e_x27_1918_);
                            crate::leanh::lean_dec_ref(v_arg_1827_);
                            crate::leanh::lean_dec_ref(v_arg_1822_);
                            crate::leanh::lean_dec_ref(v_arg_1819_);
                            crate::leanh::lean_dec_ref(v_e_1803_);
                            v_a_2008_ = crate::leanh::lean_ctor_get(v___x_1941_, 0);
                            v_isSharedCheck_2015_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1941_)) as u8;
                            if v_isSharedCheck_2015_ == 0 {
                                v___x_2010_ = v___x_1941_;
                                v_isShared_2011_ = v_isSharedCheck_2015_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2008_);
                                crate::leanh::lean_dec(v___x_1941_);
                                v___x_2010_ = crate::leanh::lean_box(0);
                                v_isShared_2011_ = v_isSharedCheck_2015_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1928_);
                        crate::leanh::lean_del_object(v___x_1922_);
                        crate::leanh::lean_dec_ref(v_proof_1919_);
                        crate::leanh::lean_dec_ref(v_e_x27_1918_);
                        crate::leanh::lean_dec_ref(v_arg_1827_);
                        crate::leanh::lean_dec_ref(v_arg_1822_);
                        crate::leanh::lean_dec_ref(v_arg_1819_);
                        crate::leanh::lean_dec_ref(v_e_1803_);
                        v_a_2016_ = crate::leanh::lean_ctor_get(v___x_1939_, 0);
                        v_isSharedCheck_2023_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1939_)) as u8;
                        if v_isSharedCheck_2023_ == 0 {
                            v___x_2018_ = v___x_1939_;
                            v_isShared_2019_ = v_isSharedCheck_2023_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2016_);
                            crate::leanh::lean_dec(v___x_1939_);
                            v___x_2018_ = crate::leanh::lean_box(0);
                            v_isShared_2019_ = v_isSharedCheck_2023_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1934_);
                    crate::leanh::lean_del_object(v___x_1922_);
                    crate::leanh::lean_dec_ref(v_proof_1919_);
                    crate::leanh::lean_dec_ref(v_e_x27_1918_);
                    crate::leanh::lean_dec_ref(v_arg_1827_);
                    crate::leanh::lean_dec_ref(v_arg_1822_);
                    crate::leanh::lean_dec_ref(v_arg_1819_);
                    crate::leanh::lean_dec_ref(v_e_1803_);
                    v___x_2024_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    v___x_2025_ = (crate::leanh::lean_unbox(v_a_1928_) as u8);
                    crate::leanh::lean_ctor_set_uint8(v___x_2024_, 0 as u32, v___x_2025_);
                    v___x_2026_ = (crate::leanh::lean_unbox(v_a_1928_) as u8);
                    crate::leanh::lean_dec(v_a_1928_);
                    crate::leanh::lean_ctor_set_uint8(v___x_2024_, 1 as u32, v___x_2026_);
                    if v_isShared_1937_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1936_, 0, v___x_2024_);
                        v___x_2028_ = v___x_1936_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_2029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2024_);
                        v___x_2028_ = v_reuseFailAlloc_2029_;
                        state = 31;
                        continue;
                    }
                }
            }
            18 => {
                v___x_1974_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26;
                v___x_1975_ = l_Lean_Expr_replaceFn(v_e_1803_, v___x_1974_);
                v___x_1976_ = l_Lean_mkApp3(v___x_1975_, v_e_x27_1918_, v_a_1940_, v_a_1942_);
                if v_isShared_1923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1922_, 1, v___x_1976_);
                    crate::leanh::lean_ctor_set(v___x_1922_, 0, v_a_1970_);
                    v___x_1978_ = v___x_1922_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 1, v___x_1976_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1982_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_1920_,
                    );
                    v___x_1978_ = v_reuseFailAlloc_1982_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1978_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1833_,
                );
                if v_isShared_1973_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1972_, 0, v___x_1978_);
                    v___x_1980_ = v___x_1972_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
                    v___x_1980_ = v_reuseFailAlloc_1981_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1980_;
            }
            21 => {
                if v_isShared_1987_ == 0 {
                    v___x_1989_ = v___x_1986_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
                    v___x_1989_ = v_reuseFailAlloc_1990_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1989_;
            }
            23 => {
                if v_isShared_1995_ == 0 {
                    v___x_1997_ = v___x_1994_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
                    v___x_1997_ = v_reuseFailAlloc_1998_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1997_;
            }
            25 => {
                if v_isShared_2003_ == 0 {
                    v___x_2005_ = v___x_2002_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
                    v___x_2005_ = v_reuseFailAlloc_2006_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2005_;
            }
            27 => {
                if v_isShared_2011_ == 0 {
                    v___x_2013_ = v___x_2010_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
                    v___x_2013_ = v_reuseFailAlloc_2014_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2013_;
            }
            29 => {
                if v_isShared_2019_ == 0 {
                    v___x_2021_ = v___x_2018_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
                    v___x_2021_ = v_reuseFailAlloc_2022_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2021_;
            }
            31 => {
                return v___x_2028_;
            }
            32 => {
                if v_isShared_2034_ == 0 {
                    v___x_2036_ = v___x_2033_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2036_;
            }
            34 => {
                v___x_2053_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28;
                v___x_2054_ = l_Lean_Expr_replaceFn(v_e_1803_, v___x_2053_);
                v___x_2055_ = l_Lean_Expr_app___override(v___x_2054_, v_proof_1919_);
                if v_isShared_1923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1922_, 1, v___x_2055_);
                    crate::leanh::lean_ctor_set(v___x_1922_, 0, v_a_2049_);
                    v___x_2057_ = v___x_1922_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2062_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2062_, 1, v___x_2055_);
                    v___x_2057_ = v_reuseFailAlloc_2062_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2058_ = (crate::leanh::lean_unbox(v_a_1925_) as u8);
                crate::leanh::lean_dec(v_a_1925_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2057_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2058_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2057_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_1920_,
                );
                if v_isShared_2052_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2051_, 0, v___x_2057_);
                    v___x_2060_ = v___x_2051_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2061_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2057_);
                    v___x_2060_ = v_reuseFailAlloc_2061_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_2060_;
            }
            37 => {
                if v_isShared_2067_ == 0 {
                    v___x_2069_ = v___x_2066_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
                    v___x_2069_ = v_reuseFailAlloc_2070_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_2069_;
            }
            39 => {
                if v_isShared_2075_ == 0 {
                    v___x_2077_ = v___x_2074_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
                    v___x_2077_ = v_reuseFailAlloc_2078_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2077_;
            }
            41 => {
                if v_isShared_2083_ == 0 {
                    v___x_2085_ = v___x_2082_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2086_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
                    v___x_2085_ = v_reuseFailAlloc_2086_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2085_;
            }
            43 => {
                v___x_2100_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30;
                v___x_2101_ = l_Lean_Expr_replaceFn(v_e_1803_, v___x_2100_);
                v___x_2102_ = l_Lean_Expr_app___override(v___x_2101_, v_proof_1919_);
                if v_isShared_1923_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1922_, 1, v___x_2102_);
                    crate::leanh::lean_ctor_set(v___x_1922_, 0, v_a_2096_);
                    v___x_2104_ = v___x_1922_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2108_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2096_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2102_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2108_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_1920_,
                    );
                    v___x_2104_ = v_reuseFailAlloc_2108_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2104_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1802_,
                );
                if v_isShared_2099_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2098_, 0, v___x_2104_);
                    v___x_2106_ = v___x_2098_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2107_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
                    v___x_2106_ = v_reuseFailAlloc_2107_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_2106_;
            }
            46 => {
                if v_isShared_2113_ == 0 {
                    v___x_2115_ = v___x_2112_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_2116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
                    v___x_2115_ = v_reuseFailAlloc_2116_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_2115_;
            }
            48 => {
                if v_isShared_2121_ == 0 {
                    v___x_2123_ = v___x_2120_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_2124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
                    v___x_2123_ = v_reuseFailAlloc_2124_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_2123_;
            }
            50 => {
                if v_isShared_2129_ == 0 {
                    v___x_2131_ = v___x_2128_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_2132_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
                    v___x_2131_ = v_reuseFailAlloc_2132_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_2131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___boxed(
    mut v___x_2135_: *mut crate::leanh::LeanObject,
    mut v_e_2136_: *mut crate::leanh::LeanObject,
    mut v___y_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_37758__boxed_2147_: u8 = 0;
    let mut v_res_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_37758__boxed_2147_ = (crate::leanh::lean_unbox(v___x_2135_) as u8);
    v_res_2148_ =
        l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(
            v___x_37758__boxed_2147_,
            v_e_2136_,
            v___y_2137_,
            v___y_2138_,
            v___y_2139_,
            v___y_2140_,
            v___y_2141_,
            v___y_2142_,
            v___y_2143_,
            v___y_2144_,
            v___y_2145_,
        );
    crate::leanh::lean_dec(v___y_2145_);
    crate::leanh::lean_dec_ref(v___y_2144_);
    crate::leanh::lean_dec(v___y_2143_);
    crate::leanh::lean_dec_ref(v___y_2142_);
    crate::leanh::lean_dec(v___y_2141_);
    crate::leanh::lean_dec_ref(v___y_2140_);
    crate::leanh::lean_dec(v___y_2139_);
    crate::leanh::lean_dec_ref(v___y_2138_);
    crate::leanh::lean_dec(v___y_2137_);
    return v_res_2148_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(
    mut v_e_2149_: *mut crate::leanh::LeanObject,
    mut v_a_2150_: *mut crate::leanh::LeanObject,
    mut v_a_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
    mut v_a_2153_: *mut crate::leanh::LeanObject,
    mut v_a_2154_: *mut crate::leanh::LeanObject,
    mut v_a_2155_: *mut crate::leanh::LeanObject,
    mut v_a_2156_: *mut crate::leanh::LeanObject,
    mut v_a_2157_: *mut crate::leanh::LeanObject,
    mut v_a_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numArgs_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: u8 = 0;
    v_numArgs_2160_ = l_Lean_Expr_getAppNumArgs(v_e_2149_);
    v___x_2161_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_2162_ = lean_nat_dec_lt(v_numArgs_2160_, v___x_2161_);
    if v___x_2162_ == 0 {
        let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2163_ = crate::leanh::lean_box((v___x_2162_) as usize);
        v___f_2164_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___boxed as *mut core::ffi::c_void, 12, 1);
        crate::leanh::lean_closure_set(v___f_2164_, 0, v___x_2163_);
        v___x_2165_ = lean_nat_sub(v_numArgs_2160_, v___x_2161_);
        crate::leanh::lean_dec(v_numArgs_2160_);
        v___x_2166_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(
            v_e_2149_,
            v___x_2165_,
            v___f_2164_,
            v_a_2150_,
            v_a_2151_,
            v_a_2152_,
            v_a_2153_,
            v_a_2154_,
            v_a_2155_,
            v_a_2156_,
            v_a_2157_,
            v_a_2158_,
        );
        crate::leanh::lean_dec(v___x_2165_);
        return v___x_2166_;
    } else {
        let mut v___x_2167_: u8 = 0;
        let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_numArgs_2160_);
        crate::leanh::lean_dec_ref(v_e_2149_);
        v___x_2167_ = 0;
        v___x_2168_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
        crate::leanh::lean_ctor_set_uint8(v___x_2168_, 0 as u32, v___x_2162_);
        crate::leanh::lean_ctor_set_uint8(v___x_2168_, 1 as u32, v___x_2167_);
        v___x_2169_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2169_, 0, v___x_2168_);
        return v___x_2169_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___boxed(
    mut v_e_2170_: *mut crate::leanh::LeanObject,
    mut v_a_2171_: *mut crate::leanh::LeanObject,
    mut v_a_2172_: *mut crate::leanh::LeanObject,
    mut v_a_2173_: *mut crate::leanh::LeanObject,
    mut v_a_2174_: *mut crate::leanh::LeanObject,
    mut v_a_2175_: *mut crate::leanh::LeanObject,
    mut v_a_2176_: *mut crate::leanh::LeanObject,
    mut v_a_2177_: *mut crate::leanh::LeanObject,
    mut v_a_2178_: *mut crate::leanh::LeanObject,
    mut v_a_2179_: *mut crate::leanh::LeanObject,
    mut v_a_2180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2181_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(
        v_e_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_,
        v_a_2178_, v_a_2179_,
    );
    crate::leanh::lean_dec(v_a_2179_);
    crate::leanh::lean_dec_ref(v_a_2178_);
    crate::leanh::lean_dec(v_a_2177_);
    crate::leanh::lean_dec_ref(v_a_2176_);
    crate::leanh::lean_dec(v_a_2175_);
    crate::leanh::lean_dec_ref(v_a_2174_);
    crate::leanh::lean_dec(v_a_2173_);
    crate::leanh::lean_dec_ref(v_a_2172_);
    crate::leanh::lean_dec(v_a_2171_);
    return v_res_2181_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpCond___lam__0(
    mut v___x_2206_: u8,
    mut v_e_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
    mut v___y_2214_: *mut crate::leanh::LeanObject,
    mut v___y_2215_: *mut crate::leanh::LeanObject,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    let mut v_arg_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v_arg_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v_arg_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: u8 = 0;
    let mut v_arg_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2238_: u8 = 0;
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2243_: u8 = 0;
    let mut v___x_2244_: u8 = 0;
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2249_: u8 = 0;
    let mut v___x_2250_: u8 = 0;
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v_a_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2271_: u8 = 0;
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut v_a_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut v_e_x27_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_2291_: u8 = 0;
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2299_: u8 = 0;
    let mut v___x_2300_: u8 = 0;
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2306_: u8 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut v_a_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2327_: u8 = 0;
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut v_a_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2345_: u8 = 0;
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut v_a_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2363_: u8 = 0;
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2367_: u8 = 0;
    let mut v_isSharedCheck_2368_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2207_);
                v___x_2221_ = l_Lean_Expr_cleanupAnnotations(v_e_2207_);
                v___x_2222_ = l_Lean_Expr_isApp(v___x_2221_);
                if v___x_2222_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2221_);
                    crate::leanh::lean_dec_ref(v_e_2207_);
                    state = 1;
                    continue;
                } else {
                    v_arg_2223_ = crate::leanh::lean_ctor_get(v___x_2221_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2223_);
                    v___x_2224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2221_);
                    v___x_2225_ = l_Lean_Expr_isApp(v___x_2224_);
                    if v___x_2225_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2224_);
                        crate::leanh::lean_dec_ref(v_arg_2223_);
                        crate::leanh::lean_dec_ref(v_e_2207_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_2226_ = crate::leanh::lean_ctor_get(v___x_2224_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2226_);
                        v___x_2227_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2224_);
                        v___x_2228_ = l_Lean_Expr_isApp(v___x_2227_);
                        if v___x_2228_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2227_);
                            crate::leanh::lean_dec_ref(v_arg_2226_);
                            crate::leanh::lean_dec_ref(v_arg_2223_);
                            crate::leanh::lean_dec_ref(v_e_2207_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_2229_ = crate::leanh::lean_ctor_get(v___x_2227_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2229_);
                            v___x_2230_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2227_);
                            v___x_2231_ = l_Lean_Expr_isApp(v___x_2230_);
                            if v___x_2231_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2230_);
                                crate::leanh::lean_dec_ref(v_arg_2229_);
                                crate::leanh::lean_dec_ref(v_arg_2226_);
                                crate::leanh::lean_dec_ref(v_arg_2223_);
                                crate::leanh::lean_dec_ref(v_e_2207_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_2232_ = crate::leanh::lean_ctor_get(v___x_2230_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2232_);
                                v___x_2233_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2230_);
                                v___x_2234_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1;
                                v___x_2235_ = l_Lean_Expr_isConstOf(v___x_2233_, v___x_2234_);
                                if v___x_2235_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2233_);
                                    crate::leanh::lean_dec_ref(v_arg_2232_);
                                    crate::leanh::lean_dec_ref(v_arg_2229_);
                                    crate::leanh::lean_dec_ref(v_arg_2226_);
                                    crate::leanh::lean_dec_ref(v_arg_2223_);
                                    crate::leanh::lean_dec_ref(v_e_2207_);
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v___y_2216_);
                                    crate::leanh::lean_inc_ref(v___y_2215_);
                                    crate::leanh::lean_inc(v___y_2214_);
                                    crate::leanh::lean_inc_ref(v___y_2213_);
                                    crate::leanh::lean_inc(v___y_2212_);
                                    crate::leanh::lean_inc_ref(v___y_2211_);
                                    crate::leanh::lean_inc(v___y_2210_);
                                    crate::leanh::lean_inc_ref(v___y_2209_);
                                    crate::leanh::lean_inc(v___y_2208_);
                                    crate::leanh::lean_inc_ref(v_arg_2229_);
                                    v___x_2236_ = lean_sym_simp(
                                        v_arg_2229_,
                                        v___y_2208_,
                                        v___y_2209_,
                                        v___y_2210_,
                                        v___y_2211_,
                                        v___y_2212_,
                                        v___y_2213_,
                                        v___y_2214_,
                                        v___y_2215_,
                                        v___y_2216_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2236_) == 0 {
                                        v_a_2237_ = crate::leanh::lean_ctor_get(v___x_2236_, 0);
                                        crate::leanh::lean_inc(v_a_2237_);
                                        crate::leanh::lean_dec_ref_known(v___x_2236_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_2237_) == 0 {
                                            crate::leanh::lean_dec_ref(v_e_2207_);
                                            v_contextDependent_2238_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v_a_2237_, 1 as u32,
                                                );
                                            crate::leanh::lean_dec_ref_known(v_a_2237_, 0);
                                            v___x_2239_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(
                                                v___y_2211_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_2239_) == 0 {
                                                v_a_2240_ =
                                                    crate::leanh::lean_ctor_get(v___x_2239_, 0);
                                                v_isSharedCheck_2280_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2239_))
                                                        as u8;
                                                if v_isSharedCheck_2280_ == 0 {
                                                    v___x_2242_ = v___x_2239_;
                                                    v_isShared_2243_ = v_isSharedCheck_2280_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2240_);
                                                    crate::leanh::lean_dec(v___x_2239_);
                                                    v___x_2242_ = crate::leanh::lean_box(0);
                                                    v_isShared_2243_ = v_isSharedCheck_2280_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_2233_);
                                                crate::leanh::lean_dec_ref(v_arg_2232_);
                                                crate::leanh::lean_dec_ref(v_arg_2229_);
                                                crate::leanh::lean_dec_ref(v_arg_2226_);
                                                crate::leanh::lean_dec_ref(v_arg_2223_);
                                                v_a_2281_ =
                                                    crate::leanh::lean_ctor_get(v___x_2239_, 0);
                                                v_isSharedCheck_2288_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2239_))
                                                        as u8;
                                                if v_isSharedCheck_2288_ == 0 {
                                                    v___x_2283_ = v___x_2239_;
                                                    v_isShared_2284_ = v_isSharedCheck_2288_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2281_);
                                                    crate::leanh::lean_dec(v___x_2239_);
                                                    v___x_2283_ = crate::leanh::lean_box(0);
                                                    v_isShared_2284_ = v_isSharedCheck_2288_;
                                                    state = 9;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_2233_);
                                            crate::leanh::lean_dec_ref(v_arg_2232_);
                                            crate::leanh::lean_dec_ref(v_arg_2229_);
                                            v_e_x27_2289_ =
                                                crate::leanh::lean_ctor_get(v_a_2237_, 0);
                                            v_proof_2290_ =
                                                crate::leanh::lean_ctor_get(v_a_2237_, 1);
                                            v_contextDependent_2291_ =
                                                crate::leanh::lean_ctor_get_uint8(
                                                    v_a_2237_,
                                                    (core::mem::size_of::<
                                                        *mut crate::leanh::LeanObject,
                                                    >(
                                                    ) * 2
                                                        + 1)
                                                        as u32,
                                                );
                                            v_isSharedCheck_2368_ =
                                                (!crate::leanh::lean_is_exclusive(v_a_2237_)) as u8;
                                            if v_isSharedCheck_2368_ == 0 {
                                                v___x_2293_ = v_a_2237_;
                                                v_isShared_2294_ = v_isSharedCheck_2368_;
                                                state = 11;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_proof_2290_);
                                                crate::leanh::lean_inc(v_e_x27_2289_);
                                                crate::leanh::lean_dec(v_a_2237_);
                                                v___x_2293_ = crate::leanh::lean_box(0);
                                                v_isShared_2294_ = v_isSharedCheck_2368_;
                                                state = 11;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_2233_);
                                        crate::leanh::lean_dec_ref(v_arg_2232_);
                                        crate::leanh::lean_dec_ref(v_arg_2229_);
                                        crate::leanh::lean_dec_ref(v_arg_2226_);
                                        crate::leanh::lean_dec_ref(v_arg_2223_);
                                        crate::leanh::lean_dec_ref(v_e_2207_);
                                        return v___x_2236_;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2219_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_2219_, 0 as u32, v___x_2206_);
                crate::leanh::lean_ctor_set_uint8(v___x_2219_, 1 as u32, v___x_2206_);
                v___x_2220_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2220_, 0, v___x_2219_);
                return v___x_2220_;
            }
            2 => {
                v___x_2244_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_arg_2229_,
                        v_a_2240_,
                    );
                crate::leanh::lean_dec(v_a_2240_);
                if v___x_2244_ == 0 {
                    crate::leanh::lean_del_object(v___x_2242_);
                    v___x_2245_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_2211_);
                    if crate::leanh::lean_obj_tag(v___x_2245_) == 0 {
                        v_a_2246_ = crate::leanh::lean_ctor_get(v___x_2245_, 0);
                        v_isSharedCheck_2263_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2245_)) as u8;
                        if v_isSharedCheck_2263_ == 0 {
                            v___x_2248_ = v___x_2245_;
                            v_isShared_2249_ = v_isSharedCheck_2263_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2246_);
                            crate::leanh::lean_dec(v___x_2245_);
                            v___x_2248_ = crate::leanh::lean_box(0);
                            v_isShared_2249_ = v_isSharedCheck_2263_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2233_);
                        crate::leanh::lean_dec_ref(v_arg_2232_);
                        crate::leanh::lean_dec_ref(v_arg_2229_);
                        crate::leanh::lean_dec_ref(v_arg_2226_);
                        crate::leanh::lean_dec_ref(v_arg_2223_);
                        v_a_2264_ = crate::leanh::lean_ctor_get(v___x_2245_, 0);
                        v_isSharedCheck_2271_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2245_)) as u8;
                        if v_isSharedCheck_2271_ == 0 {
                            v___x_2266_ = v___x_2245_;
                            v_isShared_2267_ = v_isSharedCheck_2271_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2264_);
                            crate::leanh::lean_dec(v___x_2245_);
                            v___x_2266_ = crate::leanh::lean_box(0);
                            v_isShared_2267_ = v_isSharedCheck_2271_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_2229_);
                    v___x_2272_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5;
                    v___x_2273_ = l_Lean_Expr_constLevels_x21(v___x_2233_);
                    crate::leanh::lean_dec_ref(v___x_2233_);
                    v___x_2274_ = l_Lean_mkConst(v___x_2272_, v___x_2273_);
                    crate::leanh::lean_inc_ref(v_arg_2226_);
                    v___x_2275_ = l_Lean_mkApp3(v___x_2274_, v_arg_2232_, v_arg_2226_, v_arg_2223_);
                    v___x_2276_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_2276_, 0, v_arg_2226_);
                    crate::leanh::lean_ctor_set(v___x_2276_, 1, v___x_2275_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2276_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_2206_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2276_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_2238_,
                    );
                    if v_isShared_2243_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2242_, 0, v___x_2276_);
                        v___x_2278_ = v___x_2242_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2279_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
                        v___x_2278_ = v_reuseFailAlloc_2279_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2250_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_arg_2229_,
                        v_a_2246_,
                    );
                crate::leanh::lean_dec(v_a_2246_);
                crate::leanh::lean_dec_ref(v_arg_2229_);
                if v___x_2250_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2233_);
                    crate::leanh::lean_dec_ref(v_arg_2232_);
                    crate::leanh::lean_dec_ref(v_arg_2226_);
                    crate::leanh::lean_dec_ref(v_arg_2223_);
                    v___x_2251_ =
                        l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2235_, v_contextDependent_2238_);
                    if v_isShared_2249_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2248_, 0, v___x_2251_);
                        v___x_2253_ = v___x_2248_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
                        v___x_2253_ = v_reuseFailAlloc_2254_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2255_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3;
                    v___x_2256_ = l_Lean_Expr_constLevels_x21(v___x_2233_);
                    crate::leanh::lean_dec_ref(v___x_2233_);
                    v___x_2257_ = l_Lean_mkConst(v___x_2255_, v___x_2256_);
                    crate::leanh::lean_inc_ref(v_arg_2223_);
                    v___x_2258_ = l_Lean_mkApp3(v___x_2257_, v_arg_2232_, v_arg_2226_, v_arg_2223_);
                    v___x_2259_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_2259_, 0, v_arg_2223_);
                    crate::leanh::lean_ctor_set(v___x_2259_, 1, v___x_2258_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2259_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_2244_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2259_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_2238_,
                    );
                    if v_isShared_2249_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2248_, 0, v___x_2259_);
                        v___x_2261_ = v___x_2248_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
                        v___x_2261_ = v_reuseFailAlloc_2262_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2253_;
            }
            5 => {
                return v___x_2261_;
            }
            6 => {
                if v_isShared_2267_ == 0 {
                    v___x_2269_ = v___x_2266_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
                    v___x_2269_ = v_reuseFailAlloc_2270_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2269_;
            }
            8 => {
                return v___x_2278_;
            }
            9 => {
                if v_isShared_2284_ == 0 {
                    v___x_2286_ = v___x_2283_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
                    v___x_2286_ = v_reuseFailAlloc_2287_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2286_;
            }
            11 => {
                v___x_2295_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_2211_);
                if crate::leanh::lean_obj_tag(v___x_2295_) == 0 {
                    v_a_2296_ = crate::leanh::lean_ctor_get(v___x_2295_, 0);
                    v_isSharedCheck_2359_ = (!crate::leanh::lean_is_exclusive(v___x_2295_)) as u8;
                    if v_isSharedCheck_2359_ == 0 {
                        v___x_2298_ = v___x_2295_;
                        v_isShared_2299_ = v_isSharedCheck_2359_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2296_);
                        crate::leanh::lean_dec(v___x_2295_);
                        v___x_2298_ = crate::leanh::lean_box(0);
                        v_isShared_2299_ = v_isSharedCheck_2359_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2293_);
                    crate::leanh::lean_dec_ref(v_proof_2290_);
                    crate::leanh::lean_dec_ref(v_e_x27_2289_);
                    crate::leanh::lean_dec_ref(v_arg_2226_);
                    crate::leanh::lean_dec_ref(v_arg_2223_);
                    crate::leanh::lean_dec_ref(v_e_2207_);
                    v_a_2360_ = crate::leanh::lean_ctor_get(v___x_2295_, 0);
                    v_isSharedCheck_2367_ = (!crate::leanh::lean_is_exclusive(v___x_2295_)) as u8;
                    if v_isSharedCheck_2367_ == 0 {
                        v___x_2362_ = v___x_2295_;
                        v_isShared_2363_ = v_isSharedCheck_2367_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2360_);
                        crate::leanh::lean_dec(v___x_2295_);
                        v___x_2362_ = crate::leanh::lean_box(0);
                        v_isShared_2363_ = v_isSharedCheck_2367_;
                        state = 25;
                        continue;
                    }
                }
            }
            12 => {
                v___x_2300_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_e_x27_2289_,
                        v_a_2296_,
                    );
                crate::leanh::lean_dec(v_a_2296_);
                if v___x_2300_ == 0 {
                    crate::leanh::lean_del_object(v___x_2298_);
                    v___x_2301_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_2211_);
                    if crate::leanh::lean_obj_tag(v___x_2301_) == 0 {
                        v_a_2302_ = crate::leanh::lean_ctor_get(v___x_2301_, 0);
                        v_isSharedCheck_2341_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2301_)) as u8;
                        if v_isSharedCheck_2341_ == 0 {
                            v___x_2304_ = v___x_2301_;
                            v_isShared_2305_ = v_isSharedCheck_2341_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2302_);
                            crate::leanh::lean_dec(v___x_2301_);
                            v___x_2304_ = crate::leanh::lean_box(0);
                            v_isShared_2305_ = v_isSharedCheck_2341_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2293_);
                        crate::leanh::lean_dec_ref(v_proof_2290_);
                        crate::leanh::lean_dec_ref(v_e_x27_2289_);
                        crate::leanh::lean_dec_ref(v_arg_2226_);
                        crate::leanh::lean_dec_ref(v_arg_2223_);
                        crate::leanh::lean_dec_ref(v_e_2207_);
                        v_a_2342_ = crate::leanh::lean_ctor_get(v___x_2301_, 0);
                        v_isSharedCheck_2349_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2301_)) as u8;
                        if v_isSharedCheck_2349_ == 0 {
                            v___x_2344_ = v___x_2301_;
                            v_isShared_2345_ = v_isSharedCheck_2349_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2342_);
                            crate::leanh::lean_dec(v___x_2301_);
                            v___x_2344_ = crate::leanh::lean_box(0);
                            v_isShared_2345_ = v_isSharedCheck_2349_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_x27_2289_);
                    crate::leanh::lean_dec_ref(v_arg_2223_);
                    v___x_2350_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11;
                    v___x_2351_ = l_Lean_Expr_replaceFn(v_e_2207_, v___x_2350_);
                    v___x_2352_ = l_Lean_Expr_app___override(v___x_2351_, v_proof_2290_);
                    if v_isShared_2294_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2293_, 1, v___x_2352_);
                        crate::leanh::lean_ctor_set(v___x_2293_, 0, v_arg_2226_);
                        v___x_2354_ = v___x_2293_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2358_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_arg_2226_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2352_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2358_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                            v_contextDependent_2291_,
                        );
                        v___x_2354_ = v_reuseFailAlloc_2358_;
                        state = 23;
                        continue;
                    }
                }
            }
            13 => {
                v___x_2306_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_e_x27_2289_,
                        v_a_2302_,
                    );
                crate::leanh::lean_dec(v_a_2302_);
                if v___x_2306_ == 0 {
                    crate::leanh::lean_del_object(v___x_2304_);
                    v___x_2307_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2308_ = l_Lean_Expr_getBoundedAppFn(v___x_2307_, v_e_2207_);
                    crate::leanh::lean_inc_ref(v_e_x27_2289_);
                    v___x_2309_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(v___x_2308_, v_e_x27_2289_, v_arg_2226_, v_arg_2223_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
                    if crate::leanh::lean_obj_tag(v___x_2309_) == 0 {
                        v_a_2310_ = crate::leanh::lean_ctor_get(v___x_2309_, 0);
                        v_isSharedCheck_2323_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2309_)) as u8;
                        if v_isSharedCheck_2323_ == 0 {
                            v___x_2312_ = v___x_2309_;
                            v_isShared_2313_ = v_isSharedCheck_2323_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2310_);
                            crate::leanh::lean_dec(v___x_2309_);
                            v___x_2312_ = crate::leanh::lean_box(0);
                            v_isShared_2313_ = v_isSharedCheck_2323_;
                            state = 14;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2293_);
                        crate::leanh::lean_dec_ref(v_proof_2290_);
                        crate::leanh::lean_dec_ref(v_e_x27_2289_);
                        crate::leanh::lean_dec_ref(v_e_2207_);
                        v_a_2324_ = crate::leanh::lean_ctor_get(v___x_2309_, 0);
                        v_isSharedCheck_2331_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2309_)) as u8;
                        if v_isSharedCheck_2331_ == 0 {
                            v___x_2326_ = v___x_2309_;
                            v_isShared_2327_ = v_isSharedCheck_2331_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2324_);
                            crate::leanh::lean_dec(v___x_2309_);
                            v___x_2326_ = crate::leanh::lean_box(0);
                            v_isShared_2327_ = v_isSharedCheck_2331_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_x27_2289_);
                    crate::leanh::lean_dec_ref(v_arg_2226_);
                    v___x_2332_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9;
                    v___x_2333_ = l_Lean_Expr_replaceFn(v_e_2207_, v___x_2332_);
                    v___x_2334_ = l_Lean_Expr_app___override(v___x_2333_, v_proof_2290_);
                    if v_isShared_2294_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2293_, 1, v___x_2334_);
                        crate::leanh::lean_ctor_set(v___x_2293_, 0, v_arg_2223_);
                        v___x_2336_ = v___x_2293_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_2340_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_arg_2223_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 1, v___x_2334_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2340_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                            v_contextDependent_2291_,
                        );
                        v___x_2336_ = v_reuseFailAlloc_2340_;
                        state = 19;
                        continue;
                    }
                }
            }
            14 => {
                v___x_2314_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7;
                v___x_2315_ = l_Lean_Expr_replaceFn(v_e_2207_, v___x_2314_);
                v___x_2316_ = l_Lean_mkAppB(v___x_2315_, v_e_x27_2289_, v_proof_2290_);
                if v_isShared_2294_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2293_, 1, v___x_2316_);
                    crate::leanh::lean_ctor_set(v___x_2293_, 0, v_a_2310_);
                    v___x_2318_ = v___x_2293_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2322_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 1, v___x_2316_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2322_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_2291_,
                    );
                    v___x_2318_ = v_reuseFailAlloc_2322_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2318_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2235_,
                );
                if v_isShared_2313_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2312_, 0, v___x_2318_);
                    v___x_2320_ = v___x_2312_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
                    v___x_2320_ = v_reuseFailAlloc_2321_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2320_;
            }
            17 => {
                if v_isShared_2327_ == 0 {
                    v___x_2329_ = v___x_2326_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
                    v___x_2329_ = v_reuseFailAlloc_2330_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2329_;
            }
            19 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2336_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2300_,
                );
                if v_isShared_2305_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2304_, 0, v___x_2336_);
                    v___x_2338_ = v___x_2304_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2339_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
                    v___x_2338_ = v_reuseFailAlloc_2339_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2338_;
            }
            21 => {
                if v_isShared_2345_ == 0 {
                    v___x_2347_ = v___x_2344_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2348_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
                    v___x_2347_ = v_reuseFailAlloc_2348_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2347_;
            }
            23 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2354_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2206_,
                );
                if v_isShared_2299_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2298_, 0, v___x_2354_);
                    v___x_2356_ = v___x_2298_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
                    v___x_2356_ = v_reuseFailAlloc_2357_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2356_;
            }
            25 => {
                if v_isShared_2363_ == 0 {
                    v___x_2365_ = v___x_2362_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2366_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
                    v___x_2365_ = v_reuseFailAlloc_2366_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpCond___lam__0___boxed(
    mut v___x_2369_: *mut crate::leanh::LeanObject,
    mut v_e_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14280__boxed_2381_: u8 = 0;
    let mut v_res_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14280__boxed_2381_ = (crate::leanh::lean_unbox(v___x_2369_) as u8);
    v_res_2382_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0(
        v___x_14280__boxed_2381_,
        v_e_2370_,
        v___y_2371_,
        v___y_2372_,
        v___y_2373_,
        v___y_2374_,
        v___y_2375_,
        v___y_2376_,
        v___y_2377_,
        v___y_2378_,
        v___y_2379_,
    );
    crate::leanh::lean_dec(v___y_2379_);
    crate::leanh::lean_dec_ref(v___y_2378_);
    crate::leanh::lean_dec(v___y_2377_);
    crate::leanh::lean_dec_ref(v___y_2376_);
    crate::leanh::lean_dec(v___y_2375_);
    crate::leanh::lean_dec_ref(v___y_2374_);
    crate::leanh::lean_dec(v___y_2373_);
    crate::leanh::lean_dec_ref(v___y_2372_);
    crate::leanh::lean_dec(v___y_2371_);
    return v_res_2382_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpCond(
    mut v_e_2383_: *mut crate::leanh::LeanObject,
    mut v_a_2384_: *mut crate::leanh::LeanObject,
    mut v_a_2385_: *mut crate::leanh::LeanObject,
    mut v_a_2386_: *mut crate::leanh::LeanObject,
    mut v_a_2387_: *mut crate::leanh::LeanObject,
    mut v_a_2388_: *mut crate::leanh::LeanObject,
    mut v_a_2389_: *mut crate::leanh::LeanObject,
    mut v_a_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numArgs_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: u8 = 0;
    v_numArgs_2394_ = l_Lean_Expr_getAppNumArgs(v_e_2383_);
    v___x_2395_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_2396_ = lean_nat_dec_lt(v_numArgs_2394_, v___x_2395_);
    if v___x_2396_ == 0 {
        let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2397_ = crate::leanh::lean_box((v___x_2396_) as usize);
        v___f_2398_ = crate::leanh::lean_alloc_closure(
            l_Lean_Meta_Sym_Simp_simpCond___lam__0___boxed as *mut core::ffi::c_void,
            12,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2398_, 0, v___x_2397_);
        v___x_2399_ = lean_nat_sub(v_numArgs_2394_, v___x_2395_);
        crate::leanh::lean_dec(v_numArgs_2394_);
        v___x_2400_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(
            v_e_2383_,
            v___x_2399_,
            v___f_2398_,
            v_a_2384_,
            v_a_2385_,
            v_a_2386_,
            v_a_2387_,
            v_a_2388_,
            v_a_2389_,
            v_a_2390_,
            v_a_2391_,
            v_a_2392_,
        );
        crate::leanh::lean_dec(v___x_2399_);
        return v___x_2400_;
    } else {
        let mut v___x_2401_: u8 = 0;
        let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_numArgs_2394_);
        crate::leanh::lean_dec_ref(v_e_2383_);
        v___x_2401_ = 0;
        v___x_2402_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
        crate::leanh::lean_ctor_set_uint8(v___x_2402_, 0 as u32, v___x_2396_);
        crate::leanh::lean_ctor_set_uint8(v___x_2402_, 1 as u32, v___x_2401_);
        v___x_2403_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2403_, 0, v___x_2402_);
        return v___x_2403_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpCond___boxed(
    mut v_e_2404_: *mut crate::leanh::LeanObject,
    mut v_a_2405_: *mut crate::leanh::LeanObject,
    mut v_a_2406_: *mut crate::leanh::LeanObject,
    mut v_a_2407_: *mut crate::leanh::LeanObject,
    mut v_a_2408_: *mut crate::leanh::LeanObject,
    mut v_a_2409_: *mut crate::leanh::LeanObject,
    mut v_a_2410_: *mut crate::leanh::LeanObject,
    mut v_a_2411_: *mut crate::leanh::LeanObject,
    mut v_a_2412_: *mut crate::leanh::LeanObject,
    mut v_a_2413_: *mut crate::leanh::LeanObject,
    mut v_a_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2415_ = l_Lean_Meta_Sym_Simp_simpCond(
        v_e_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_,
        v_a_2412_, v_a_2413_,
    );
    crate::leanh::lean_dec(v_a_2413_);
    crate::leanh::lean_dec_ref(v_a_2412_);
    crate::leanh::lean_dec(v_a_2411_);
    crate::leanh::lean_dec_ref(v_a_2410_);
    crate::leanh::lean_dec(v_a_2409_);
    crate::leanh::lean_dec_ref(v_a_2408_);
    crate::leanh::lean_dec(v_a_2407_);
    crate::leanh::lean_dec_ref(v_a_2406_);
    crate::leanh::lean_dec(v_a_2405_);
    return v_res_2415_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(
    mut v_declName_2416_: *mut crate::leanh::LeanObject,
    mut v___y_2417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2419_ = lean_st_ref_get(v___y_2417_);
    v_env_2420_ = crate::leanh::lean_ctor_get(v___x_2419_, 0);
    crate::leanh::lean_inc_ref(v_env_2420_);
    crate::leanh::lean_dec(v___x_2419_);
    v___x_2421_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2420_, v_declName_2416_);
    v___x_2422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2422_, 0, v___x_2421_);
    return v___x_2422_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg___boxed(
    mut v_declName_2423_: *mut crate::leanh::LeanObject,
    mut v___y_2424_: *mut crate::leanh::LeanObject,
    mut v___y_2425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2426_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(v_declName_2423_, v___y_2424_);
    crate::leanh::lean_dec(v___y_2424_);
    return v_res_2426_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(
    mut v_declName_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
    mut v___y_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
    mut v___y_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2438_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(v_declName_2427_, v___y_2436_);
    return v___x_2438_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___boxed(
    mut v_declName_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
    mut v___y_2443_: *mut crate::leanh::LeanObject,
    mut v___y_2444_: *mut crate::leanh::LeanObject,
    mut v___y_2445_: *mut crate::leanh::LeanObject,
    mut v___y_2446_: *mut crate::leanh::LeanObject,
    mut v___y_2447_: *mut crate::leanh::LeanObject,
    mut v___y_2448_: *mut crate::leanh::LeanObject,
    mut v___y_2449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2450_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(v_declName_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
    crate::leanh::lean_dec(v___y_2448_);
    crate::leanh::lean_dec_ref(v___y_2447_);
    crate::leanh::lean_dec(v___y_2446_);
    crate::leanh::lean_dec_ref(v___y_2445_);
    crate::leanh::lean_dec(v___y_2444_);
    crate::leanh::lean_dec_ref(v___y_2443_);
    crate::leanh::lean_dec(v___y_2442_);
    crate::leanh::lean_dec_ref(v___y_2441_);
    crate::leanh::lean_dec(v___y_2440_);
    return v_res_2450_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(
    mut v_declName_2453_: *mut crate::leanh::LeanObject,
    mut v_e_2454_: *mut crate::leanh::LeanObject,
    mut v_a_2455_: *mut crate::leanh::LeanObject,
    mut v_a_2456_: *mut crate::leanh::LeanObject,
    mut v_a_2457_: *mut crate::leanh::LeanObject,
    mut v_a_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
    mut v_a_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2476_: u8 = 0;
    let mut v___x_2477_: u8 = 0;
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2482_: u8 = 0;
    let mut v_a_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2486_: u8 = 0;
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut v_a_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2498_: u8 = 0;
    let mut v_a_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2502_: u8 = 0;
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2506_: u8 = 0;
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2511_: u8 = 0;
    let mut v_val_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v_contextDependent_2523_: u8 = 0;
    let mut v___x_2524_: u8 = 0;
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2529_: u8 = 0;
    let mut v_unused_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut v_a_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2539_: u8 = 0;
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2543_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2465_ = l_Lean_Meta_reduceRecMatcher_x3f(
                    v_e_2454_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_,
                );
                if crate::leanh::lean_obj_tag(v___x_2465_) == 0 {
                    v_a_2466_ = crate::leanh::lean_ctor_get(v___x_2465_, 0);
                    crate::leanh::lean_inc(v_a_2466_);
                    crate::leanh::lean_dec_ref_known(v___x_2465_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2466_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_2454_);
                        crate::leanh::lean_dec(v_declName_2453_);
                        v_val_2467_ = crate::leanh::lean_ctor_get(v_a_2466_, 0);
                        crate::leanh::lean_inc(v_val_2467_);
                        crate::leanh::lean_dec_ref_known(v_a_2466_, 1);
                        v___x_2468_ = l_Lean_Meta_Sym_foldProjs(
                            v_val_2467_,
                            v_a_2460_,
                            v_a_2461_,
                            v_a_2462_,
                            v_a_2463_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2468_) == 0 {
                            v_a_2469_ = crate::leanh::lean_ctor_get(v___x_2468_, 0);
                            crate::leanh::lean_inc(v_a_2469_);
                            crate::leanh::lean_dec_ref_known(v___x_2468_, 1);
                            v___x_2470_ =
                                l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_2469_, v_a_2459_);
                            if crate::leanh::lean_obj_tag(v___x_2470_) == 0 {
                                v_a_2471_ = crate::leanh::lean_ctor_get(v___x_2470_, 0);
                                crate::leanh::lean_inc_n(v_a_2471_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_2470_, 1);
                                v___x_2472_ = l_Lean_Meta_Sym_mkEqRefl___redArg(
                                    v_a_2471_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_,
                                    v_a_2463_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2472_) == 0 {
                                    v_a_2473_ = crate::leanh::lean_ctor_get(v___x_2472_, 0);
                                    v_isSharedCheck_2482_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2472_)) as u8;
                                    if v_isSharedCheck_2482_ == 0 {
                                        v___x_2475_ = v___x_2472_;
                                        v_isShared_2476_ = v_isSharedCheck_2482_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2473_);
                                        crate::leanh::lean_dec(v___x_2472_);
                                        v___x_2475_ = crate::leanh::lean_box(0);
                                        v_isShared_2476_ = v_isSharedCheck_2482_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2471_);
                                    v_a_2483_ = crate::leanh::lean_ctor_get(v___x_2472_, 0);
                                    v_isSharedCheck_2490_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2472_)) as u8;
                                    if v_isSharedCheck_2490_ == 0 {
                                        v___x_2485_ = v___x_2472_;
                                        v_isShared_2486_ = v_isSharedCheck_2490_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2483_);
                                        crate::leanh::lean_dec(v___x_2472_);
                                        v___x_2485_ = crate::leanh::lean_box(0);
                                        v_isShared_2486_ = v_isSharedCheck_2490_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_2491_ = crate::leanh::lean_ctor_get(v___x_2470_, 0);
                                v_isSharedCheck_2498_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2470_)) as u8;
                                if v_isSharedCheck_2498_ == 0 {
                                    v___x_2493_ = v___x_2470_;
                                    v_isShared_2494_ = v_isSharedCheck_2498_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2491_);
                                    crate::leanh::lean_dec(v___x_2470_);
                                    v___x_2493_ = crate::leanh::lean_box(0);
                                    v_isShared_2494_ = v_isSharedCheck_2498_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v_a_2499_ = crate::leanh::lean_ctor_get(v___x_2468_, 0);
                            v_isSharedCheck_2506_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2468_)) as u8;
                            if v_isSharedCheck_2506_ == 0 {
                                v___x_2501_ = v___x_2468_;
                                v_isShared_2502_ = v_isSharedCheck_2506_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2499_);
                                crate::leanh::lean_dec(v___x_2468_);
                                v___x_2501_ = crate::leanh::lean_box(0);
                                v_isShared_2502_ = v_isSharedCheck_2506_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2466_);
                        v___x_2507_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(v_declName_2453_, v_a_2463_);
                        v_a_2508_ = crate::leanh::lean_ctor_get(v___x_2507_, 0);
                        v_isSharedCheck_2535_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2507_)) as u8;
                        if v_isSharedCheck_2535_ == 0 {
                            v___x_2510_ = v___x_2507_;
                            v_isShared_2511_ = v_isSharedCheck_2535_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2508_);
                            crate::leanh::lean_dec(v___x_2507_);
                            v___x_2510_ = crate::leanh::lean_box(0);
                            v_isShared_2511_ = v_isSharedCheck_2535_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2454_);
                    crate::leanh::lean_dec(v_declName_2453_);
                    v_a_2536_ = crate::leanh::lean_ctor_get(v___x_2465_, 0);
                    v_isSharedCheck_2543_ = (!crate::leanh::lean_is_exclusive(v___x_2465_)) as u8;
                    if v_isSharedCheck_2543_ == 0 {
                        v___x_2538_ = v___x_2465_;
                        v_isShared_2539_ = v_isSharedCheck_2543_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2536_);
                        crate::leanh::lean_dec(v___x_2465_);
                        v___x_2538_ = crate::leanh::lean_box(0);
                        v_isShared_2539_ = v_isSharedCheck_2543_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2477_ = 0;
                v___x_2478_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_2478_, 0, v_a_2471_);
                crate::leanh::lean_ctor_set(v___x_2478_, 1, v_a_2473_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2478_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2477_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2478_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_2477_,
                );
                if v_isShared_2476_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2475_, 0, v___x_2478_);
                    v___x_2480_ = v___x_2475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2481_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2478_);
                    v___x_2480_ = v_reuseFailAlloc_2481_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2480_;
            }
            3 => {
                if v_isShared_2486_ == 0 {
                    v___x_2488_ = v___x_2485_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
                    v___x_2488_ = v_reuseFailAlloc_2489_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2488_;
            }
            5 => {
                if v_isShared_2494_ == 0 {
                    v___x_2496_ = v___x_2493_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2497_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
                    v___x_2496_ = v_reuseFailAlloc_2497_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2496_;
            }
            7 => {
                if v_isShared_2502_ == 0 {
                    v___x_2504_ = v___x_2501_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2505_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
                    v___x_2504_ = v_reuseFailAlloc_2505_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2504_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_a_2508_) == 1 {
                    crate::leanh::lean_del_object(v___x_2510_);
                    v_val_2512_ = crate::leanh::lean_ctor_get(v_a_2508_, 0);
                    crate::leanh::lean_inc(v_val_2512_);
                    crate::leanh::lean_dec_ref_known(v_a_2508_, 1);
                    v_numParams_2513_ = crate::leanh::lean_ctor_get(v_val_2512_, 0);
                    crate::leanh::lean_inc(v_numParams_2513_);
                    v_numDiscrs_2514_ = crate::leanh::lean_ctor_get(v_val_2512_, 1);
                    crate::leanh::lean_inc(v_numDiscrs_2514_);
                    crate::leanh::lean_dec(v_val_2512_);
                    v___x_2515_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2516_ = lean_nat_add(v_numParams_2513_, v___x_2515_);
                    crate::leanh::lean_dec(v_numParams_2513_);
                    v___x_2517_ = lean_nat_add(v___x_2516_, v_numDiscrs_2514_);
                    crate::leanh::lean_dec(v_numDiscrs_2514_);
                    v___x_2518_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(
                        v_e_2454_,
                        v___x_2516_,
                        v___x_2517_,
                        v_a_2455_,
                        v_a_2456_,
                        v_a_2457_,
                        v_a_2458_,
                        v_a_2459_,
                        v_a_2460_,
                        v_a_2461_,
                        v_a_2462_,
                        v_a_2463_,
                    );
                    crate::leanh::lean_dec(v___x_2517_);
                    crate::leanh::lean_dec(v___x_2516_);
                    if crate::leanh::lean_obj_tag(v___x_2518_) == 0 {
                        v_a_2519_ = crate::leanh::lean_ctor_get(v___x_2518_, 0);
                        crate::leanh::lean_inc(v_a_2519_);
                        if crate::leanh::lean_obj_tag(v_a_2519_) == 0 {
                            v_isSharedCheck_2529_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2518_)) as u8;
                            if v_isSharedCheck_2529_ == 0 {
                                v_unused_2530_ = crate::leanh::lean_ctor_get(v___x_2518_, 0);
                                crate::leanh::lean_dec(v_unused_2530_);
                                v___x_2521_ = v___x_2518_;
                                v_isShared_2522_ = v_isSharedCheck_2529_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2518_);
                                v___x_2521_ = crate::leanh::lean_box(0);
                                v_isShared_2522_ = v_isSharedCheck_2529_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_2519_, 2);
                            return v___x_2518_;
                        }
                    } else {
                        return v___x_2518_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2508_);
                    crate::leanh::lean_dec_ref(v_e_2454_);
                    v___x_2531_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0;
                    if v_isShared_2511_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2510_, 0, v___x_2531_);
                        v___x_2533_ = v___x_2510_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2534_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
                        v___x_2533_ = v_reuseFailAlloc_2534_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                v_contextDependent_2523_ = crate::leanh::lean_ctor_get_uint8(v_a_2519_, 1 as u32);
                crate::leanh::lean_dec_ref_known(v_a_2519_, 0);
                v___x_2524_ = 1;
                v___x_2525_ =
                    l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2524_, v_contextDependent_2523_);
                if v_isShared_2522_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2521_, 0, v___x_2525_);
                    v___x_2527_ = v___x_2521_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2525_);
                    v___x_2527_ = v_reuseFailAlloc_2528_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2527_;
            }
            12 => {
                return v___x_2533_;
            }
            13 => {
                if v_isShared_2539_ == 0 {
                    v___x_2541_ = v___x_2538_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2542_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
                    v___x_2541_ = v_reuseFailAlloc_2542_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___boxed(
    mut v_declName_2544_: *mut crate::leanh::LeanObject,
    mut v_e_2545_: *mut crate::leanh::LeanObject,
    mut v_a_2546_: *mut crate::leanh::LeanObject,
    mut v_a_2547_: *mut crate::leanh::LeanObject,
    mut v_a_2548_: *mut crate::leanh::LeanObject,
    mut v_a_2549_: *mut crate::leanh::LeanObject,
    mut v_a_2550_: *mut crate::leanh::LeanObject,
    mut v_a_2551_: *mut crate::leanh::LeanObject,
    mut v_a_2552_: *mut crate::leanh::LeanObject,
    mut v_a_2553_: *mut crate::leanh::LeanObject,
    mut v_a_2554_: *mut crate::leanh::LeanObject,
    mut v_a_2555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(
        v_declName_2544_,
        v_e_2545_,
        v_a_2546_,
        v_a_2547_,
        v_a_2548_,
        v_a_2549_,
        v_a_2550_,
        v_a_2551_,
        v_a_2552_,
        v_a_2553_,
        v_a_2554_,
    );
    crate::leanh::lean_dec(v_a_2554_);
    crate::leanh::lean_dec_ref(v_a_2553_);
    crate::leanh::lean_dec(v_a_2552_);
    crate::leanh::lean_dec_ref(v_a_2551_);
    crate::leanh::lean_dec(v_a_2550_);
    crate::leanh::lean_dec_ref(v_a_2549_);
    crate::leanh::lean_dec(v_a_2548_);
    crate::leanh::lean_dec_ref(v_a_2547_);
    crate::leanh::lean_dec(v_a_2546_);
    return v_res_2556_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpControl(
    mut v_e_2557_: *mut crate::leanh::LeanObject,
    mut v_a_2558_: *mut crate::leanh::LeanObject,
    mut v_a_2559_: *mut crate::leanh::LeanObject,
    mut v_a_2560_: *mut crate::leanh::LeanObject,
    mut v_a_2561_: *mut crate::leanh::LeanObject,
    mut v_a_2562_: *mut crate::leanh::LeanObject,
    mut v_a_2563_: *mut crate::leanh::LeanObject,
    mut v_a_2564_: *mut crate::leanh::LeanObject,
    mut v_a_2565_: *mut crate::leanh::LeanObject,
    mut v_a_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2568_: u8 = 0;
    v___x_2568_ = l_Lean_Expr_isApp(v_e_2557_);
    if v___x_2568_ == 0 {
        let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_e_2557_);
        v___x_2569_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
        crate::leanh::lean_ctor_set_uint8(v___x_2569_, 0 as u32, v___x_2568_);
        crate::leanh::lean_ctor_set_uint8(v___x_2569_, 1 as u32, v___x_2568_);
        v___x_2570_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2570_, 0, v___x_2569_);
        return v___x_2570_;
    } else {
        let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2571_ = l_Lean_Expr_getAppFn(v_e_2557_);
        if crate::leanh::lean_obj_tag(v___x_2571_) == 4 {
            let mut v_declName_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2574_: u8 = 0;
            v_declName_2572_ = crate::leanh::lean_ctor_get(v___x_2571_, 0);
            crate::leanh::lean_inc(v_declName_2572_);
            crate::leanh::lean_dec_ref_known(v___x_2571_, 2);
            v___x_2573_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1;
            v___x_2574_ = lean_name_eq(v_declName_2572_, v___x_2573_);
            if v___x_2574_ == 0 {
                let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2576_: u8 = 0;
                v___x_2575_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1;
                v___x_2576_ = lean_name_eq(v_declName_2572_, v___x_2575_);
                if v___x_2576_ == 0 {
                    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2578_: u8 = 0;
                    v___x_2577_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1;
                    v___x_2578_ = lean_name_eq(v_declName_2572_, v___x_2577_);
                    if v___x_2578_ == 0 {
                        let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2579_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(v_declName_2572_, v_e_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
                        return v___x_2579_;
                    } else {
                        let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_declName_2572_);
                        v___x_2580_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(v_e_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
                        return v___x_2580_;
                    }
                } else {
                    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_declName_2572_);
                    v___x_2581_ = l_Lean_Meta_Sym_Simp_simpCond(
                        v_e_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_,
                        v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_,
                    );
                    return v___x_2581_;
                }
            } else {
                let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_declName_2572_);
                v___x_2582_ =
                    l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(
                        v_e_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_,
                        v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_,
                    );
                return v___x_2582_;
            }
        } else {
            let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_2571_);
            crate::leanh::lean_dec_ref(v_e_2557_);
            v___x_2583_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0;
            v___x_2584_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2584_, 0, v___x_2583_);
            return v___x_2584_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpControl___boxed(
    mut v_e_2585_: *mut crate::leanh::LeanObject,
    mut v_a_2586_: *mut crate::leanh::LeanObject,
    mut v_a_2587_: *mut crate::leanh::LeanObject,
    mut v_a_2588_: *mut crate::leanh::LeanObject,
    mut v_a_2589_: *mut crate::leanh::LeanObject,
    mut v_a_2590_: *mut crate::leanh::LeanObject,
    mut v_a_2591_: *mut crate::leanh::LeanObject,
    mut v_a_2592_: *mut crate::leanh::LeanObject,
    mut v_a_2593_: *mut crate::leanh::LeanObject,
    mut v_a_2594_: *mut crate::leanh::LeanObject,
    mut v_a_2595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2596_ = l_Lean_Meta_Sym_Simp_simpControl(
        v_e_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_,
        v_a_2593_, v_a_2594_,
    );
    crate::leanh::lean_dec(v_a_2594_);
    crate::leanh::lean_dec_ref(v_a_2593_);
    crate::leanh::lean_dec(v_a_2592_);
    crate::leanh::lean_dec_ref(v_a_2591_);
    crate::leanh::lean_dec(v_a_2590_);
    crate::leanh::lean_dec_ref(v_a_2589_);
    crate::leanh::lean_dec(v_a_2588_);
    crate::leanh::lean_dec_ref(v_a_2587_);
    crate::leanh::lean_dec(v_a_2586_);
    return v_res_2596_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Sym_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_ControlFlow(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_ControlFlow(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Sym_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
}
