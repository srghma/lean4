// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Forall
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.AlphaShareBuilder Lean.Meta.Sym.Simp.Result
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_bindingBody_x21,
    l_Lean_Expr_bindingDomain_x21, l_Lean_Expr_bvar___override, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_constLevels_x21, l_Lean_Expr_forallE___override,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_isApp, l_Lean_Expr_isArrow, l_Lean_Expr_isConstOf,
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkApp6,
    l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkLambda, l_Lean_mkSort,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_isZero, l_Lean_Level_ofNat, l_Lean_Level_succ___override, l_Lean_mkLevelIMax_x27,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_getLevel, l_Lean_Meta_isProp};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, l_Lean_Meta_Sym_Internal_Sym_assertShared,
    l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
    runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::InferType::l_Lean_Meta_Sym_getLevel___redArg;
use crate::r#gen::Lean::Meta::Sym::Simp::Result::{
    initialize_Lean_Meta_Sym_Simp_Result, l_Lean_Meta_Sym_Simp_Result_getResultExpr,
    runtime_initialize_Lean_Meta_Sym_Simp_Result,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, l_Lean_Meta_Sym_Simp_mkRflResult,
    l_Lean_Meta_Sym_Simp_mkRflResultCD, l_Lean_Meta_Sym_Simp_simp___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getTrueExpr___redArg, l_Lean_Meta_Sym_isFalseExpr___redArg,
    l_Lean_Meta_Sym_isTrueExpr___redArg, l_Lean_Meta_Sym_shareCommon___redArg,
};
use crate::ffi::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_panic_fn_borrowed,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_expr_has_loose_bvar;
use crate::ffi::lean_sym_simp;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 105, 102, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 111, 110, 103, 114, 65, 114, 103, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,2642306550782628284 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 101, 102, 108, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [110, 100, 114, 101, 99, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [81, 117, 111, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,14456664134214385499 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 39, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__2_value) as *mut crate::leanh::LeanObject,2892992152676553881 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__5_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [113, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__0_value) as *mut crate::leanh::LeanObject,5289473232121221231 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [112, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__2_value) as *mut crate::leanh::LeanObject,9720699510028671266 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value:
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
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__1_value:
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
    m_data: [65, 114, 114, 111, 119, 0],
};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__1_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__1_value) as *mut crate::leanh::LeanObject,8546895479907627979 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [97, 114, 114, 111, 119, 95, 116, 114, 117, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__0_value) as *mut crate::leanh::LeanObject,11904470435052778522 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [97, 114, 114, 111, 119, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__2_value) as *mut crate::leanh::LeanObject,7230273742960147709 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [97, 114, 114, 111, 119, 95, 99, 111, 110, 103, 114, 95, 114, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__4_value) as *mut crate::leanh::LeanObject,7353248642434496285 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [97, 114, 114, 111, 119, 95, 99, 111, 110, 103, 114, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__6_value) as *mut crate::leanh::LeanObject,8814815876520233122 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 114, 114, 111, 119, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__8_value) as *mut crate::leanh::LeanObject,14857432921209711526 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 114, 117, 101, 95, 97, 114, 114, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__10_value) as *mut crate::leanh::LeanObject,15224384634218415015 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [116, 114, 117, 101, 95, 97, 114, 114, 111, 119, 95, 99, 111, 110, 103, 114, 95, 114, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__13_value) as *mut crate::leanh::LeanObject,6432741859769671798 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [116, 114, 117, 101, 95, 97, 114, 114, 111, 119, 95, 99, 111, 110, 103, 114, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__16_value) as *mut crate::leanh::LeanObject,2761443124418934022 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [116, 114, 117, 101, 95, 97, 114, 114, 111, 119, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__19_value) as *mut crate::leanh::LeanObject,13563566245290110437 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__22_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [102, 97, 108, 115, 101, 95, 97, 114, 114, 111, 119, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__22_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__22_value) as *mut crate::leanh::LeanObject,3101449391495309379 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__25_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [102, 97, 108, 115, 101, 95, 97, 114, 114, 111, 119, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__25_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__25_value) as *mut crate::leanh::LeanObject,2205725183007902457 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__0_value:
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
    m_data: [116, 114, 97, 110, 115, 0],
};
static mut l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17532416664988428445 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,13480818501600609864 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpArrow___closed__0_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
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
            105, 109, 112, 108, 105, 101, 115, 95, 99, 111, 110, 103, 114, 95, 114, 105, 103, 104,
            116, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpArrow___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3914459446195639943 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpArrow___closed__2_value: crate::leanh::LeanStringObject<32> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 65, 108, 112, 104, 97,
            83, 104, 97, 114, 101, 66, 117, 105, 108, 100, 101, 114, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpArrow___closed__3_value: crate::leanh::LeanStringObject<25> =
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
            76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 70, 111, 114,
            97, 108, 108, 83, 33, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpArrow___closed__4_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
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
            102, 111, 114, 97, 108, 108, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Simp_simpArrow___closed__6_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
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
            105, 109, 112, 108, 105, 101, 115, 95, 99, 111, 110, 103, 114, 95, 108, 101, 102, 116,
            0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpArrow___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__6_value)
                as *mut crate::leanh::LeanObject,
            8131708761548202259 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpArrow___closed__8_value: crate::leanh::LeanStringObject<14> =
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
            105, 109, 112, 108, 105, 101, 115, 95, 99, 111, 110, 103, 114, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpArrow___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__8_value)
                as *mut crate::leanh::LeanObject,
            11074994739801900941 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Simp_simpArrow___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpArrow___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpForall___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_Simp_simpArrow___boxed as *const core::ffi::c_void,
        m_arity: 11,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_simpForall___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpForall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Simp_simpForall___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_Simp_simp___boxed as *const core::ffi::c_void,
        m_arity: 11,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Simp_simpForall___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Simp_simpForall___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(
    mut v___x_2427_: *mut crate::leanh::LeanObject,
    mut v_a_2428_: *mut crate::leanh::LeanObject,
    mut v___x_2429_: *mut crate::leanh::LeanObject,
    mut v___x_2430_: *mut crate::leanh::LeanObject,
    mut v_xs_2431_: *mut crate::leanh::LeanObject,
    mut v___x_2432_: *mut crate::leanh::LeanObject,
    mut v_a_2433_: *mut crate::leanh::LeanObject,
    mut v___x_2434_: *mut crate::leanh::LeanObject,
    mut v_a_2435_: *mut crate::leanh::LeanObject,
    mut v___x_2436_: *mut crate::leanh::LeanObject,
    mut v___x_2437_: *mut crate::leanh::LeanObject,
    mut v_prop_2438_: *mut crate::leanh::LeanObject,
    mut v___x_2439_: u8,
    mut v___x_2440_: u8,
    mut v___x_2441_: u8,
    mut v___x_2442_: *mut crate::leanh::LeanObject,
    mut v_p_2443_: *mut crate::leanh::LeanObject,
    mut v_q_2444_: *mut crate::leanh::LeanObject,
    mut v_h_2445_: *mut crate::leanh::LeanObject,
    mut v___x_2446_: *mut crate::leanh::LeanObject,
    mut v___x_2447_: *mut crate::leanh::LeanObject,
    mut v___x_2448_: *mut crate::leanh::LeanObject,
    mut v___x_2449_: *mut crate::leanh::LeanObject,
    mut v___x_2450_: *mut crate::leanh::LeanObject,
    mut v___x_2451_: *mut crate::leanh::LeanObject,
    mut v_p_x27_2452_: *mut crate::leanh::LeanObject,
    mut v___y_2453_: *mut crate::leanh::LeanObject,
    mut v___y_2454_: *mut crate::leanh::LeanObject,
    mut v___y_2455_: *mut crate::leanh::LeanObject,
    mut v___y_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: u8 = 0;
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2458_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__0;
    crate::leanh::lean_inc_ref(v___x_2427_);
    v___x_2459_ = l_Lean_Name_mkStr2(v___x_2427_, v___x_2458_);
    crate::leanh::lean_inc(v___x_2429_);
    crate::leanh::lean_inc(v_a_2428_);
    v___x_2460_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2460_, 0, v_a_2428_);
    crate::leanh::lean_ctor_set(v___x_2460_, 1, v___x_2429_);
    v___x_2461_ = l_Lean_mkConst(v___x_2459_, v___x_2460_);
    v___x_2462_ = 0;
    v___x_2463_ = l_Lean_Expr_bvar___override(v___x_2430_);
    crate::leanh::lean_inc_ref(v___x_2463_);
    v___x_2464_ = l_Lean_mkAppN(v___x_2463_, v_xs_2431_);
    crate::leanh::lean_inc_ref(v___x_2464_);
    crate::leanh::lean_inc_ref_n(v_a_2433_, 4);
    crate::leanh::lean_inc(v___x_2432_);
    v___x_2465_ = l_Lean_mkLambda(v___x_2432_, v___x_2462_, v_a_2433_, v___x_2464_);
    crate::leanh::lean_inc(v___x_2434_);
    v___x_2466_ = l_Lean_Expr_bvar___override(v___x_2434_);
    crate::leanh::lean_inc_ref_n(v_a_2435_, 2);
    v___x_2467_ = l_Lean_mkAppB(v_a_2435_, v___x_2466_, v___x_2463_);
    v___x_2468_ = l_Lean_mkLambda(v___x_2436_, v___x_2462_, v___x_2467_, v___x_2464_);
    v___x_2469_ = l_Lean_mkLambda(v___x_2437_, v___x_2462_, v_a_2433_, v___x_2468_);
    v___x_2470_ = l_Lean_mkLambda(v___x_2432_, v___x_2462_, v_a_2433_, v___x_2469_);
    crate::leanh::lean_inc_ref(v_p_x27_2452_);
    crate::leanh::lean_inc_ref(v_prop_2438_);
    v___x_2471_ = l_Lean_mkApp6(
        v___x_2461_,
        v_a_2433_,
        v_a_2435_,
        v_prop_2438_,
        v___x_2465_,
        v___x_2470_,
        v_p_x27_2452_,
    );
    v___x_2472_ = lean_mk_empty_array_with_capacity(v___x_2434_);
    crate::leanh::lean_dec(v___x_2434_);
    crate::leanh::lean_inc_ref(v___x_2472_);
    v___x_2473_ = lean_array_push(v___x_2472_, v_p_x27_2452_);
    v___x_2474_ = l_Array_append___redArg(v___x_2473_, v_xs_2431_);
    v___x_2475_ = l_Lean_Meta_mkLambdaFVars(
        v___x_2474_,
        v___x_2471_,
        v___x_2439_,
        v___x_2440_,
        v___x_2439_,
        v___x_2440_,
        v___x_2441_,
        v___y_2453_,
        v___y_2454_,
        v___y_2455_,
        v___y_2456_,
    );
    crate::leanh::lean_dec_ref(v___x_2474_);
    if crate::leanh::lean_obj_tag(v___x_2475_) == 0 {
        let mut v_a_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2476_ = crate::leanh::lean_ctor_get(v___x_2475_, 0);
        crate::leanh::lean_inc(v_a_2476_);
        crate::leanh::lean_dec_ref_known(v___x_2475_, 1);
        v___x_2477_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__1;
        crate::leanh::lean_inc_ref(v___x_2427_);
        v___x_2478_ = l_Lean_Name_mkStr2(v___x_2427_, v___x_2477_);
        crate::leanh::lean_inc(v___x_2442_);
        v___x_2479_ = l_Lean_mkConst(v___x_2478_, v___x_2442_);
        crate::leanh::lean_inc_ref(v_h_2445_);
        crate::leanh::lean_inc_ref(v_q_2444_);
        crate::leanh::lean_inc_ref(v_p_2443_);
        crate::leanh::lean_inc_ref(v_a_2435_);
        crate::leanh::lean_inc_ref(v_a_2433_);
        v___x_2480_ = l_Lean_mkApp5(
            v___x_2479_,
            v_a_2433_,
            v_a_2435_,
            v_p_2443_,
            v_q_2444_,
            v_h_2445_,
        );
        v___x_2481_ = l_Lean_Meta_mkForallFVars(
            v_xs_2431_,
            v___x_2446_,
            v___x_2439_,
            v___x_2440_,
            v___x_2440_,
            v___x_2441_,
            v___y_2453_,
            v___y_2454_,
            v___y_2455_,
            v___y_2456_,
        );
        if crate::leanh::lean_obj_tag(v___x_2481_) == 0 {
            let mut v_a_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2482_ = crate::leanh::lean_ctor_get(v___x_2481_, 0);
            crate::leanh::lean_inc(v_a_2482_);
            crate::leanh::lean_dec_ref_known(v___x_2481_, 1);
            v___x_2483_ = l_Lean_Meta_mkForallFVars(
                v_xs_2431_,
                v___x_2447_,
                v___x_2439_,
                v___x_2440_,
                v___x_2440_,
                v___x_2441_,
                v___y_2453_,
                v___y_2454_,
                v___y_2455_,
                v___y_2456_,
            );
            if crate::leanh::lean_obj_tag(v___x_2483_) == 0 {
                let mut v_a_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_2484_ = crate::leanh::lean_ctor_get(v___x_2483_, 0);
                crate::leanh::lean_inc(v_a_2484_);
                crate::leanh::lean_dec_ref_known(v___x_2483_, 1);
                v___x_2485_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__2;
                v___x_2486_ = l_Lean_Name_mkStr2(v___x_2427_, v___x_2485_);
                crate::leanh::lean_inc(v___x_2442_);
                v___x_2487_ = l_Lean_mkConst(v___x_2486_, v___x_2442_);
                crate::leanh::lean_inc_ref(v_p_2443_);
                crate::leanh::lean_inc_ref(v_a_2435_);
                crate::leanh::lean_inc_ref_n(v_a_2433_, 2);
                crate::leanh::lean_inc_ref(v___x_2487_);
                v___x_2488_ = l_Lean_mkApp3(v___x_2487_, v_a_2433_, v_a_2435_, v_p_2443_);
                crate::leanh::lean_inc_ref_n(v_q_2444_, 2);
                v___x_2489_ = l_Lean_mkApp3(v___x_2487_, v_a_2433_, v_a_2435_, v_q_2444_);
                v___x_2490_ = lean_array_push(v___x_2472_, v_q_2444_);
                crate::leanh::lean_inc(v_a_2482_);
                crate::leanh::lean_inc_ref(v_prop_2438_);
                v___x_2491_ = l_Lean_mkApp3(v___x_2448_, v_prop_2438_, v_a_2482_, v_a_2484_);
                v___x_2492_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_2490_,
                    v___x_2491_,
                    v___x_2439_,
                    v___x_2440_,
                    v___x_2439_,
                    v___x_2440_,
                    v___x_2441_,
                    v___y_2453_,
                    v___y_2454_,
                    v___y_2455_,
                    v___y_2456_,
                );
                crate::leanh::lean_dec_ref(v___x_2490_);
                if crate::leanh::lean_obj_tag(v___x_2492_) == 0 {
                    let mut v_a_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_a_2493_ = crate::leanh::lean_ctor_get(v___x_2492_, 0);
                    crate::leanh::lean_inc(v_a_2493_);
                    crate::leanh::lean_dec_ref_known(v___x_2492_, 1);
                    v___x_2494_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__4;
                    crate::leanh::lean_inc(v___x_2442_);
                    v___x_2495_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2495_, 0, v_a_2428_);
                    crate::leanh::lean_ctor_set(v___x_2495_, 1, v___x_2442_);
                    v___x_2496_ = l_Lean_mkConst(v___x_2494_, v___x_2495_);
                    crate::leanh::lean_inc_ref(v_a_2433_);
                    v___x_2497_ = l_Lean_mkApp6(
                        v___x_2496_,
                        v___x_2449_,
                        v_a_2433_,
                        v___x_2488_,
                        v___x_2489_,
                        v_a_2476_,
                        v___x_2480_,
                    );
                    v___x_2498_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__5;
                    crate::leanh::lean_inc_ref(v___x_2450_);
                    v___x_2499_ = l_Lean_Name_mkStr2(v___x_2450_, v___x_2498_);
                    v___x_2500_ = l_Lean_mkConst(v___x_2499_, v___x_2429_);
                    v___x_2501_ = l_Lean_mkAppB(v___x_2500_, v_prop_2438_, v_a_2482_);
                    v___x_2502_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___closed__6;
                    v___x_2503_ = l_Lean_Name_mkStr2(v___x_2450_, v___x_2502_);
                    v___x_2504_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2504_, 0, v___x_2451_);
                    crate::leanh::lean_ctor_set(v___x_2504_, 1, v___x_2442_);
                    v___x_2505_ = l_Lean_mkConst(v___x_2503_, v___x_2504_);
                    crate::leanh::lean_inc_ref(v_q_2444_);
                    crate::leanh::lean_inc_ref(v_p_2443_);
                    v___x_2506_ = l_Lean_mkApp6(
                        v___x_2505_,
                        v_a_2433_,
                        v_p_2443_,
                        v_a_2493_,
                        v___x_2501_,
                        v_q_2444_,
                        v___x_2497_,
                    );
                    v___x_2507_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2508_ = lean_mk_empty_array_with_capacity(v___x_2507_);
                    v___x_2509_ = lean_array_push(v___x_2508_, v_p_2443_);
                    v___x_2510_ = lean_array_push(v___x_2509_, v_q_2444_);
                    v___x_2511_ = lean_array_push(v___x_2510_, v_h_2445_);
                    v___x_2512_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_2511_,
                        v___x_2506_,
                        v___x_2439_,
                        v___x_2440_,
                        v___x_2439_,
                        v___x_2440_,
                        v___x_2441_,
                        v___y_2453_,
                        v___y_2454_,
                        v___y_2455_,
                        v___y_2456_,
                    );
                    crate::leanh::lean_dec_ref(v___x_2511_);
                    return v___x_2512_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_2489_);
                    crate::leanh::lean_dec_ref(v___x_2488_);
                    crate::leanh::lean_dec(v_a_2482_);
                    crate::leanh::lean_dec_ref(v___x_2480_);
                    crate::leanh::lean_dec(v_a_2476_);
                    crate::leanh::lean_dec(v___x_2451_);
                    crate::leanh::lean_dec_ref(v___x_2450_);
                    crate::leanh::lean_dec_ref(v___x_2449_);
                    crate::leanh::lean_dec_ref(v_h_2445_);
                    crate::leanh::lean_dec_ref(v_q_2444_);
                    crate::leanh::lean_dec_ref(v_p_2443_);
                    crate::leanh::lean_dec(v___x_2442_);
                    crate::leanh::lean_dec_ref(v_prop_2438_);
                    crate::leanh::lean_dec_ref(v_a_2433_);
                    crate::leanh::lean_dec(v___x_2429_);
                    crate::leanh::lean_dec(v_a_2428_);
                    return v___x_2492_;
                }
            } else {
                crate::leanh::lean_dec(v_a_2482_);
                crate::leanh::lean_dec_ref(v___x_2480_);
                crate::leanh::lean_dec(v_a_2476_);
                crate::leanh::lean_dec_ref(v___x_2472_);
                crate::leanh::lean_dec(v___x_2451_);
                crate::leanh::lean_dec_ref(v___x_2450_);
                crate::leanh::lean_dec_ref(v___x_2449_);
                crate::leanh::lean_dec_ref(v___x_2448_);
                crate::leanh::lean_dec_ref(v_h_2445_);
                crate::leanh::lean_dec_ref(v_q_2444_);
                crate::leanh::lean_dec_ref(v_p_2443_);
                crate::leanh::lean_dec(v___x_2442_);
                crate::leanh::lean_dec_ref(v_prop_2438_);
                crate::leanh::lean_dec_ref(v_a_2435_);
                crate::leanh::lean_dec_ref(v_a_2433_);
                crate::leanh::lean_dec(v___x_2429_);
                crate::leanh::lean_dec(v_a_2428_);
                crate::leanh::lean_dec_ref(v___x_2427_);
                return v___x_2483_;
            }
        } else {
            crate::leanh::lean_dec_ref(v___x_2480_);
            crate::leanh::lean_dec(v_a_2476_);
            crate::leanh::lean_dec_ref(v___x_2472_);
            crate::leanh::lean_dec(v___x_2451_);
            crate::leanh::lean_dec_ref(v___x_2450_);
            crate::leanh::lean_dec_ref(v___x_2449_);
            crate::leanh::lean_dec_ref(v___x_2448_);
            crate::leanh::lean_dec_ref(v___x_2447_);
            crate::leanh::lean_dec_ref(v_h_2445_);
            crate::leanh::lean_dec_ref(v_q_2444_);
            crate::leanh::lean_dec_ref(v_p_2443_);
            crate::leanh::lean_dec(v___x_2442_);
            crate::leanh::lean_dec_ref(v_prop_2438_);
            crate::leanh::lean_dec_ref(v_a_2435_);
            crate::leanh::lean_dec_ref(v_a_2433_);
            crate::leanh::lean_dec(v___x_2429_);
            crate::leanh::lean_dec(v_a_2428_);
            crate::leanh::lean_dec_ref(v___x_2427_);
            return v___x_2481_;
        }
    } else {
        crate::leanh::lean_dec_ref(v___x_2472_);
        crate::leanh::lean_dec(v___x_2451_);
        crate::leanh::lean_dec_ref(v___x_2450_);
        crate::leanh::lean_dec_ref(v___x_2449_);
        crate::leanh::lean_dec_ref(v___x_2448_);
        crate::leanh::lean_dec_ref(v___x_2447_);
        crate::leanh::lean_dec_ref(v___x_2446_);
        crate::leanh::lean_dec_ref(v_h_2445_);
        crate::leanh::lean_dec_ref(v_q_2444_);
        crate::leanh::lean_dec_ref(v_p_2443_);
        crate::leanh::lean_dec(v___x_2442_);
        crate::leanh::lean_dec_ref(v_prop_2438_);
        crate::leanh::lean_dec_ref(v_a_2435_);
        crate::leanh::lean_dec_ref(v_a_2433_);
        crate::leanh::lean_dec(v___x_2429_);
        crate::leanh::lean_dec(v_a_2428_);
        crate::leanh::lean_dec_ref(v___x_2427_);
        return v___x_2475_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2513_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_2514_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2515_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2516_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_xs_2517_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2518_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_2519_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_2520_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_a_2521_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_2522_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_2523_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_prop_2524_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_2525_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_2526_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_2527_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_2528_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_p_2529_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_q_2530_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_h_2531_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_2532_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___x_2533_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___x_2534_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___x_2535_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___x_2536_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___x_2537_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v_p_x27_2538_: *mut crate::leanh::LeanObject = *_args.add(25);
    let mut v___y_2539_: *mut crate::leanh::LeanObject = *_args.add(26);
    let mut v___y_2540_: *mut crate::leanh::LeanObject = *_args.add(27);
    let mut v___y_2541_: *mut crate::leanh::LeanObject = *_args.add(28);
    let mut v___y_2542_: *mut crate::leanh::LeanObject = *_args.add(29);
    let mut v___y_2543_: *mut crate::leanh::LeanObject = *_args.add(30);
    let mut v___x_2437__boxed_2544_: u8 = 0;
    let mut v___x_2438__boxed_2545_: u8 = 0;
    let mut v___x_2439__boxed_2546_: u8 = 0;
    let mut v_res_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2437__boxed_2544_ = (crate::leanh::lean_unbox(v___x_2525_) as u8);
    v___x_2438__boxed_2545_ = (crate::leanh::lean_unbox(v___x_2526_) as u8);
    v___x_2439__boxed_2546_ = (crate::leanh::lean_unbox(v___x_2527_) as u8);
    v_res_2547_ =
        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0(
            v___x_2513_,
            v_a_2514_,
            v___x_2515_,
            v___x_2516_,
            v_xs_2517_,
            v___x_2518_,
            v_a_2519_,
            v___x_2520_,
            v_a_2521_,
            v___x_2522_,
            v___x_2523_,
            v_prop_2524_,
            v___x_2437__boxed_2544_,
            v___x_2438__boxed_2545_,
            v___x_2439__boxed_2546_,
            v___x_2528_,
            v_p_2529_,
            v_q_2530_,
            v_h_2531_,
            v___x_2532_,
            v___x_2533_,
            v___x_2534_,
            v___x_2535_,
            v___x_2536_,
            v___x_2537_,
            v_p_x27_2538_,
            v___y_2539_,
            v___y_2540_,
            v___y_2541_,
            v___y_2542_,
        );
    crate::leanh::lean_dec(v___y_2542_);
    crate::leanh::lean_dec_ref(v___y_2541_);
    crate::leanh::lean_dec(v___y_2540_);
    crate::leanh::lean_dec_ref(v___y_2539_);
    crate::leanh::lean_dec_ref(v_xs_2517_);
    return v_res_2547_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(
    mut v_k_2548_: *mut crate::leanh::LeanObject,
    mut v_b_2549_: *mut crate::leanh::LeanObject,
    mut v___y_2550_: *mut crate::leanh::LeanObject,
    mut v___y_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2553_);
    crate::leanh::lean_inc_ref(v___y_2552_);
    crate::leanh::lean_inc(v___y_2551_);
    crate::leanh::lean_inc_ref(v___y_2550_);
    v___x_2555_ = crate::leanh::lean_apply_6(
        v_k_2548_,
        v_b_2549_,
        v___y_2550_,
        v___y_2551_,
        v___y_2552_,
        v___y_2553_,
        crate::leanh::lean_box(0),
    );
    return v___x_2555_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_2556_: *mut crate::leanh::LeanObject,
    mut v_b_2557_: *mut crate::leanh::LeanObject,
    mut v___y_2558_: *mut crate::leanh::LeanObject,
    mut v___y_2559_: *mut crate::leanh::LeanObject,
    mut v___y_2560_: *mut crate::leanh::LeanObject,
    mut v___y_2561_: *mut crate::leanh::LeanObject,
    mut v___y_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2563_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0(v_k_2556_, v_b_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
    crate::leanh::lean_dec(v___y_2561_);
    crate::leanh::lean_dec_ref(v___y_2560_);
    crate::leanh::lean_dec(v___y_2559_);
    crate::leanh::lean_dec_ref(v___y_2558_);
    return v_res_2563_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(
    mut v_name_2564_: *mut crate::leanh::LeanObject,
    mut v_bi_2565_: u8,
    mut v_type_2566_: *mut crate::leanh::LeanObject,
    mut v_k_2567_: *mut crate::leanh::LeanObject,
    mut v_kind_2568_: u8,
    mut v___y_2569_: *mut crate::leanh::LeanObject,
    mut v___y_2570_: *mut crate::leanh::LeanObject,
    mut v___y_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2583_: u8 = 0;
    let mut v_a_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2587_: u8 = 0;
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2574_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_2574_, 0, v_k_2567_);
                v___x_2575_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_2564_,
                    v_bi_2565_,
                    v_type_2566_,
                    v___f_2574_,
                    v_kind_2568_,
                    v___y_2569_,
                    v___y_2570_,
                    v___y_2571_,
                    v___y_2572_,
                );
                if crate::leanh::lean_obj_tag(v___x_2575_) == 0 {
                    v_a_2576_ = crate::leanh::lean_ctor_get(v___x_2575_, 0);
                    v_isSharedCheck_2583_ = (!crate::leanh::lean_is_exclusive(v___x_2575_)) as u8;
                    if v_isSharedCheck_2583_ == 0 {
                        v___x_2578_ = v___x_2575_;
                        v_isShared_2579_ = v_isSharedCheck_2583_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2576_);
                        crate::leanh::lean_dec(v___x_2575_);
                        v___x_2578_ = crate::leanh::lean_box(0);
                        v_isShared_2579_ = v_isSharedCheck_2583_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2584_ = crate::leanh::lean_ctor_get(v___x_2575_, 0);
                    v_isSharedCheck_2591_ = (!crate::leanh::lean_is_exclusive(v___x_2575_)) as u8;
                    if v_isSharedCheck_2591_ == 0 {
                        v___x_2586_ = v___x_2575_;
                        v_isShared_2587_ = v_isSharedCheck_2591_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2584_);
                        crate::leanh::lean_dec(v___x_2575_);
                        v___x_2586_ = crate::leanh::lean_box(0);
                        v_isShared_2587_ = v_isSharedCheck_2591_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2579_ == 0 {
                    v___x_2581_ = v___x_2578_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2582_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
                    v___x_2581_ = v_reuseFailAlloc_2582_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2581_;
            }
            3 => {
                if v_isShared_2587_ == 0 {
                    v___x_2589_ = v___x_2586_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg___boxed(
    mut v_name_2592_: *mut crate::leanh::LeanObject,
    mut v_bi_2593_: *mut crate::leanh::LeanObject,
    mut v_type_2594_: *mut crate::leanh::LeanObject,
    mut v_k_2595_: *mut crate::leanh::LeanObject,
    mut v_kind_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
    mut v___y_2599_: *mut crate::leanh::LeanObject,
    mut v___y_2600_: *mut crate::leanh::LeanObject,
    mut v___y_2601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_2602_: u8 = 0;
    let mut v_kind_boxed_2603_: u8 = 0;
    let mut v_res_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2602_ = (crate::leanh::lean_unbox(v_bi_2593_) as u8);
    v_kind_boxed_2603_ = (crate::leanh::lean_unbox(v_kind_2596_) as u8);
    v_res_2604_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_2592_, v_bi_boxed_2602_, v_type_2594_, v_k_2595_, v_kind_boxed_2603_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
    crate::leanh::lean_dec(v___y_2600_);
    crate::leanh::lean_dec_ref(v___y_2599_);
    crate::leanh::lean_dec(v___y_2598_);
    crate::leanh::lean_dec_ref(v___y_2597_);
    return v_res_2604_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(
    mut v_name_2605_: *mut crate::leanh::LeanObject,
    mut v_type_2606_: *mut crate::leanh::LeanObject,
    mut v_k_2607_: *mut crate::leanh::LeanObject,
    mut v___y_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
    mut v___y_2610_: *mut crate::leanh::LeanObject,
    mut v___y_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2613_: u8 = 0;
    let mut v___x_2614_: u8 = 0;
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2613_ = 0;
    v___x_2614_ = 0;
    v___x_2615_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_2605_, v___x_2613_, v_type_2606_, v_k_2607_, v___x_2614_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
    return v___x_2615_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg___boxed(
    mut v_name_2616_: *mut crate::leanh::LeanObject,
    mut v_type_2617_: *mut crate::leanh::LeanObject,
    mut v_k_2618_: *mut crate::leanh::LeanObject,
    mut v___y_2619_: *mut crate::leanh::LeanObject,
    mut v___y_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
    mut v___y_2622_: *mut crate::leanh::LeanObject,
    mut v___y_2623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2624_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v_name_2616_, v_type_2617_, v_k_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
    crate::leanh::lean_dec(v___y_2622_);
    crate::leanh::lean_dec_ref(v___y_2621_);
    crate::leanh::lean_dec(v___y_2620_);
    crate::leanh::lean_dec_ref(v___y_2619_);
    return v_res_2624_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(
    mut v_xs_2631_: *mut crate::leanh::LeanObject,
    mut v___x_2632_: *mut crate::leanh::LeanObject,
    mut v___x_2633_: u8,
    mut v___x_2634_: u8,
    mut v___x_2635_: u8,
    mut v_p_2636_: *mut crate::leanh::LeanObject,
    mut v_q_2637_: *mut crate::leanh::LeanObject,
    mut v_a_2638_: *mut crate::leanh::LeanObject,
    mut v___x_2639_: *mut crate::leanh::LeanObject,
    mut v_a_2640_: *mut crate::leanh::LeanObject,
    mut v___x_2641_: *mut crate::leanh::LeanObject,
    mut v___x_2642_: *mut crate::leanh::LeanObject,
    mut v___x_2643_: *mut crate::leanh::LeanObject,
    mut v___x_2644_: *mut crate::leanh::LeanObject,
    mut v___x_2645_: *mut crate::leanh::LeanObject,
    mut v___x_2646_: *mut crate::leanh::LeanObject,
    mut v_prop_2647_: *mut crate::leanh::LeanObject,
    mut v___x_2648_: *mut crate::leanh::LeanObject,
    mut v___x_2649_: *mut crate::leanh::LeanObject,
    mut v___x_2650_: *mut crate::leanh::LeanObject,
    mut v___x_2651_: *mut crate::leanh::LeanObject,
    mut v___x_2652_: *mut crate::leanh::LeanObject,
    mut v_h_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
    mut v___y_2655_: *mut crate::leanh::LeanObject,
    mut v___y_2656_: *mut crate::leanh::LeanObject,
    mut v___y_2657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2659_ = l_Lean_Meta_mkForallFVars(
        v_xs_2631_,
        v___x_2632_,
        v___x_2633_,
        v___x_2634_,
        v___x_2634_,
        v___x_2635_,
        v___y_2654_,
        v___y_2655_,
        v___y_2656_,
        v___y_2657_,
    );
    if crate::leanh::lean_obj_tag(v___x_2659_) == 0 {
        let mut v_a_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2660_ = crate::leanh::lean_ctor_get(v___x_2659_, 0);
        crate::leanh::lean_inc(v_a_2660_);
        crate::leanh::lean_dec_ref_known(v___x_2659_, 1);
        v___x_2661_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_2662_ = lean_mk_empty_array_with_capacity(v___x_2661_);
        crate::leanh::lean_inc_ref(v_p_2636_);
        v___x_2663_ = lean_array_push(v___x_2662_, v_p_2636_);
        crate::leanh::lean_inc_ref(v_q_2637_);
        v___x_2664_ = lean_array_push(v___x_2663_, v_q_2637_);
        v___x_2665_ = l_Lean_Meta_mkLambdaFVars(
            v___x_2664_,
            v_a_2660_,
            v___x_2633_,
            v___x_2634_,
            v___x_2633_,
            v___x_2634_,
            v___x_2635_,
            v___y_2654_,
            v___y_2655_,
            v___y_2656_,
            v___y_2657_,
        );
        crate::leanh::lean_dec_ref(v___x_2664_);
        if crate::leanh::lean_obj_tag(v___x_2665_) == 0 {
            let mut v_a_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2666_ = crate::leanh::lean_ctor_get(v___x_2665_, 0);
            crate::leanh::lean_inc_n(v_a_2666_, 2);
            crate::leanh::lean_dec_ref_known(v___x_2665_, 1);
            v___x_2667_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__0;
            v___x_2668_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__1;
            crate::leanh::lean_inc(v_a_2638_);
            v___x_2669_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2669_, 0, v_a_2638_);
            crate::leanh::lean_ctor_set(v___x_2669_, 1, v___x_2639_);
            crate::leanh::lean_inc_ref(v___x_2669_);
            v___x_2670_ = l_Lean_mkConst(v___x_2668_, v___x_2669_);
            crate::leanh::lean_inc_ref(v_a_2640_);
            v___x_2671_ = l_Lean_mkAppB(v___x_2670_, v_a_2640_, v_a_2666_);
            v___x_2672_ = crate::leanh::lean_box((v___x_2633_) as usize);
            v___x_2673_ = crate::leanh::lean_box((v___x_2634_) as usize);
            v___x_2674_ = crate::leanh::lean_box((v___x_2635_) as usize);
            crate::leanh::lean_inc_ref(v___x_2671_);
            v___f_2675_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__0___boxed as *mut core::ffi::c_void, 31, 25);
            crate::leanh::lean_closure_set(v___f_2675_, 0, v___x_2667_);
            crate::leanh::lean_closure_set(v___f_2675_, 1, v_a_2638_);
            crate::leanh::lean_closure_set(v___f_2675_, 2, v___x_2641_);
            crate::leanh::lean_closure_set(v___f_2675_, 3, v___x_2642_);
            crate::leanh::lean_closure_set(v___f_2675_, 4, v_xs_2631_);
            crate::leanh::lean_closure_set(v___f_2675_, 5, v___x_2643_);
            crate::leanh::lean_closure_set(v___f_2675_, 6, v_a_2640_);
            crate::leanh::lean_closure_set(v___f_2675_, 7, v___x_2644_);
            crate::leanh::lean_closure_set(v___f_2675_, 8, v_a_2666_);
            crate::leanh::lean_closure_set(v___f_2675_, 9, v___x_2645_);
            crate::leanh::lean_closure_set(v___f_2675_, 10, v___x_2646_);
            crate::leanh::lean_closure_set(v___f_2675_, 11, v_prop_2647_);
            crate::leanh::lean_closure_set(v___f_2675_, 12, v___x_2672_);
            crate::leanh::lean_closure_set(v___f_2675_, 13, v___x_2673_);
            crate::leanh::lean_closure_set(v___f_2675_, 14, v___x_2674_);
            crate::leanh::lean_closure_set(v___f_2675_, 15, v___x_2669_);
            crate::leanh::lean_closure_set(v___f_2675_, 16, v_p_2636_);
            crate::leanh::lean_closure_set(v___f_2675_, 17, v_q_2637_);
            crate::leanh::lean_closure_set(v___f_2675_, 18, v_h_2653_);
            crate::leanh::lean_closure_set(v___f_2675_, 19, v___x_2648_);
            crate::leanh::lean_closure_set(v___f_2675_, 20, v___x_2649_);
            crate::leanh::lean_closure_set(v___f_2675_, 21, v___x_2650_);
            crate::leanh::lean_closure_set(v___f_2675_, 22, v___x_2671_);
            crate::leanh::lean_closure_set(v___f_2675_, 23, v___x_2651_);
            crate::leanh::lean_closure_set(v___f_2675_, 24, v___x_2652_);
            v___x_2676_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___closed__3;
            v___x_2677_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_2676_, v___x_2671_, v___f_2675_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
            return v___x_2677_;
        } else {
            crate::leanh::lean_dec_ref(v_h_2653_);
            crate::leanh::lean_dec(v___x_2652_);
            crate::leanh::lean_dec_ref(v___x_2651_);
            crate::leanh::lean_dec_ref(v___x_2650_);
            crate::leanh::lean_dec_ref(v___x_2649_);
            crate::leanh::lean_dec_ref(v___x_2648_);
            crate::leanh::lean_dec_ref(v_prop_2647_);
            crate::leanh::lean_dec(v___x_2646_);
            crate::leanh::lean_dec(v___x_2645_);
            crate::leanh::lean_dec(v___x_2644_);
            crate::leanh::lean_dec(v___x_2643_);
            crate::leanh::lean_dec(v___x_2642_);
            crate::leanh::lean_dec(v___x_2641_);
            crate::leanh::lean_dec_ref(v_a_2640_);
            crate::leanh::lean_dec(v___x_2639_);
            crate::leanh::lean_dec(v_a_2638_);
            crate::leanh::lean_dec_ref(v_q_2637_);
            crate::leanh::lean_dec_ref(v_p_2636_);
            crate::leanh::lean_dec_ref(v_xs_2631_);
            return v___x_2665_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_h_2653_);
        crate::leanh::lean_dec(v___x_2652_);
        crate::leanh::lean_dec_ref(v___x_2651_);
        crate::leanh::lean_dec_ref(v___x_2650_);
        crate::leanh::lean_dec_ref(v___x_2649_);
        crate::leanh::lean_dec_ref(v___x_2648_);
        crate::leanh::lean_dec_ref(v_prop_2647_);
        crate::leanh::lean_dec(v___x_2646_);
        crate::leanh::lean_dec(v___x_2645_);
        crate::leanh::lean_dec(v___x_2644_);
        crate::leanh::lean_dec(v___x_2643_);
        crate::leanh::lean_dec(v___x_2642_);
        crate::leanh::lean_dec(v___x_2641_);
        crate::leanh::lean_dec_ref(v_a_2640_);
        crate::leanh::lean_dec(v___x_2639_);
        crate::leanh::lean_dec(v_a_2638_);
        crate::leanh::lean_dec_ref(v_q_2637_);
        crate::leanh::lean_dec_ref(v_p_2636_);
        crate::leanh::lean_dec_ref(v_xs_2631_);
        return v___x_2659_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_xs_2678_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_2679_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_2680_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2681_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2682_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_p_2683_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_q_2684_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_2685_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_2686_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_2687_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_2688_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2689_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_2690_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_2691_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_2692_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_2693_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_prop_2694_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_2695_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_2696_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_2697_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___x_2698_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___x_2699_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_h_2700_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_2701_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___y_2702_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v___y_2703_: *mut crate::leanh::LeanObject = *_args.add(25);
    let mut v___y_2704_: *mut crate::leanh::LeanObject = *_args.add(26);
    let mut v___y_2705_: *mut crate::leanh::LeanObject = *_args.add(27);
    let mut v___x_2726__boxed_2706_: u8 = 0;
    let mut v___x_2727__boxed_2707_: u8 = 0;
    let mut v___x_2728__boxed_2708_: u8 = 0;
    let mut v_res_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2726__boxed_2706_ = (crate::leanh::lean_unbox(v___x_2680_) as u8);
    v___x_2727__boxed_2707_ = (crate::leanh::lean_unbox(v___x_2681_) as u8);
    v___x_2728__boxed_2708_ = (crate::leanh::lean_unbox(v___x_2682_) as u8);
    v_res_2709_ =
        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1(
            v_xs_2678_,
            v___x_2679_,
            v___x_2726__boxed_2706_,
            v___x_2727__boxed_2707_,
            v___x_2728__boxed_2708_,
            v_p_2683_,
            v_q_2684_,
            v_a_2685_,
            v___x_2686_,
            v_a_2687_,
            v___x_2688_,
            v___x_2689_,
            v___x_2690_,
            v___x_2691_,
            v___x_2692_,
            v___x_2693_,
            v_prop_2694_,
            v___x_2695_,
            v___x_2696_,
            v___x_2697_,
            v___x_2698_,
            v___x_2699_,
            v_h_2700_,
            v___y_2701_,
            v___y_2702_,
            v___y_2703_,
            v___y_2704_,
        );
    crate::leanh::lean_dec(v___y_2704_);
    crate::leanh::lean_dec_ref(v___y_2703_);
    crate::leanh::lean_dec(v___y_2702_);
    crate::leanh::lean_dec_ref(v___y_2701_);
    return v_res_2709_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2713_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2714_ = l_Lean_Level_ofNat(v___x_2713_);
    return v___x_2714_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2715_ = crate::leanh::lean_box(0);
    v___x_2716_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__2);
    v___x_2717_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2717_, 0, v___x_2716_);
    crate::leanh::lean_ctor_set(v___x_2717_, 1, v___x_2715_);
    return v___x_2717_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2718_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3);
    v___x_2719_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__1;
    v___x_2720_ = l_Lean_mkConst(v___x_2719_, v___x_2718_);
    return v___x_2720_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(
    mut v_p_2724_: *mut crate::leanh::LeanObject,
    mut v_xs_2725_: *mut crate::leanh::LeanObject,
    mut v_prop_2726_: *mut crate::leanh::LeanObject,
    mut v___x_2727_: u8,
    mut v___x_2728_: u8,
    mut v___x_2729_: u8,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
    mut v___x_2732_: *mut crate::leanh::LeanObject,
    mut v___x_2733_: *mut crate::leanh::LeanObject,
    mut v___x_2734_: *mut crate::leanh::LeanObject,
    mut v___x_2735_: *mut crate::leanh::LeanObject,
    mut v_q_2736_: *mut crate::leanh::LeanObject,
    mut v___y_2737_: *mut crate::leanh::LeanObject,
    mut v___y_2738_: *mut crate::leanh::LeanObject,
    mut v___y_2739_: *mut crate::leanh::LeanObject,
    mut v___y_2740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2742_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__0;
    v___x_2743_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2744_ = crate::leanh::lean_box(0);
    v___x_2745_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__3);
    v___x_2746_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__4);
    crate::leanh::lean_inc_ref(v_p_2724_);
    v___x_2747_ = l_Lean_mkAppN(v_p_2724_, v_xs_2725_);
    crate::leanh::lean_inc_ref(v_q_2736_);
    v___x_2748_ = l_Lean_mkAppN(v_q_2736_, v_xs_2725_);
    crate::leanh::lean_inc_ref(v___x_2748_);
    crate::leanh::lean_inc_ref(v___x_2747_);
    crate::leanh::lean_inc_ref(v_prop_2726_);
    v___x_2749_ = l_Lean_mkApp3(v___x_2746_, v_prop_2726_, v___x_2747_, v___x_2748_);
    crate::leanh::lean_inc_ref(v___x_2749_);
    v___x_2750_ = l_Lean_Meta_mkForallFVars(
        v_xs_2725_,
        v___x_2749_,
        v___x_2727_,
        v___x_2728_,
        v___x_2728_,
        v___x_2729_,
        v___y_2737_,
        v___y_2738_,
        v___y_2739_,
        v___y_2740_,
    );
    if crate::leanh::lean_obj_tag(v___x_2750_) == 0 {
        let mut v_a_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2751_ = crate::leanh::lean_ctor_get(v___x_2750_, 0);
        crate::leanh::lean_inc(v_a_2751_);
        crate::leanh::lean_dec_ref_known(v___x_2750_, 1);
        v___x_2752_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___closed__6;
        v___x_2753_ = crate::leanh::lean_box((v___x_2727_) as usize);
        v___x_2754_ = crate::leanh::lean_box((v___x_2728_) as usize);
        v___x_2755_ = crate::leanh::lean_box((v___x_2729_) as usize);
        v___f_2756_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__1___boxed as *mut core::ffi::c_void, 28, 22);
        crate::leanh::lean_closure_set(v___f_2756_, 0, v_xs_2725_);
        crate::leanh::lean_closure_set(v___f_2756_, 1, v___x_2749_);
        crate::leanh::lean_closure_set(v___f_2756_, 2, v___x_2753_);
        crate::leanh::lean_closure_set(v___f_2756_, 3, v___x_2754_);
        crate::leanh::lean_closure_set(v___f_2756_, 4, v___x_2755_);
        crate::leanh::lean_closure_set(v___f_2756_, 5, v_p_2724_);
        crate::leanh::lean_closure_set(v___f_2756_, 6, v_q_2736_);
        crate::leanh::lean_closure_set(v___f_2756_, 7, v_a_2730_);
        crate::leanh::lean_closure_set(v___f_2756_, 8, v___x_2744_);
        crate::leanh::lean_closure_set(v___f_2756_, 9, v_a_2731_);
        crate::leanh::lean_closure_set(v___f_2756_, 10, v___x_2745_);
        crate::leanh::lean_closure_set(v___f_2756_, 11, v___x_2732_);
        crate::leanh::lean_closure_set(v___f_2756_, 12, v___x_2733_);
        crate::leanh::lean_closure_set(v___f_2756_, 13, v___x_2743_);
        crate::leanh::lean_closure_set(v___f_2756_, 14, v___x_2752_);
        crate::leanh::lean_closure_set(v___f_2756_, 15, v___x_2734_);
        crate::leanh::lean_closure_set(v___f_2756_, 16, v_prop_2726_);
        crate::leanh::lean_closure_set(v___f_2756_, 17, v___x_2747_);
        crate::leanh::lean_closure_set(v___f_2756_, 18, v___x_2748_);
        crate::leanh::lean_closure_set(v___f_2756_, 19, v___x_2746_);
        crate::leanh::lean_closure_set(v___f_2756_, 20, v___x_2742_);
        crate::leanh::lean_closure_set(v___f_2756_, 21, v___x_2735_);
        v___x_2757_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_2752_, v_a_2751_, v___f_2756_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
        return v___x_2757_;
    } else {
        crate::leanh::lean_dec_ref(v___x_2749_);
        crate::leanh::lean_dec_ref(v___x_2748_);
        crate::leanh::lean_dec_ref(v___x_2747_);
        crate::leanh::lean_dec_ref(v_q_2736_);
        crate::leanh::lean_dec(v___x_2735_);
        crate::leanh::lean_dec(v___x_2734_);
        crate::leanh::lean_dec(v___x_2733_);
        crate::leanh::lean_dec(v___x_2732_);
        crate::leanh::lean_dec_ref(v_a_2731_);
        crate::leanh::lean_dec(v_a_2730_);
        crate::leanh::lean_dec_ref(v_prop_2726_);
        crate::leanh::lean_dec_ref(v_xs_2725_);
        crate::leanh::lean_dec_ref(v_p_2724_);
        return v___x_2750_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_2758_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_xs_2759_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_prop_2760_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_2761_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_2762_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_2763_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_2764_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_2765_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_2766_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_2767_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_2768_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_2769_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_q_2770_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2771_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2772_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2773_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2774_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_2775_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_2868__boxed_2776_: u8 = 0;
    let mut v___x_2869__boxed_2777_: u8 = 0;
    let mut v___x_2870__boxed_2778_: u8 = 0;
    let mut v_res_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2868__boxed_2776_ = (crate::leanh::lean_unbox(v___x_2761_) as u8);
    v___x_2869__boxed_2777_ = (crate::leanh::lean_unbox(v___x_2762_) as u8);
    v___x_2870__boxed_2778_ = (crate::leanh::lean_unbox(v___x_2763_) as u8);
    v_res_2779_ =
        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2(
            v_p_2758_,
            v_xs_2759_,
            v_prop_2760_,
            v___x_2868__boxed_2776_,
            v___x_2869__boxed_2777_,
            v___x_2870__boxed_2778_,
            v_a_2764_,
            v_a_2765_,
            v___x_2766_,
            v___x_2767_,
            v___x_2768_,
            v___x_2769_,
            v_q_2770_,
            v___y_2771_,
            v___y_2772_,
            v___y_2773_,
            v___y_2774_,
        );
    crate::leanh::lean_dec(v___y_2774_);
    crate::leanh::lean_dec_ref(v___y_2773_);
    crate::leanh::lean_dec(v___y_2772_);
    crate::leanh::lean_dec_ref(v___y_2771_);
    return v_res_2779_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(
    mut v_xs_2783_: *mut crate::leanh::LeanObject,
    mut v_prop_2784_: *mut crate::leanh::LeanObject,
    mut v___x_2785_: u8,
    mut v___x_2786_: u8,
    mut v___x_2787_: u8,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
    mut v_a_2789_: *mut crate::leanh::LeanObject,
    mut v___x_2790_: *mut crate::leanh::LeanObject,
    mut v___x_2791_: *mut crate::leanh::LeanObject,
    mut v___x_2792_: *mut crate::leanh::LeanObject,
    mut v_p_2793_: *mut crate::leanh::LeanObject,
    mut v___y_2794_: *mut crate::leanh::LeanObject,
    mut v___y_2795_: *mut crate::leanh::LeanObject,
    mut v___y_2796_: *mut crate::leanh::LeanObject,
    mut v___y_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2799_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___closed__1;
    v___x_2800_ = crate::leanh::lean_box((v___x_2785_) as usize);
    v___x_2801_ = crate::leanh::lean_box((v___x_2786_) as usize);
    v___x_2802_ = crate::leanh::lean_box((v___x_2787_) as usize);
    crate::leanh::lean_inc_ref(v_a_2789_);
    v___f_2803_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__2___boxed as *mut core::ffi::c_void, 18, 12);
    crate::leanh::lean_closure_set(v___f_2803_, 0, v_p_2793_);
    crate::leanh::lean_closure_set(v___f_2803_, 1, v_xs_2783_);
    crate::leanh::lean_closure_set(v___f_2803_, 2, v_prop_2784_);
    crate::leanh::lean_closure_set(v___f_2803_, 3, v___x_2800_);
    crate::leanh::lean_closure_set(v___f_2803_, 4, v___x_2801_);
    crate::leanh::lean_closure_set(v___f_2803_, 5, v___x_2802_);
    crate::leanh::lean_closure_set(v___f_2803_, 6, v_a_2788_);
    crate::leanh::lean_closure_set(v___f_2803_, 7, v_a_2789_);
    crate::leanh::lean_closure_set(v___f_2803_, 8, v___x_2790_);
    crate::leanh::lean_closure_set(v___f_2803_, 9, v___x_2791_);
    crate::leanh::lean_closure_set(v___f_2803_, 10, v___x_2799_);
    crate::leanh::lean_closure_set(v___f_2803_, 11, v___x_2792_);
    v___x_2804_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_2799_, v_a_2789_, v___f_2803_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
    return v___x_2804_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___boxed(
    mut v_xs_2805_: *mut crate::leanh::LeanObject,
    mut v_prop_2806_: *mut crate::leanh::LeanObject,
    mut v___x_2807_: *mut crate::leanh::LeanObject,
    mut v___x_2808_: *mut crate::leanh::LeanObject,
    mut v___x_2809_: *mut crate::leanh::LeanObject,
    mut v_a_2810_: *mut crate::leanh::LeanObject,
    mut v_a_2811_: *mut crate::leanh::LeanObject,
    mut v___x_2812_: *mut crate::leanh::LeanObject,
    mut v___x_2813_: *mut crate::leanh::LeanObject,
    mut v___x_2814_: *mut crate::leanh::LeanObject,
    mut v_p_2815_: *mut crate::leanh::LeanObject,
    mut v___y_2816_: *mut crate::leanh::LeanObject,
    mut v___y_2817_: *mut crate::leanh::LeanObject,
    mut v___y_2818_: *mut crate::leanh::LeanObject,
    mut v___y_2819_: *mut crate::leanh::LeanObject,
    mut v___y_2820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2963__boxed_2821_: u8 = 0;
    let mut v___x_2964__boxed_2822_: u8 = 0;
    let mut v___x_2965__boxed_2823_: u8 = 0;
    let mut v_res_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2963__boxed_2821_ = (crate::leanh::lean_unbox(v___x_2807_) as u8);
    v___x_2964__boxed_2822_ = (crate::leanh::lean_unbox(v___x_2808_) as u8);
    v___x_2965__boxed_2823_ = (crate::leanh::lean_unbox(v___x_2809_) as u8);
    v_res_2824_ =
        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3(
            v_xs_2805_,
            v_prop_2806_,
            v___x_2963__boxed_2821_,
            v___x_2964__boxed_2822_,
            v___x_2965__boxed_2823_,
            v_a_2810_,
            v_a_2811_,
            v___x_2812_,
            v___x_2813_,
            v___x_2814_,
            v_p_2815_,
            v___y_2816_,
            v___y_2817_,
            v___y_2818_,
            v___y_2819_,
        );
    crate::leanh::lean_dec(v___y_2819_);
    crate::leanh::lean_dec_ref(v___y_2818_);
    crate::leanh::lean_dec(v___y_2817_);
    crate::leanh::lean_dec_ref(v___y_2816_);
    return v_res_2824_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2825_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2826_ = l_Lean_Level_ofNat(v___x_2825_);
    return v___x_2826_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prop_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0);
    v_prop_2828_ = l_Lean_mkSort(v___x_2827_);
    return v_prop_2828_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(
    mut v_xs_2832_: *mut crate::leanh::LeanObject,
    mut v_a_2833_: *mut crate::leanh::LeanObject,
    mut v_a_2834_: *mut crate::leanh::LeanObject,
    mut v_a_2835_: *mut crate::leanh::LeanObject,
    mut v_a_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prop_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: u8 = 0;
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2857_: u8 = 0;
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2838_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2839_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__0);
                v_prop_2840_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__1);
                v___x_2841_ = 0;
                v___x_2842_ = 1;
                v___x_2843_ = 1;
                v___x_2844_ = l_Lean_Meta_mkForallFVars(
                    v_xs_2832_,
                    v_prop_2840_,
                    v___x_2841_,
                    v___x_2842_,
                    v___x_2842_,
                    v___x_2843_,
                    v_a_2833_,
                    v_a_2834_,
                    v_a_2835_,
                    v_a_2836_,
                );
                if crate::leanh::lean_obj_tag(v___x_2844_) == 0 {
                    v_a_2845_ = crate::leanh::lean_ctor_get(v___x_2844_, 0);
                    crate::leanh::lean_inc_n(v_a_2845_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2844_, 1);
                    v___x_2846_ =
                        l_Lean_Meta_getLevel(v_a_2845_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
                    if crate::leanh::lean_obj_tag(v___x_2846_) == 0 {
                        v_a_2847_ = crate::leanh::lean_ctor_get(v___x_2846_, 0);
                        crate::leanh::lean_inc(v_a_2847_);
                        crate::leanh::lean_dec_ref_known(v___x_2846_, 1);
                        v___x_2848_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___closed__3;
                        v___x_2849_ = crate::leanh::lean_box((v___x_2841_) as usize);
                        v___x_2850_ = crate::leanh::lean_box((v___x_2842_) as usize);
                        v___x_2851_ = crate::leanh::lean_box((v___x_2843_) as usize);
                        crate::leanh::lean_inc(v_a_2845_);
                        v___f_2852_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___lam__3___boxed as *mut core::ffi::c_void, 16, 10);
                        crate::leanh::lean_closure_set(v___f_2852_, 0, v_xs_2832_);
                        crate::leanh::lean_closure_set(v___f_2852_, 1, v_prop_2840_);
                        crate::leanh::lean_closure_set(v___f_2852_, 2, v___x_2849_);
                        crate::leanh::lean_closure_set(v___f_2852_, 3, v___x_2850_);
                        crate::leanh::lean_closure_set(v___f_2852_, 4, v___x_2851_);
                        crate::leanh::lean_closure_set(v___f_2852_, 5, v_a_2847_);
                        crate::leanh::lean_closure_set(v___f_2852_, 6, v_a_2845_);
                        crate::leanh::lean_closure_set(v___f_2852_, 7, v___x_2838_);
                        crate::leanh::lean_closure_set(v___f_2852_, 8, v___x_2848_);
                        crate::leanh::lean_closure_set(v___f_2852_, 9, v___x_2839_);
                        v___x_2853_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v___x_2848_, v_a_2845_, v___f_2852_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
                        return v___x_2853_;
                    } else {
                        crate::leanh::lean_dec(v_a_2845_);
                        crate::leanh::lean_dec_ref(v_xs_2832_);
                        v_a_2854_ = crate::leanh::lean_ctor_get(v___x_2846_, 0);
                        v_isSharedCheck_2861_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2846_)) as u8;
                        if v_isSharedCheck_2861_ == 0 {
                            v___x_2856_ = v___x_2846_;
                            v_isShared_2857_ = v_isSharedCheck_2861_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2854_);
                            crate::leanh::lean_dec(v___x_2846_);
                            v___x_2856_ = crate::leanh::lean_box(0);
                            v_isShared_2857_ = v_isSharedCheck_2861_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_xs_2832_);
                    return v___x_2844_;
                }
            }
            1 => {
                if v_isShared_2857_ == 0 {
                    v___x_2859_ = v___x_2856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
                    v___x_2859_ = v_reuseFailAlloc_2860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor___boxed(
    mut v_xs_2862_: *mut crate::leanh::LeanObject,
    mut v_a_2863_: *mut crate::leanh::LeanObject,
    mut v_a_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
    mut v_a_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2868_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(
        v_xs_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_,
    );
    crate::leanh::lean_dec(v_a_2866_);
    crate::leanh::lean_dec_ref(v_a_2865_);
    crate::leanh::lean_dec(v_a_2864_);
    crate::leanh::lean_dec_ref(v_a_2863_);
    return v_res_2868_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(
    mut v_00_u03b1_2869_: *mut crate::leanh::LeanObject,
    mut v_name_2870_: *mut crate::leanh::LeanObject,
    mut v_bi_2871_: u8,
    mut v_type_2872_: *mut crate::leanh::LeanObject,
    mut v_k_2873_: *mut crate::leanh::LeanObject,
    mut v_kind_2874_: u8,
    mut v___y_2875_: *mut crate::leanh::LeanObject,
    mut v___y_2876_: *mut crate::leanh::LeanObject,
    mut v___y_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2880_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___redArg(v_name_2870_, v_bi_2871_, v_type_2872_, v_k_2873_, v_kind_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
    return v___x_2880_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0___boxed(
    mut v_00_u03b1_2881_: *mut crate::leanh::LeanObject,
    mut v_name_2882_: *mut crate::leanh::LeanObject,
    mut v_bi_2883_: *mut crate::leanh::LeanObject,
    mut v_type_2884_: *mut crate::leanh::LeanObject,
    mut v_k_2885_: *mut crate::leanh::LeanObject,
    mut v_kind_2886_: *mut crate::leanh::LeanObject,
    mut v___y_2887_: *mut crate::leanh::LeanObject,
    mut v___y_2888_: *mut crate::leanh::LeanObject,
    mut v___y_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_2892_: u8 = 0;
    let mut v_kind_boxed_2893_: u8 = 0;
    let mut v_res_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2892_ = (crate::leanh::lean_unbox(v_bi_2883_) as u8);
    v_kind_boxed_2893_ = (crate::leanh::lean_unbox(v_kind_2886_) as u8);
    v_res_2894_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0_spec__0(v_00_u03b1_2881_, v_name_2882_, v_bi_boxed_2892_, v_type_2884_, v_k_2885_, v_kind_boxed_2893_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
    crate::leanh::lean_dec(v___y_2890_);
    crate::leanh::lean_dec_ref(v___y_2889_);
    crate::leanh::lean_dec(v___y_2888_);
    crate::leanh::lean_dec_ref(v___y_2887_);
    return v_res_2894_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(
    mut v_00_u03b1_2895_: *mut crate::leanh::LeanObject,
    mut v_name_2896_: *mut crate::leanh::LeanObject,
    mut v_type_2897_: *mut crate::leanh::LeanObject,
    mut v_k_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
    mut v___y_2902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2904_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___redArg(v_name_2896_, v_type_2897_, v_k_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_);
    return v___x_2904_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0___boxed(
    mut v_00_u03b1_2905_: *mut crate::leanh::LeanObject,
    mut v_name_2906_: *mut crate::leanh::LeanObject,
    mut v_type_2907_: *mut crate::leanh::LeanObject,
    mut v_k_2908_: *mut crate::leanh::LeanObject,
    mut v___y_2909_: *mut crate::leanh::LeanObject,
    mut v___y_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
    mut v___y_2912_: *mut crate::leanh::LeanObject,
    mut v___y_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2914_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor_spec__0(v_00_u03b1_2905_, v_name_2906_, v_type_2907_, v_k_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
    crate::leanh::lean_dec(v___y_2912_);
    crate::leanh::lean_dec_ref(v___y_2911_);
    crate::leanh::lean_dec(v___y_2910_);
    crate::leanh::lean_dec_ref(v___y_2909_);
    return v_res_2914_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(
    mut v_declName_2915_: *mut crate::leanh::LeanObject,
    mut v_us_2916_: *mut crate::leanh::LeanObject,
    mut v___y_2917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2919_ = l_Lean_Expr_const___override(v_declName_2915_, v_us_2916_);
    v___x_2920_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2919_, v___y_2917_);
    return v___x_2920_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg___boxed(
    mut v_declName_2921_: *mut crate::leanh::LeanObject,
    mut v_us_2922_: *mut crate::leanh::LeanObject,
    mut v___y_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2925_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v_declName_2921_, v_us_2922_, v___y_2923_);
    crate::leanh::lean_dec(v___y_2923_);
    return v_res_2925_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0(
    mut v_declName_2926_: *mut crate::leanh::LeanObject,
    mut v_us_2927_: *mut crate::leanh::LeanObject,
    mut v___y_2928_: *mut crate::leanh::LeanObject,
    mut v___y_2929_: *mut crate::leanh::LeanObject,
    mut v___y_2930_: *mut crate::leanh::LeanObject,
    mut v___y_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
    mut v___y_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2935_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v_declName_2926_, v_us_2927_, v___y_2929_);
    return v___x_2935_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___boxed(
    mut v_declName_2936_: *mut crate::leanh::LeanObject,
    mut v_us_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
    mut v___y_2940_: *mut crate::leanh::LeanObject,
    mut v___y_2941_: *mut crate::leanh::LeanObject,
    mut v___y_2942_: *mut crate::leanh::LeanObject,
    mut v___y_2943_: *mut crate::leanh::LeanObject,
    mut v___y_2944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2945_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0(v_declName_2936_, v_us_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
    crate::leanh::lean_dec(v___y_2943_);
    crate::leanh::lean_dec_ref(v___y_2942_);
    crate::leanh::lean_dec(v___y_2941_);
    crate::leanh::lean_dec_ref(v___y_2940_);
    crate::leanh::lean_dec(v___y_2939_);
    crate::leanh::lean_dec_ref(v___y_2938_);
    return v_res_2945_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(
    mut v_f_2946_: *mut crate::leanh::LeanObject,
    mut v_a_2947_: *mut crate::leanh::LeanObject,
    mut v___y_2948_: *mut crate::leanh::LeanObject,
    mut v___y_2949_: *mut crate::leanh::LeanObject,
    mut v___y_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
    mut v___y_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2960_: u8 = 0;
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2966_: u8 = 0;
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2970_: u8 = 0;
    let mut v_a_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2959_ = lean_st_ref_get(v___y_2949_);
                v_debug_2960_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2959_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_2959_);
                if v_debug_2960_ == 0 {
                    v___y_2956_ = v___y_2949_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_2946_);
                    v___x_2961_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_2946_,
                        v___y_2948_,
                        v___y_2949_,
                        v___y_2950_,
                        v___y_2951_,
                        v___y_2952_,
                        v___y_2953_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2961_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2961_, 1);
                        crate::leanh::lean_inc_ref(v_a_2947_);
                        v___x_2962_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_2947_,
                            v___y_2948_,
                            v___y_2949_,
                            v___y_2950_,
                            v___y_2951_,
                            v___y_2952_,
                            v___y_2953_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2962_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2962_, 1);
                            v___y_2956_ = v___y_2949_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_2947_);
                            crate::leanh::lean_dec_ref(v_f_2946_);
                            v_a_2963_ = crate::leanh::lean_ctor_get(v___x_2962_, 0);
                            v_isSharedCheck_2970_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2962_)) as u8;
                            if v_isSharedCheck_2970_ == 0 {
                                v___x_2965_ = v___x_2962_;
                                v_isShared_2966_ = v_isSharedCheck_2970_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2963_);
                                crate::leanh::lean_dec(v___x_2962_);
                                v___x_2965_ = crate::leanh::lean_box(0);
                                v_isShared_2966_ = v_isSharedCheck_2970_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_2947_);
                        crate::leanh::lean_dec_ref(v_f_2946_);
                        v_a_2971_ = crate::leanh::lean_ctor_get(v___x_2961_, 0);
                        v_isSharedCheck_2978_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2961_)) as u8;
                        if v_isSharedCheck_2978_ == 0 {
                            v___x_2973_ = v___x_2961_;
                            v_isShared_2974_ = v_isSharedCheck_2978_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2971_);
                            crate::leanh::lean_dec(v___x_2961_);
                            v___x_2973_ = crate::leanh::lean_box(0);
                            v_isShared_2974_ = v_isSharedCheck_2978_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2957_ = l_Lean_Expr_app___override(v_f_2946_, v_a_2947_);
                v___x_2958_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2957_, v___y_2956_);
                return v___x_2958_;
            }
            2 => {
                if v_isShared_2966_ == 0 {
                    v___x_2968_ = v___x_2965_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2969_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
                    v___x_2968_ = v_reuseFailAlloc_2969_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2968_;
            }
            4 => {
                if v_isShared_2974_ == 0 {
                    v___x_2976_ = v___x_2973_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
                    v___x_2976_ = v_reuseFailAlloc_2977_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1___boxed(
    mut v_f_2979_: *mut crate::leanh::LeanObject,
    mut v_a_2980_: *mut crate::leanh::LeanObject,
    mut v___y_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
    mut v___y_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
    mut v___y_2985_: *mut crate::leanh::LeanObject,
    mut v___y_2986_: *mut crate::leanh::LeanObject,
    mut v___y_2987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2988_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_f_2979_, v_a_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
    crate::leanh::lean_dec(v___y_2986_);
    crate::leanh::lean_dec_ref(v___y_2985_);
    crate::leanh::lean_dec(v___y_2984_);
    crate::leanh::lean_dec_ref(v___y_2983_);
    crate::leanh::lean_dec(v___y_2982_);
    crate::leanh::lean_dec_ref(v___y_2981_);
    return v_res_2988_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(
    mut v_f_2989_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_2990_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_2991_: *mut crate::leanh::LeanObject,
    mut v___y_2992_: *mut crate::leanh::LeanObject,
    mut v___y_2993_: *mut crate::leanh::LeanObject,
    mut v___y_2994_: *mut crate::leanh::LeanObject,
    mut v___y_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
    mut v___y_2997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2999_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_f_2989_, v_a_u2081_2990_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
    if crate::leanh::lean_obj_tag(v___x_2999_) == 0 {
        let mut v_a_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3000_ = crate::leanh::lean_ctor_get(v___x_2999_, 0);
        crate::leanh::lean_inc(v_a_3000_);
        crate::leanh::lean_dec_ref_known(v___x_2999_, 1);
        v___x_3001_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1_spec__1(v_a_3000_, v_a_u2082_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
        return v___x_3001_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2082_2991_);
        return v___x_2999_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1___boxed(
    mut v_f_3002_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_3003_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_3004_: *mut crate::leanh::LeanObject,
    mut v___y_3005_: *mut crate::leanh::LeanObject,
    mut v___y_3006_: *mut crate::leanh::LeanObject,
    mut v___y_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
    mut v___y_3009_: *mut crate::leanh::LeanObject,
    mut v___y_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3012_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(v_f_3002_, v_a_u2081_3003_, v_a_u2082_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
    crate::leanh::lean_dec(v___y_3010_);
    crate::leanh::lean_dec_ref(v___y_3009_);
    crate::leanh::lean_dec(v___y_3008_);
    crate::leanh::lean_dec_ref(v___y_3007_);
    crate::leanh::lean_dec(v___y_3006_);
    crate::leanh::lean_dec_ref(v___y_3005_);
    return v_res_3012_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(
    mut v_e_3018_: *mut crate::leanh::LeanObject,
    mut v_a_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
    mut v_a_3021_: *mut crate::leanh::LeanObject,
    mut v_a_3022_: *mut crate::leanh::LeanObject,
    mut v_a_3023_: *mut crate::leanh::LeanObject,
    mut v_a_3024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3036_: u8 = 0;
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut v_a_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_binderName_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3054_: u8 = 0;
    let mut v___x_3055_: u8 = 0;
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrow_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infos_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3063_: u8 = 0;
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3086_: u8 = 0;
    let mut v_a_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3090_: u8 = 0;
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3094_: u8 = 0;
    let mut v_a_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3098_: u8 = 0;
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut v_a_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3106_: u8 = 0;
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3110_: u8 = 0;
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_3018_) == 7 {
                    v_binderName_3051_ = crate::leanh::lean_ctor_get(v_e_3018_, 0);
                    v_binderType_3052_ = crate::leanh::lean_ctor_get(v_e_3018_, 1);
                    v_body_3053_ = crate::leanh::lean_ctor_get(v_e_3018_, 2);
                    v_binderInfo_3054_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_3018_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_3055_ = l_Lean_Expr_hasLooseBVars(v_body_3053_);
                    if v___x_3055_ == 0 {
                        crate::leanh::lean_inc_ref(v_body_3053_);
                        crate::leanh::lean_inc_ref(v_binderType_3052_);
                        crate::leanh::lean_inc(v_binderName_3051_);
                        crate::leanh::lean_dec_ref_known(v_e_3018_, 3);
                        v___x_3056_ =
                            l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(
                                v_body_3053_,
                                v_a_3019_,
                                v_a_3020_,
                                v_a_3021_,
                                v_a_3022_,
                                v_a_3023_,
                                v_a_3024_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_3056_) == 0 {
                            v_a_3057_ = crate::leanh::lean_ctor_get(v___x_3056_, 0);
                            crate::leanh::lean_inc(v_a_3057_);
                            crate::leanh::lean_dec_ref_known(v___x_3056_, 1);
                            v_arrow_3058_ = crate::leanh::lean_ctor_get(v_a_3057_, 0);
                            v_infos_3059_ = crate::leanh::lean_ctor_get(v_a_3057_, 1);
                            v_v_3060_ = crate::leanh::lean_ctor_get(v_a_3057_, 2);
                            v_isSharedCheck_3111_ =
                                (!crate::leanh::lean_is_exclusive(v_a_3057_)) as u8;
                            if v_isSharedCheck_3111_ == 0 {
                                v___x_3062_ = v_a_3057_;
                                v_isShared_3063_ = v_isSharedCheck_3111_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_v_3060_);
                                crate::leanh::lean_inc(v_infos_3059_);
                                crate::leanh::lean_inc(v_arrow_3058_);
                                crate::leanh::lean_dec(v_a_3057_);
                                v___x_3062_ = crate::leanh::lean_box(0);
                                v_isShared_3063_ = v_isSharedCheck_3111_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_binderType_3052_);
                            crate::leanh::lean_dec(v_binderName_3051_);
                            return v___x_3056_;
                        }
                    } else {
                        v___y_3027_ = v_a_3020_;
                        v___y_3028_ = v_a_3021_;
                        v___y_3029_ = v_a_3022_;
                        v___y_3030_ = v_a_3023_;
                        v___y_3031_ = v_a_3024_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_3027_ = v_a_3020_;
                    v___y_3028_ = v_a_3021_;
                    v___y_3029_ = v_a_3022_;
                    v___y_3030_ = v_a_3023_;
                    v___y_3031_ = v_a_3024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_e_3018_);
                v___x_3032_ = l_Lean_Meta_Sym_getLevel___redArg(
                    v_e_3018_,
                    v___y_3027_,
                    v___y_3028_,
                    v___y_3029_,
                    v___y_3030_,
                    v___y_3031_,
                );
                if crate::leanh::lean_obj_tag(v___x_3032_) == 0 {
                    v_a_3033_ = crate::leanh::lean_ctor_get(v___x_3032_, 0);
                    v_isSharedCheck_3042_ = (!crate::leanh::lean_is_exclusive(v___x_3032_)) as u8;
                    if v_isSharedCheck_3042_ == 0 {
                        v___x_3035_ = v___x_3032_;
                        v_isShared_3036_ = v_isSharedCheck_3042_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3033_);
                        crate::leanh::lean_dec(v___x_3032_);
                        v___x_3035_ = crate::leanh::lean_box(0);
                        v_isShared_3036_ = v_isSharedCheck_3042_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3018_);
                    v_a_3043_ = crate::leanh::lean_ctor_get(v___x_3032_, 0);
                    v_isSharedCheck_3050_ = (!crate::leanh::lean_is_exclusive(v___x_3032_)) as u8;
                    if v_isSharedCheck_3050_ == 0 {
                        v___x_3045_ = v___x_3032_;
                        v_isShared_3046_ = v_isSharedCheck_3050_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3043_);
                        crate::leanh::lean_dec(v___x_3032_);
                        v___x_3045_ = crate::leanh::lean_box(0);
                        v_isShared_3046_ = v_isSharedCheck_3050_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3037_ = crate::leanh::lean_box(0);
                v___x_3038_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3038_, 0, v_e_3018_);
                crate::leanh::lean_ctor_set(v___x_3038_, 1, v___x_3037_);
                crate::leanh::lean_ctor_set(v___x_3038_, 2, v_a_3033_);
                if v_isShared_3036_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3035_, 0, v___x_3038_);
                    v___x_3040_ = v___x_3035_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3038_);
                    v___x_3040_ = v_reuseFailAlloc_3041_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3040_;
            }
            4 => {
                if v_isShared_3046_ == 0 {
                    v___x_3048_ = v___x_3045_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
                    v___x_3048_ = v_reuseFailAlloc_3049_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3048_;
            }
            6 => {
                crate::leanh::lean_inc_ref(v_binderType_3052_);
                v___x_3064_ = l_Lean_Meta_Sym_getLevel___redArg(
                    v_binderType_3052_,
                    v_a_3020_,
                    v_a_3021_,
                    v_a_3022_,
                    v_a_3023_,
                    v_a_3024_,
                );
                if crate::leanh::lean_obj_tag(v___x_3064_) == 0 {
                    v_a_3065_ = crate::leanh::lean_ctor_get(v___x_3064_, 0);
                    crate::leanh::lean_inc_n(v_a_3065_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3064_, 1);
                    v___x_3066_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2;
                    v___x_3067_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_v_3060_);
                    v___x_3068_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3068_, 0, v_v_3060_);
                    crate::leanh::lean_ctor_set(v___x_3068_, 1, v___x_3067_);
                    v___x_3069_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v_a_3065_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 1, v___x_3068_);
                    v___x_3070_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__0___redArg(v___x_3066_, v___x_3069_, v_a_3020_);
                    if crate::leanh::lean_obj_tag(v___x_3070_) == 0 {
                        v_a_3071_ = crate::leanh::lean_ctor_get(v___x_3070_, 0);
                        crate::leanh::lean_inc(v_a_3071_);
                        crate::leanh::lean_dec_ref_known(v___x_3070_, 1);
                        v___x_3072_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow_spec__1(v_a_3071_, v_binderType_3052_, v_arrow_3058_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
                        if crate::leanh::lean_obj_tag(v___x_3072_) == 0 {
                            v_a_3073_ = crate::leanh::lean_ctor_get(v___x_3072_, 0);
                            v_isSharedCheck_3086_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3072_)) as u8;
                            if v_isSharedCheck_3086_ == 0 {
                                v___x_3075_ = v___x_3072_;
                                v_isShared_3076_ = v_isSharedCheck_3086_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3073_);
                                crate::leanh::lean_dec(v___x_3072_);
                                v___x_3075_ = crate::leanh::lean_box(0);
                                v_isShared_3076_ = v_isSharedCheck_3086_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3065_);
                            crate::leanh::lean_del_object(v___x_3062_);
                            crate::leanh::lean_dec(v_v_3060_);
                            crate::leanh::lean_dec(v_infos_3059_);
                            crate::leanh::lean_dec(v_binderName_3051_);
                            v_a_3087_ = crate::leanh::lean_ctor_get(v___x_3072_, 0);
                            v_isSharedCheck_3094_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3072_)) as u8;
                            if v_isSharedCheck_3094_ == 0 {
                                v___x_3089_ = v___x_3072_;
                                v_isShared_3090_ = v_isSharedCheck_3094_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3087_);
                                crate::leanh::lean_dec(v___x_3072_);
                                v___x_3089_ = crate::leanh::lean_box(0);
                                v_isShared_3090_ = v_isSharedCheck_3094_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3065_);
                        crate::leanh::lean_del_object(v___x_3062_);
                        crate::leanh::lean_dec(v_v_3060_);
                        crate::leanh::lean_dec(v_infos_3059_);
                        crate::leanh::lean_dec_ref(v_arrow_3058_);
                        crate::leanh::lean_dec_ref(v_binderType_3052_);
                        crate::leanh::lean_dec(v_binderName_3051_);
                        v_a_3095_ = crate::leanh::lean_ctor_get(v___x_3070_, 0);
                        v_isSharedCheck_3102_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3070_)) as u8;
                        if v_isSharedCheck_3102_ == 0 {
                            v___x_3097_ = v___x_3070_;
                            v_isShared_3098_ = v_isSharedCheck_3102_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3095_);
                            crate::leanh::lean_dec(v___x_3070_);
                            v___x_3097_ = crate::leanh::lean_box(0);
                            v_isShared_3098_ = v_isSharedCheck_3102_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3062_);
                    crate::leanh::lean_dec(v_v_3060_);
                    crate::leanh::lean_dec(v_infos_3059_);
                    crate::leanh::lean_dec_ref(v_arrow_3058_);
                    crate::leanh::lean_dec_ref(v_binderType_3052_);
                    crate::leanh::lean_dec(v_binderName_3051_);
                    v_a_3103_ = crate::leanh::lean_ctor_get(v___x_3064_, 0);
                    v_isSharedCheck_3110_ = (!crate::leanh::lean_is_exclusive(v___x_3064_)) as u8;
                    if v_isSharedCheck_3110_ == 0 {
                        v___x_3105_ = v___x_3064_;
                        v_isShared_3106_ = v_isSharedCheck_3110_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3103_);
                        crate::leanh::lean_dec(v___x_3064_);
                        v___x_3105_ = crate::leanh::lean_box(0);
                        v_isShared_3106_ = v_isSharedCheck_3110_;
                        state = 14;
                        continue;
                    }
                }
            }
            7 => {
                crate::leanh::lean_inc(v_v_3060_);
                crate::leanh::lean_inc(v_a_3065_);
                v___x_3077_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3077_, 0, v_binderName_3051_);
                crate::leanh::lean_ctor_set(v___x_3077_, 1, v_a_3065_);
                crate::leanh::lean_ctor_set(v___x_3077_, 2, v_v_3060_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3077_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_binderInfo_3054_,
                );
                v___x_3078_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3078_, 0, v___x_3077_);
                crate::leanh::lean_ctor_set(v___x_3078_, 1, v_infos_3059_);
                v___x_3079_ = l_Lean_mkLevelIMax_x27(v_a_3065_, v_v_3060_);
                if v_isShared_3063_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3062_, 2, v___x_3079_);
                    crate::leanh::lean_ctor_set(v___x_3062_, 1, v___x_3078_);
                    crate::leanh::lean_ctor_set(v___x_3062_, 0, v_a_3073_);
                    v___x_3081_ = v___x_3062_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_3078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 2, v___x_3079_);
                    v___x_3081_ = v_reuseFailAlloc_3085_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3076_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3075_, 0, v___x_3081_);
                    v___x_3083_ = v___x_3075_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3081_);
                    v___x_3083_ = v_reuseFailAlloc_3084_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3083_;
            }
            10 => {
                if v_isShared_3090_ == 0 {
                    v___x_3092_ = v___x_3089_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
                    v___x_3092_ = v_reuseFailAlloc_3093_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3092_;
            }
            12 => {
                if v_isShared_3098_ == 0 {
                    v___x_3100_ = v___x_3097_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
                    v___x_3100_ = v_reuseFailAlloc_3101_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3100_;
            }
            14 => {
                if v_isShared_3106_ == 0 {
                    v___x_3108_ = v___x_3105_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
                    v___x_3108_ = v_reuseFailAlloc_3109_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___boxed(
    mut v_e_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
    mut v_a_3114_: *mut crate::leanh::LeanObject,
    mut v_a_3115_: *mut crate::leanh::LeanObject,
    mut v_a_3116_: *mut crate::leanh::LeanObject,
    mut v_a_3117_: *mut crate::leanh::LeanObject,
    mut v_a_3118_: *mut crate::leanh::LeanObject,
    mut v_a_3119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3120_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(
        v_e_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_,
    );
    crate::leanh::lean_dec(v_a_3118_);
    crate::leanh::lean_dec_ref(v_a_3117_);
    crate::leanh::lean_dec(v_a_3116_);
    crate::leanh::lean_dec_ref(v_a_3115_);
    crate::leanh::lean_dec(v_a_3114_);
    crate::leanh::lean_dec_ref(v_a_3113_);
    return v_res_3120_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(
    mut v_x_3121_: *mut crate::leanh::LeanObject,
    mut v_bi_3122_: u8,
    mut v_t_3123_: *mut crate::leanh::LeanObject,
    mut v_b_3124_: *mut crate::leanh::LeanObject,
    mut v___y_3125_: *mut crate::leanh::LeanObject,
    mut v___y_3126_: *mut crate::leanh::LeanObject,
    mut v___y_3127_: *mut crate::leanh::LeanObject,
    mut v___y_3128_: *mut crate::leanh::LeanObject,
    mut v___y_3129_: *mut crate::leanh::LeanObject,
    mut v___y_3130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3137_: u8 = 0;
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3147_: u8 = 0;
    let mut v_a_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3151_: u8 = 0;
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3136_ = lean_st_ref_get(v___y_3126_);
                v_debug_3137_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3136_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_3136_);
                if v_debug_3137_ == 0 {
                    v___y_3133_ = v___y_3126_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_t_3123_);
                    v___x_3138_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_t_3123_,
                        v___y_3125_,
                        v___y_3126_,
                        v___y_3127_,
                        v___y_3128_,
                        v___y_3129_,
                        v___y_3130_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3138_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3138_, 1);
                        crate::leanh::lean_inc_ref(v_b_3124_);
                        v___x_3139_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_b_3124_,
                            v___y_3125_,
                            v___y_3126_,
                            v___y_3127_,
                            v___y_3128_,
                            v___y_3129_,
                            v___y_3130_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3139_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3139_, 1);
                            v___y_3133_ = v___y_3126_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_3124_);
                            crate::leanh::lean_dec_ref(v_t_3123_);
                            crate::leanh::lean_dec(v_x_3121_);
                            v_a_3140_ = crate::leanh::lean_ctor_get(v___x_3139_, 0);
                            v_isSharedCheck_3147_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3139_)) as u8;
                            if v_isSharedCheck_3147_ == 0 {
                                v___x_3142_ = v___x_3139_;
                                v_isShared_3143_ = v_isSharedCheck_3147_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3140_);
                                crate::leanh::lean_dec(v___x_3139_);
                                v___x_3142_ = crate::leanh::lean_box(0);
                                v_isShared_3143_ = v_isSharedCheck_3147_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3124_);
                        crate::leanh::lean_dec_ref(v_t_3123_);
                        crate::leanh::lean_dec(v_x_3121_);
                        v_a_3148_ = crate::leanh::lean_ctor_get(v___x_3138_, 0);
                        v_isSharedCheck_3155_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3138_)) as u8;
                        if v_isSharedCheck_3155_ == 0 {
                            v___x_3150_ = v___x_3138_;
                            v_isShared_3151_ = v_isSharedCheck_3155_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3148_);
                            crate::leanh::lean_dec(v___x_3138_);
                            v___x_3150_ = crate::leanh::lean_box(0);
                            v_isShared_3151_ = v_isSharedCheck_3155_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3134_ =
                    l_Lean_Expr_forallE___override(v_x_3121_, v_t_3123_, v_b_3124_, v_bi_3122_);
                v___x_3135_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3134_, v___y_3133_);
                return v___x_3135_;
            }
            2 => {
                if v_isShared_3143_ == 0 {
                    v___x_3145_ = v___x_3142_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
                    v___x_3145_ = v_reuseFailAlloc_3146_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3145_;
            }
            4 => {
                if v_isShared_3151_ == 0 {
                    v___x_3153_ = v___x_3150_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
                    v___x_3153_ = v_reuseFailAlloc_3154_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0___boxed(
    mut v_x_3156_: *mut crate::leanh::LeanObject,
    mut v_bi_3157_: *mut crate::leanh::LeanObject,
    mut v_t_3158_: *mut crate::leanh::LeanObject,
    mut v_b_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
    mut v___y_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3167_: u8 = 0;
    let mut v_res_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3167_ = (crate::leanh::lean_unbox(v_bi_3157_) as u8);
    v_res_3168_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(v_x_3156_, v_bi_boxed_3167_, v_t_3158_, v_b_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
    crate::leanh::lean_dec(v___y_3165_);
    crate::leanh::lean_dec_ref(v___y_3164_);
    crate::leanh::lean_dec(v___y_3163_);
    crate::leanh::lean_dec_ref(v___y_3162_);
    crate::leanh::lean_dec(v___y_3161_);
    crate::leanh::lean_dec_ref(v___y_3160_);
    return v_res_3168_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(
    mut v_e_3169_: *mut crate::leanh::LeanObject,
    mut v_infos_3170_: *mut crate::leanh::LeanObject,
    mut v_a_3171_: *mut crate::leanh::LeanObject,
    mut v_a_3172_: *mut crate::leanh::LeanObject,
    mut v_a_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
    mut v_a_3175_: *mut crate::leanh::LeanObject,
    mut v_a_3176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_infos_3170_) == 1 {
        let mut v_head_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderName_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3181_: u8 = 0;
        let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3183_: u8 = 0;
        v_head_3178_ = crate::leanh::lean_ctor_get(v_infos_3170_, 0);
        crate::leanh::lean_inc(v_head_3178_);
        v_tail_3179_ = crate::leanh::lean_ctor_get(v_infos_3170_, 1);
        crate::leanh::lean_inc(v_tail_3179_);
        crate::leanh::lean_dec_ref_known(v_infos_3170_, 2);
        v_binderName_3180_ = crate::leanh::lean_ctor_get(v_head_3178_, 0);
        crate::leanh::lean_inc(v_binderName_3180_);
        v_binderInfo_3181_ = crate::leanh::lean_ctor_get_uint8(
            v_head_3178_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        );
        crate::leanh::lean_dec(v_head_3178_);
        crate::leanh::lean_inc_ref(v_e_3169_);
        v___x_3182_ = l_Lean_Expr_cleanupAnnotations(v_e_3169_);
        v___x_3183_ = l_Lean_Expr_isApp(v___x_3182_);
        if v___x_3183_ == 0 {
            let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_3182_);
            crate::leanh::lean_dec(v_binderName_3180_);
            crate::leanh::lean_dec(v_tail_3179_);
            v___x_3184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_3184_, 0, v_e_3169_);
            return v___x_3184_;
        } else {
            let mut v_arg_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3187_: u8 = 0;
            v_arg_3185_ = crate::leanh::lean_ctor_get(v___x_3182_, 1);
            crate::leanh::lean_inc_ref(v_arg_3185_);
            v___x_3186_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3182_);
            v___x_3187_ = l_Lean_Expr_isApp(v___x_3186_);
            if v___x_3187_ == 0 {
                let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_3186_);
                crate::leanh::lean_dec_ref(v_arg_3185_);
                crate::leanh::lean_dec(v_binderName_3180_);
                crate::leanh::lean_dec(v_tail_3179_);
                v___x_3188_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3188_, 0, v_e_3169_);
                return v___x_3188_;
            } else {
                let mut v_arg_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3192_: u8 = 0;
                v_arg_3189_ = crate::leanh::lean_ctor_get(v___x_3186_, 1);
                crate::leanh::lean_inc_ref(v_arg_3189_);
                v___x_3190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3186_);
                v___x_3191_ =
                    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2;
                v___x_3192_ = l_Lean_Expr_isConstOf(v___x_3190_, v___x_3191_);
                crate::leanh::lean_dec_ref(v___x_3190_);
                if v___x_3192_ == 0 {
                    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_arg_3189_);
                    crate::leanh::lean_dec_ref(v_arg_3185_);
                    crate::leanh::lean_dec(v_binderName_3180_);
                    crate::leanh::lean_dec(v_tail_3179_);
                    v___x_3193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3193_, 0, v_e_3169_);
                    return v___x_3193_;
                } else {
                    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_e_3169_);
                    v___x_3194_ =
                        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(
                            v_arg_3185_,
                            v_tail_3179_,
                            v_a_3171_,
                            v_a_3172_,
                            v_a_3173_,
                            v_a_3174_,
                            v_a_3175_,
                            v_a_3176_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3194_) == 0 {
                        let mut v_a_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_a_3195_ = crate::leanh::lean_ctor_get(v___x_3194_, 0);
                        crate::leanh::lean_inc(v_a_3195_);
                        crate::leanh::lean_dec_ref_known(v___x_3194_, 1);
                        v___x_3196_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall_spec__0(v_binderName_3180_, v_binderInfo_3181_, v_arg_3189_, v_a_3195_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_);
                        return v___x_3196_;
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_3189_);
                        crate::leanh::lean_dec(v_binderName_3180_);
                        return v___x_3194_;
                    }
                }
            }
        }
    } else {
        let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_infos_3170_);
        v___x_3197_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3197_, 0, v_e_3169_);
        return v___x_3197_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall___boxed(
    mut v_e_3198_: *mut crate::leanh::LeanObject,
    mut v_infos_3199_: *mut crate::leanh::LeanObject,
    mut v_a_3200_: *mut crate::leanh::LeanObject,
    mut v_a_3201_: *mut crate::leanh::LeanObject,
    mut v_a_3202_: *mut crate::leanh::LeanObject,
    mut v_a_3203_: *mut crate::leanh::LeanObject,
    mut v_a_3204_: *mut crate::leanh::LeanObject,
    mut v_a_3205_: *mut crate::leanh::LeanObject,
    mut v_a_3206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3207_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(
        v_e_3198_,
        v_infos_3199_,
        v_a_3200_,
        v_a_3201_,
        v_a_3202_,
        v_a_3203_,
        v_a_3204_,
        v_a_3205_,
    );
    crate::leanh::lean_dec(v_a_3205_);
    crate::leanh::lean_dec_ref(v_a_3204_);
    crate::leanh::lean_dec(v_a_3203_);
    crate::leanh::lean_dec_ref(v_a_3202_);
    crate::leanh::lean_dec(v_a_3201_);
    crate::leanh::lean_dec_ref(v_a_3200_);
    return v_res_3207_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(
    mut v_head_3208_: *mut crate::leanh::LeanObject,
    mut v_00___3209_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_v_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: u8 = 0;
    v_v_3210_ = crate::leanh::lean_ctor_get(v_head_3208_, 2);
    v___x_3211_ = l_Lean_Level_isZero(v_v_3210_);
    return v___x_3211_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0___boxed(
    mut v_head_3212_: *mut crate::leanh::LeanObject,
    mut v_00___3213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3214_: u8 = 0;
    let mut v_r_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3214_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(
        v_head_3212_,
        v_00___3213_,
    );
    crate::leanh::lean_dec_ref(v_head_3212_);
    v_r_3215_ = crate::leanh::lean_box((v_res_3214_) as usize);
    return v_r_3215_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(
    mut v_f_3216_: *mut crate::leanh::LeanObject,
    mut v_a_3217_: *mut crate::leanh::LeanObject,
    mut v___y_3218_: *mut crate::leanh::LeanObject,
    mut v___y_3219_: *mut crate::leanh::LeanObject,
    mut v___y_3220_: *mut crate::leanh::LeanObject,
    mut v___y_3221_: *mut crate::leanh::LeanObject,
    mut v___y_3222_: *mut crate::leanh::LeanObject,
    mut v___y_3223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3230_: u8 = 0;
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3236_: u8 = 0;
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v_a_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3244_: u8 = 0;
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3229_ = lean_st_ref_get(v___y_3219_);
                v_debug_3230_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3229_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_3229_);
                if v_debug_3230_ == 0 {
                    v___y_3226_ = v___y_3219_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_3216_);
                    v___x_3231_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_3216_,
                        v___y_3218_,
                        v___y_3219_,
                        v___y_3220_,
                        v___y_3221_,
                        v___y_3222_,
                        v___y_3223_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3231_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3231_, 1);
                        crate::leanh::lean_inc_ref(v_a_3217_);
                        v___x_3232_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_3217_,
                            v___y_3218_,
                            v___y_3219_,
                            v___y_3220_,
                            v___y_3221_,
                            v___y_3222_,
                            v___y_3223_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3232_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3232_, 1);
                            v___y_3226_ = v___y_3219_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_3217_);
                            crate::leanh::lean_dec_ref(v_f_3216_);
                            v_a_3233_ = crate::leanh::lean_ctor_get(v___x_3232_, 0);
                            v_isSharedCheck_3240_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3232_)) as u8;
                            if v_isSharedCheck_3240_ == 0 {
                                v___x_3235_ = v___x_3232_;
                                v_isShared_3236_ = v_isSharedCheck_3240_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3233_);
                                crate::leanh::lean_dec(v___x_3232_);
                                v___x_3235_ = crate::leanh::lean_box(0);
                                v_isShared_3236_ = v_isSharedCheck_3240_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_3217_);
                        crate::leanh::lean_dec_ref(v_f_3216_);
                        v_a_3241_ = crate::leanh::lean_ctor_get(v___x_3231_, 0);
                        v_isSharedCheck_3248_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3231_)) as u8;
                        if v_isSharedCheck_3248_ == 0 {
                            v___x_3243_ = v___x_3231_;
                            v_isShared_3244_ = v_isSharedCheck_3248_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3241_);
                            crate::leanh::lean_dec(v___x_3231_);
                            v___x_3243_ = crate::leanh::lean_box(0);
                            v_isShared_3244_ = v_isSharedCheck_3248_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3227_ = l_Lean_Expr_app___override(v_f_3216_, v_a_3217_);
                v___x_3228_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3227_, v___y_3226_);
                return v___x_3228_;
            }
            2 => {
                if v_isShared_3236_ == 0 {
                    v___x_3238_ = v___x_3235_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
                    v___x_3238_ = v_reuseFailAlloc_3239_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3238_;
            }
            4 => {
                if v_isShared_3244_ == 0 {
                    v___x_3246_ = v___x_3243_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3247_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
                    v___x_3246_ = v_reuseFailAlloc_3247_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg___boxed(
    mut v_f_3249_: *mut crate::leanh::LeanObject,
    mut v_a_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
    mut v___y_3256_: *mut crate::leanh::LeanObject,
    mut v___y_3257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3258_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_3249_, v_a_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
    crate::leanh::lean_dec(v___y_3256_);
    crate::leanh::lean_dec_ref(v___y_3255_);
    crate::leanh::lean_dec(v___y_3254_);
    crate::leanh::lean_dec_ref(v___y_3253_);
    crate::leanh::lean_dec(v___y_3252_);
    crate::leanh::lean_dec_ref(v___y_3251_);
    return v_res_3258_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(
    mut v_f_3259_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_3260_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_3261_: *mut crate::leanh::LeanObject,
    mut v___y_3262_: *mut crate::leanh::LeanObject,
    mut v___y_3263_: *mut crate::leanh::LeanObject,
    mut v___y_3264_: *mut crate::leanh::LeanObject,
    mut v___y_3265_: *mut crate::leanh::LeanObject,
    mut v___y_3266_: *mut crate::leanh::LeanObject,
    mut v___y_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3272_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_3259_, v_a_u2081_3260_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
    if crate::leanh::lean_obj_tag(v___x_3272_) == 0 {
        let mut v_a_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3273_ = crate::leanh::lean_ctor_get(v___x_3272_, 0);
        crate::leanh::lean_inc(v_a_3273_);
        crate::leanh::lean_dec_ref_known(v___x_3272_, 1);
        v___x_3274_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_a_3273_, v_a_u2082_3261_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
        return v___x_3274_;
    } else {
        crate::leanh::lean_dec_ref(v_a_u2082_3261_);
        return v___x_3272_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0___boxed(
    mut v_f_3275_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_3276_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_3277_: *mut crate::leanh::LeanObject,
    mut v___y_3278_: *mut crate::leanh::LeanObject,
    mut v___y_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
    mut v___y_3283_: *mut crate::leanh::LeanObject,
    mut v___y_3284_: *mut crate::leanh::LeanObject,
    mut v___y_3285_: *mut crate::leanh::LeanObject,
    mut v___y_3286_: *mut crate::leanh::LeanObject,
    mut v___y_3287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3288_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v_f_3275_, v_a_u2081_3276_, v_a_u2082_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
    crate::leanh::lean_dec(v___y_3286_);
    crate::leanh::lean_dec_ref(v___y_3285_);
    crate::leanh::lean_dec(v___y_3284_);
    crate::leanh::lean_dec_ref(v___y_3283_);
    crate::leanh::lean_dec(v___y_3282_);
    crate::leanh::lean_dec_ref(v___y_3281_);
    crate::leanh::lean_dec(v___y_3280_);
    crate::leanh::lean_dec_ref(v___y_3279_);
    crate::leanh::lean_dec(v___y_3278_);
    return v_res_3288_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3313_ = crate::leanh::lean_box(0);
    v___x_3314_ =
        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__11;
    v___x_3315_ = l_Lean_mkConst(v___x_3314_, v___x_3313_);
    return v___x_3315_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = crate::leanh::lean_box(0);
    v___x_3321_ =
        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__14;
    v___x_3322_ = l_Lean_mkConst(v___x_3321_, v___x_3320_);
    return v___x_3322_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3327_ = crate::leanh::lean_box(0);
    v___x_3328_ =
        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__17;
    v___x_3329_ = l_Lean_mkConst(v___x_3328_, v___x_3327_);
    return v___x_3329_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3334_ = crate::leanh::lean_box(0);
    v___x_3335_ =
        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__20;
    v___x_3336_ = l_Lean_mkConst(v___x_3335_, v___x_3334_);
    return v___x_3336_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = crate::leanh::lean_box(0);
    v___x_3342_ =
        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__23;
    v___x_3343_ = l_Lean_mkConst(v___x_3342_, v___x_3341_);
    return v___x_3343_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3348_ = crate::leanh::lean_box(0);
    v___x_3349_ =
        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__26;
    v___x_3350_ = l_Lean_mkConst(v___x_3349_, v___x_3348_);
    return v___x_3350_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(
    mut v_e_3351_: *mut crate::leanh::LeanObject,
    mut v_infos_3352_: *mut crate::leanh::LeanObject,
    mut v_simpBody_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
    mut v_a_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
    mut v_a_3360_: *mut crate::leanh::LeanObject,
    mut v_a_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3378_: u8 = 0;
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v_a_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3387_: u8 = 0;
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3391_: u8 = 0;
    let mut v___y_3393_: u8 = 0;
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3399_: u8 = 0;
    let mut v___y_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3402_: u8 = 0;
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut v_a_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3419_: u8 = 0;
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3423_: u8 = 0;
    let mut v_head_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3429_: u8 = 0;
    let mut v___y_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3431_: u8 = 0;
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: u8 = 0;
    let mut v_arg_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: u8 = 0;
    let mut v_arg_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: u8 = 0;
    let mut v_proof_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3446_: u8 = 0;
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3451_: u8 = 0;
    let mut v_u_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3463_: u8 = 0;
    let mut v_a_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3471_: u8 = 0;
    let mut v___y_3473_: u8 = 0;
    let mut v___y_3474_: u8 = 0;
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3479_: u8 = 0;
    let mut v_u_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3491_: u8 = 0;
    let mut v_a_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3495_: u8 = 0;
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3499_: u8 = 0;
    let mut v___y_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3502_: u8 = 0;
    let mut v___y_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3505_: u8 = 0;
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3521_: u8 = 0;
    let mut v_a_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3525_: u8 = 0;
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut v___y_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3532_: u8 = 0;
    let mut v___y_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3535_: u8 = 0;
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3540_: u8 = 0;
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut v_a_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3555_: u8 = 0;
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: u8 = 0;
    let mut v___y_3563_: u8 = 0;
    let mut v___y_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3565_: u8 = 0;
    let mut v_contextDependent_3566_: u8 = 0;
    let mut v_proof_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3568_: u8 = 0;
    let mut v_proof_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3574_: u8 = 0;
    let mut v___y_3575_: u8 = 0;
    let mut v___y_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3578_: u8 = 0;
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3588_: u8 = 0;
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3592_: u8 = 0;
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3600_: u8 = 0;
    let mut v___y_3601_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3606_: u8 = 0;
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: u8 = 0;
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3612_: u8 = 0;
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3622_: u8 = 0;
    let mut v_unused_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3625_: u8 = 0;
    let mut v_a_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3633_: u8 = 0;
    let mut v___y_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3636_: u8 = 0;
    let mut v___y_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3639_: u8 = 0;
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v___x_3645_: u8 = 0;
    let mut v___x_3646_: u8 = 0;
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3656_: u8 = 0;
    let mut v_a_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3660_: u8 = 0;
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3664_: u8 = 0;
    let mut v___y_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3667_: u8 = 0;
    let mut v___y_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3670_: u8 = 0;
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3675_: u8 = 0;
    let mut v___x_3676_: u8 = 0;
    let mut v___x_3677_: u8 = 0;
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: u8 = 0;
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut v_a_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3691_: u8 = 0;
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut v___y_3697_: u8 = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: u8 = 0;
    let mut v_contextDependent_3706_: u8 = 0;
    let mut v_contextDependent_3707_: u8 = 0;
    let mut v___x_3708_: u8 = 0;
    let mut v___x_3709_: u8 = 0;
    let mut v_contextDependent_3710_: u8 = 0;
    let mut v_e_x27_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3713_: u8 = 0;
    let mut v___x_3714_: u8 = 0;
    let mut v_e_x27_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: u8 = 0;
    let mut v_contextDependent_3718_: u8 = 0;
    let mut v_e_x27_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3721_: u8 = 0;
    let mut v___x_3722_: u8 = 0;
    let mut v_e_x27_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: u8 = 0;
    let mut v_e_x27_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3728_: u8 = 0;
    let mut v_e_x27_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3731_: u8 = 0;
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: u8 = 0;
    let mut v___x_3735_: u8 = 0;
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: u8 = 0;
    let mut v_a_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3745_: u8 = 0;
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3749_: u8 = 0;
    let mut v_contextDependent_3750_: u8 = 0;
    let mut v_contextDependent_3751_: u8 = 0;
    let mut v_a_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3755_: u8 = 0;
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3759_: u8 = 0;
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: u8 = 0;
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: u8 = 0;
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v_contextDependent_3767_: u8 = 0;
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3772_: u8 = 0;
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: u8 = 0;
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3784_: u8 = 0;
    let mut v_a_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3788_: u8 = 0;
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3792_: u8 = 0;
    let mut v_proof_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3794_: u8 = 0;
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3802_: u8 = 0;
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: u8 = 0;
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3816_: u8 = 0;
    let mut v_a_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3820_: u8 = 0;
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3824_: u8 = 0;
    let mut v_isSharedCheck_3825_: u8 = 0;
    let mut v_unused_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3827_: u8 = 0;
    let mut v_unused_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3833_: u8 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut v_a_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3841_: u8 = 0;
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_infos_3352_) == 0 {
                    crate::leanh::lean_inc(v_a_3362_);
                    crate::leanh::lean_inc_ref(v_a_3361_);
                    crate::leanh::lean_inc(v_a_3360_);
                    crate::leanh::lean_inc_ref(v_a_3359_);
                    crate::leanh::lean_inc(v_a_3358_);
                    crate::leanh::lean_inc_ref(v_a_3357_);
                    crate::leanh::lean_inc(v_a_3356_);
                    crate::leanh::lean_inc_ref(v_a_3355_);
                    crate::leanh::lean_inc(v_a_3354_);
                    v___x_3406_ = crate::leanh::lean_apply_11(
                        v_simpBody_3353_,
                        v_e_3351_,
                        v_a_3354_,
                        v_a_3355_,
                        v_a_3356_,
                        v_a_3357_,
                        v_a_3358_,
                        v_a_3359_,
                        v_a_3360_,
                        v_a_3361_,
                        v_a_3362_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_3406_) == 0 {
                        v_a_3407_ = crate::leanh::lean_ctor_get(v___x_3406_, 0);
                        v_isSharedCheck_3415_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3406_)) as u8;
                        if v_isSharedCheck_3415_ == 0 {
                            v___x_3409_ = v___x_3406_;
                            v_isShared_3410_ = v_isSharedCheck_3415_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3407_);
                            crate::leanh::lean_dec(v___x_3406_);
                            v___x_3409_ = crate::leanh::lean_box(0);
                            v_isShared_3410_ = v_isSharedCheck_3415_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_3416_ = crate::leanh::lean_ctor_get(v___x_3406_, 0);
                        v_isSharedCheck_3423_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3406_)) as u8;
                        if v_isSharedCheck_3423_ == 0 {
                            v___x_3418_ = v___x_3406_;
                            v_isShared_3419_ = v_isSharedCheck_3423_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3416_);
                            crate::leanh::lean_dec(v___x_3406_);
                            v___x_3418_ = crate::leanh::lean_box(0);
                            v_isShared_3419_ = v_isSharedCheck_3423_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v_head_3424_ = crate::leanh::lean_ctor_get(v_infos_3352_, 0);
                    v_tail_3425_ = crate::leanh::lean_ctor_get(v_infos_3352_, 1);
                    crate::leanh::lean_inc_ref(v_e_3351_);
                    v___x_3436_ = l_Lean_Expr_cleanupAnnotations(v_e_3351_);
                    v___x_3437_ = l_Lean_Expr_isApp(v___x_3436_);
                    if v___x_3437_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3436_);
                        v___y_3365_ = v_a_3354_;
                        v___y_3366_ = v_a_3355_;
                        v___y_3367_ = v_a_3356_;
                        v___y_3368_ = v_a_3357_;
                        v___y_3369_ = v_a_3358_;
                        v___y_3370_ = v_a_3359_;
                        v___y_3371_ = v_a_3360_;
                        v___y_3372_ = v_a_3361_;
                        v___y_3373_ = v_a_3362_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_3438_ = crate::leanh::lean_ctor_get(v___x_3436_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3438_);
                        v___x_3439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3436_);
                        v___x_3440_ = l_Lean_Expr_isApp(v___x_3439_);
                        if v___x_3440_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3439_);
                            crate::leanh::lean_dec_ref(v_arg_3438_);
                            v___y_3365_ = v_a_3354_;
                            v___y_3366_ = v_a_3355_;
                            v___y_3367_ = v_a_3356_;
                            v___y_3368_ = v_a_3357_;
                            v___y_3369_ = v_a_3358_;
                            v___y_3370_ = v_a_3359_;
                            v___y_3371_ = v_a_3360_;
                            v___y_3372_ = v_a_3361_;
                            v___y_3373_ = v_a_3362_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_3441_ = crate::leanh::lean_ctor_get(v___x_3439_, 1);
                            crate::leanh::lean_inc_ref(v_arg_3441_);
                            v___x_3442_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3439_);
                            v___x_3560_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow___closed__2;
                            v___x_3561_ = l_Lean_Expr_isConstOf(v___x_3442_, v___x_3560_);
                            if v___x_3561_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3442_);
                                crate::leanh::lean_dec_ref(v_arg_3441_);
                                crate::leanh::lean_dec_ref(v_arg_3438_);
                                v___y_3365_ = v_a_3354_;
                                v___y_3366_ = v_a_3355_;
                                v___y_3367_ = v_a_3356_;
                                v___y_3368_ = v_a_3357_;
                                v___y_3369_ = v_a_3358_;
                                v___y_3370_ = v_a_3359_;
                                v___y_3371_ = v_a_3360_;
                                v___y_3372_ = v_a_3361_;
                                v___y_3373_ = v_a_3362_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_e_3351_);
                                crate::leanh::lean_inc(v_a_3362_);
                                crate::leanh::lean_inc_ref(v_a_3361_);
                                crate::leanh::lean_inc(v_a_3360_);
                                crate::leanh::lean_inc_ref(v_a_3359_);
                                crate::leanh::lean_inc(v_a_3358_);
                                crate::leanh::lean_inc_ref(v_a_3357_);
                                crate::leanh::lean_inc(v_a_3356_);
                                crate::leanh::lean_inc_ref(v_a_3355_);
                                crate::leanh::lean_inc(v_a_3354_);
                                crate::leanh::lean_inc_ref(v_arg_3441_);
                                v___x_3593_ = lean_sym_simp(
                                    v_arg_3441_,
                                    v_a_3354_,
                                    v_a_3355_,
                                    v_a_3356_,
                                    v_a_3357_,
                                    v_a_3358_,
                                    v_a_3359_,
                                    v_a_3360_,
                                    v_a_3361_,
                                    v_a_3362_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3593_) == 0 {
                                    v_a_3594_ = crate::leanh::lean_ctor_get(v___x_3593_, 0);
                                    crate::leanh::lean_inc(v_a_3594_);
                                    crate::leanh::lean_dec_ref_known(v___x_3593_, 1);
                                    v___x_3595_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(
                                        v_arg_3441_,
                                        v_a_3594_,
                                    );
                                    v___x_3596_ = l_Lean_Meta_Sym_isFalseExpr___redArg(
                                        v___x_3595_,
                                        v_a_3357_,
                                    );
                                    crate::leanh::lean_dec_ref(v___x_3595_);
                                    if crate::leanh::lean_obj_tag(v___x_3596_) == 0 {
                                        v_a_3597_ = crate::leanh::lean_ctor_get(v___x_3596_, 0);
                                        crate::leanh::lean_inc(v_a_3597_);
                                        crate::leanh::lean_dec_ref_known(v___x_3596_, 1);
                                        v___x_3760_ = (crate::leanh::lean_unbox(v_a_3597_) as u8);
                                        if v___x_3760_ == 0 {
                                            v___x_3761_ =
                                                (crate::leanh::lean_unbox(v_a_3597_) as u8);
                                            crate::leanh::lean_dec(v_a_3597_);
                                            v___y_3697_ = v___x_3761_;
                                            state = 54;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_3597_);
                                            v___x_3762_ = crate::leanh::lean_box(0);
                                            v___x_3763_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_3424_, v___x_3762_);
                                            if v___x_3763_ == 0 {
                                                v___y_3697_ = v___x_3763_;
                                                state = 54;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3442_);
                                                crate::leanh::lean_dec_ref(v_simpBody_3353_);
                                                v_isSharedCheck_3827_ =
                                                    (!crate::leanh::lean_is_exclusive(
                                                        v_infos_3352_,
                                                    ))
                                                        as u8;
                                                if v_isSharedCheck_3827_ == 0 {
                                                    v_unused_3828_ = crate::leanh::lean_ctor_get(
                                                        v_infos_3352_,
                                                        1,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_3828_);
                                                    v_unused_3829_ = crate::leanh::lean_ctor_get(
                                                        v_infos_3352_,
                                                        0,
                                                    );
                                                    crate::leanh::lean_dec(v_unused_3829_);
                                                    v___x_3765_ = v_infos_3352_;
                                                    v_isShared_3766_ = v_isSharedCheck_3827_;
                                                    state = 59;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v_infos_3352_);
                                                    v___x_3765_ = crate::leanh::lean_box(0);
                                                    v_isShared_3766_ = v_isSharedCheck_3827_;
                                                    state = 59;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_3594_);
                                        crate::leanh::lean_dec_ref(v___x_3442_);
                                        crate::leanh::lean_dec_ref(v_arg_3441_);
                                        crate::leanh::lean_dec_ref(v_arg_3438_);
                                        crate::leanh::lean_dec_ref_known(v_infos_3352_, 2);
                                        crate::leanh::lean_dec_ref(v_simpBody_3353_);
                                        v_a_3830_ = crate::leanh::lean_ctor_get(v___x_3596_, 0);
                                        v_isSharedCheck_3837_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3596_)) as u8;
                                        if v_isSharedCheck_3837_ == 0 {
                                            v___x_3832_ = v___x_3596_;
                                            v_isShared_3833_ = v_isSharedCheck_3837_;
                                            state = 72;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3830_);
                                            crate::leanh::lean_dec(v___x_3596_);
                                            v___x_3832_ = crate::leanh::lean_box(0);
                                            v_isShared_3833_ = v_isSharedCheck_3837_;
                                            state = 72;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3442_);
                                    crate::leanh::lean_dec_ref(v_arg_3441_);
                                    crate::leanh::lean_dec_ref(v_arg_3438_);
                                    crate::leanh::lean_dec_ref_known(v_infos_3352_, 2);
                                    crate::leanh::lean_dec_ref(v_simpBody_3353_);
                                    v_a_3838_ = crate::leanh::lean_ctor_get(v___x_3593_, 0);
                                    v_isSharedCheck_3845_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3593_)) as u8;
                                    if v_isSharedCheck_3845_ == 0 {
                                        v___x_3840_ = v___x_3593_;
                                        v_isShared_3841_ = v_isSharedCheck_3845_;
                                        state = 74;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3838_);
                                        crate::leanh::lean_dec(v___x_3593_);
                                        v___x_3840_ = crate::leanh::lean_box(0);
                                        v_isShared_3841_ = v_isSharedCheck_3845_;
                                        state = 74;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_3373_);
                crate::leanh::lean_inc_ref(v___y_3372_);
                crate::leanh::lean_inc(v___y_3371_);
                crate::leanh::lean_inc_ref(v___y_3370_);
                crate::leanh::lean_inc(v___y_3369_);
                crate::leanh::lean_inc_ref(v___y_3368_);
                crate::leanh::lean_inc(v___y_3367_);
                crate::leanh::lean_inc_ref(v___y_3366_);
                crate::leanh::lean_inc(v___y_3365_);
                v___x_3374_ = crate::leanh::lean_apply_11(
                    v_simpBody_3353_,
                    v_e_3351_,
                    v___y_3365_,
                    v___y_3366_,
                    v___y_3367_,
                    v___y_3368_,
                    v___y_3369_,
                    v___y_3370_,
                    v___y_3371_,
                    v___y_3372_,
                    v___y_3373_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3374_) == 0 {
                    v_a_3375_ = crate::leanh::lean_ctor_get(v___x_3374_, 0);
                    v_isSharedCheck_3383_ = (!crate::leanh::lean_is_exclusive(v___x_3374_)) as u8;
                    if v_isSharedCheck_3383_ == 0 {
                        v___x_3377_ = v___x_3374_;
                        v_isShared_3378_ = v_isSharedCheck_3383_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3375_);
                        crate::leanh::lean_dec(v___x_3374_);
                        v___x_3377_ = crate::leanh::lean_box(0);
                        v_isShared_3378_ = v_isSharedCheck_3383_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_infos_3352_);
                    v_a_3384_ = crate::leanh::lean_ctor_get(v___x_3374_, 0);
                    v_isSharedCheck_3391_ = (!crate::leanh::lean_is_exclusive(v___x_3374_)) as u8;
                    if v_isSharedCheck_3391_ == 0 {
                        v___x_3386_ = v___x_3374_;
                        v_isShared_3387_ = v_isSharedCheck_3391_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3384_);
                        crate::leanh::lean_dec(v___x_3374_);
                        v___x_3386_ = crate::leanh::lean_box(0);
                        v_isShared_3387_ = v_isSharedCheck_3391_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3379_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3379_, 0, v_a_3375_);
                crate::leanh::lean_ctor_set(v___x_3379_, 1, v_infos_3352_);
                if v_isShared_3378_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3377_, 0, v___x_3379_);
                    v___x_3381_ = v___x_3377_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
                    v___x_3381_ = v_reuseFailAlloc_3382_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3381_;
            }
            4 => {
                if v_isShared_3387_ == 0 {
                    v___x_3389_ = v___x_3386_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
                    v___x_3389_ = v_reuseFailAlloc_3390_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3389_;
            }
            6 => {
                v___x_3394_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_3393_);
                v___x_3395_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3395_, 0, v___x_3394_);
                crate::leanh::lean_ctor_set(v___x_3395_, 1, v_infos_3352_);
                v___x_3396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3396_, 0, v___x_3395_);
                return v___x_3396_;
            }
            7 => {
                v___x_3403_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3403_, 0, v___y_3400_);
                crate::leanh::lean_ctor_set(v___x_3403_, 1, v___y_3401_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3403_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_3399_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3403_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_3402_,
                );
                v___x_3404_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3404_, 0, v___x_3403_);
                crate::leanh::lean_ctor_set(v___x_3404_, 1, v___y_3398_);
                v___x_3405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3405_, 0, v___x_3404_);
                return v___x_3405_;
            }
            8 => {
                v___x_3411_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3411_, 0, v_a_3407_);
                crate::leanh::lean_ctor_set(v___x_3411_, 1, v_infos_3352_);
                if v_isShared_3410_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3409_, 0, v___x_3411_);
                    v___x_3413_ = v___x_3409_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3414_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
                    v___x_3413_ = v_reuseFailAlloc_3414_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3413_;
            }
            10 => {
                if v_isShared_3419_ == 0 {
                    v___x_3421_ = v___x_3418_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3422_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
                    v___x_3421_ = v_reuseFailAlloc_3422_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3421_;
            }
            12 => {
                v___x_3432_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3432_, 0, v___y_3430_);
                crate::leanh::lean_ctor_set(v___x_3432_, 1, v___y_3427_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3432_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_3429_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3432_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_3431_,
                );
                v___x_3433_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3433_, 0, v_head_3424_);
                crate::leanh::lean_ctor_set(v___x_3433_, 1, v___y_3428_);
                v___x_3434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3434_, 0, v___x_3432_);
                crate::leanh::lean_ctor_set(v___x_3434_, 1, v___x_3433_);
                v___x_3435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3435_, 0, v___x_3434_);
                return v___x_3435_;
            }
            13 => {
                v___x_3447_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3357_);
                if crate::leanh::lean_obj_tag(v___x_3447_) == 0 {
                    v_a_3448_ = crate::leanh::lean_ctor_get(v___x_3447_, 0);
                    v_isSharedCheck_3463_ = (!crate::leanh::lean_is_exclusive(v___x_3447_)) as u8;
                    if v_isSharedCheck_3463_ == 0 {
                        v___x_3450_ = v___x_3447_;
                        v_isShared_3451_ = v_isSharedCheck_3463_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3448_);
                        crate::leanh::lean_dec(v___x_3447_);
                        v___x_3450_ = crate::leanh::lean_box(0);
                        v_isShared_3451_ = v_isSharedCheck_3463_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_proof_3445_);
                    crate::leanh::lean_dec_ref(v_arg_3441_);
                    crate::leanh::lean_dec_ref(v_arg_3438_);
                    crate::leanh::lean_dec(v_head_3424_);
                    v_a_3464_ = crate::leanh::lean_ctor_get(v___x_3447_, 0);
                    v_isSharedCheck_3471_ = (!crate::leanh::lean_is_exclusive(v___x_3447_)) as u8;
                    if v_isSharedCheck_3471_ == 0 {
                        v___x_3466_ = v___x_3447_;
                        v_isShared_3467_ = v_isSharedCheck_3471_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3464_);
                        crate::leanh::lean_dec(v___x_3447_);
                        v___x_3466_ = crate::leanh::lean_box(0);
                        v_isShared_3467_ = v_isSharedCheck_3471_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                v_u_3452_ = crate::leanh::lean_ctor_get(v_head_3424_, 1);
                crate::leanh::lean_inc(v_u_3452_);
                crate::leanh::lean_dec(v_head_3424_);
                v___x_3453_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__1;
                v___x_3454_ = crate::leanh::lean_box(0);
                v___x_3455_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3455_, 0, v_u_3452_);
                crate::leanh::lean_ctor_set(v___x_3455_, 1, v___x_3454_);
                v___x_3456_ = l_Lean_mkConst(v___x_3453_, v___x_3455_);
                v___x_3457_ = l_Lean_mkApp3(v___x_3456_, v_arg_3441_, v_arg_3438_, v_proof_3445_);
                v___x_3458_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3458_, 0, v_a_3448_);
                crate::leanh::lean_ctor_set(v___x_3458_, 1, v___x_3457_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3458_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_3444_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3458_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_3446_,
                );
                v___x_3459_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3459_, 0, v___x_3458_);
                crate::leanh::lean_ctor_set(v___x_3459_, 1, v___x_3454_);
                if v_isShared_3451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3450_, 0, v___x_3459_);
                    v___x_3461_ = v___x_3450_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3462_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
                    v___x_3461_ = v_reuseFailAlloc_3462_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3461_;
            }
            16 => {
                if v_isShared_3467_ == 0 {
                    v___x_3469_ = v___x_3466_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3470_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
                    v___x_3469_ = v_reuseFailAlloc_3470_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3469_;
            }
            18 => {
                v___x_3475_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3357_);
                if crate::leanh::lean_obj_tag(v___x_3475_) == 0 {
                    v_a_3476_ = crate::leanh::lean_ctor_get(v___x_3475_, 0);
                    v_isSharedCheck_3491_ = (!crate::leanh::lean_is_exclusive(v___x_3475_)) as u8;
                    if v_isSharedCheck_3491_ == 0 {
                        v___x_3478_ = v___x_3475_;
                        v_isShared_3479_ = v_isSharedCheck_3491_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3476_);
                        crate::leanh::lean_dec(v___x_3475_);
                        v___x_3478_ = crate::leanh::lean_box(0);
                        v_isShared_3479_ = v_isSharedCheck_3491_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_3441_);
                    crate::leanh::lean_dec(v_head_3424_);
                    v_a_3492_ = crate::leanh::lean_ctor_get(v___x_3475_, 0);
                    v_isSharedCheck_3499_ = (!crate::leanh::lean_is_exclusive(v___x_3475_)) as u8;
                    if v_isSharedCheck_3499_ == 0 {
                        v___x_3494_ = v___x_3475_;
                        v_isShared_3495_ = v_isSharedCheck_3499_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3492_);
                        crate::leanh::lean_dec(v___x_3475_);
                        v___x_3494_ = crate::leanh::lean_box(0);
                        v_isShared_3495_ = v_isSharedCheck_3499_;
                        state = 21;
                        continue;
                    }
                }
            }
            19 => {
                v_u_3480_ = crate::leanh::lean_ctor_get(v_head_3424_, 1);
                crate::leanh::lean_inc(v_u_3480_);
                crate::leanh::lean_dec(v_head_3424_);
                v___x_3481_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__3;
                v___x_3482_ = crate::leanh::lean_box(0);
                v___x_3483_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3483_, 0, v_u_3480_);
                crate::leanh::lean_ctor_set(v___x_3483_, 1, v___x_3482_);
                v___x_3484_ = l_Lean_mkConst(v___x_3481_, v___x_3483_);
                v___x_3485_ = l_Lean_Expr_app___override(v___x_3484_, v_arg_3441_);
                v___x_3486_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3486_, 0, v_a_3476_);
                crate::leanh::lean_ctor_set(v___x_3486_, 1, v___x_3485_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3486_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_3473_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3486_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_3474_,
                );
                v___x_3487_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3487_, 0, v___x_3486_);
                crate::leanh::lean_ctor_set(v___x_3487_, 1, v___x_3482_);
                if v_isShared_3479_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3478_, 0, v___x_3487_);
                    v___x_3489_ = v___x_3478_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3490_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
                    v___x_3489_ = v_reuseFailAlloc_3490_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3489_;
            }
            21 => {
                if v_isShared_3495_ == 0 {
                    v___x_3497_ = v___x_3494_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3498_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
                    v___x_3497_ = v_reuseFailAlloc_3498_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3497_;
            }
            23 => {
                crate::leanh::lean_inc_ref(v___y_3504_);
                crate::leanh::lean_inc_ref(v_arg_3441_);
                crate::leanh::lean_inc_ref(v___x_3442_);
                v___x_3506_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_3442_, v_arg_3441_, v___y_3504_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
                if crate::leanh::lean_obj_tag(v___x_3506_) == 0 {
                    v_a_3507_ = crate::leanh::lean_ctor_get(v___x_3506_, 0);
                    v_isSharedCheck_3521_ = (!crate::leanh::lean_is_exclusive(v___x_3506_)) as u8;
                    if v_isSharedCheck_3521_ == 0 {
                        v___x_3509_ = v___x_3506_;
                        v_isShared_3510_ = v_isSharedCheck_3521_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3507_);
                        crate::leanh::lean_dec(v___x_3506_);
                        v___x_3509_ = crate::leanh::lean_box(0);
                        v_isShared_3510_ = v_isSharedCheck_3521_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3504_);
                    crate::leanh::lean_dec_ref(v___y_3503_);
                    crate::leanh::lean_dec(v___y_3501_);
                    crate::leanh::lean_dec_ref(v___x_3442_);
                    crate::leanh::lean_dec_ref(v_arg_3441_);
                    crate::leanh::lean_dec_ref(v_arg_3438_);
                    crate::leanh::lean_dec(v_head_3424_);
                    v_a_3522_ = crate::leanh::lean_ctor_get(v___x_3506_, 0);
                    v_isSharedCheck_3529_ = (!crate::leanh::lean_is_exclusive(v___x_3506_)) as u8;
                    if v_isSharedCheck_3529_ == 0 {
                        v___x_3524_ = v___x_3506_;
                        v_isShared_3525_ = v_isSharedCheck_3529_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3522_);
                        crate::leanh::lean_dec(v___x_3506_);
                        v___x_3524_ = crate::leanh::lean_box(0);
                        v_isShared_3525_ = v_isSharedCheck_3529_;
                        state = 26;
                        continue;
                    }
                }
            }
            24 => {
                v___x_3511_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__5;
                v___x_3512_ = l_Lean_Expr_constLevels_x21(v___x_3442_);
                crate::leanh::lean_dec_ref(v___x_3442_);
                v___x_3513_ = l_Lean_mkConst(v___x_3511_, v___x_3512_);
                v___x_3514_ = l_Lean_mkApp4(
                    v___x_3513_,
                    v_arg_3441_,
                    v_arg_3438_,
                    v___y_3504_,
                    v___y_3503_,
                );
                v___x_3515_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3515_, 0, v_a_3507_);
                crate::leanh::lean_ctor_set(v___x_3515_, 1, v___x_3514_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3515_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_3505_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3515_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_3502_,
                );
                v___x_3516_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3516_, 0, v_head_3424_);
                crate::leanh::lean_ctor_set(v___x_3516_, 1, v___y_3501_);
                v___x_3517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3517_, 0, v___x_3515_);
                crate::leanh::lean_ctor_set(v___x_3517_, 1, v___x_3516_);
                if v_isShared_3510_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3509_, 0, v___x_3517_);
                    v___x_3519_ = v___x_3509_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
                    v___x_3519_ = v_reuseFailAlloc_3520_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3519_;
            }
            26 => {
                if v_isShared_3525_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
                    v___x_3527_ = v_reuseFailAlloc_3528_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3527_;
            }
            28 => {
                crate::leanh::lean_inc_ref(v_arg_3438_);
                crate::leanh::lean_inc_ref(v___y_3534_);
                crate::leanh::lean_inc_ref(v___x_3442_);
                v___x_3536_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_3442_, v___y_3534_, v_arg_3438_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
                if crate::leanh::lean_obj_tag(v___x_3536_) == 0 {
                    v_a_3537_ = crate::leanh::lean_ctor_get(v___x_3536_, 0);
                    v_isSharedCheck_3551_ = (!crate::leanh::lean_is_exclusive(v___x_3536_)) as u8;
                    if v_isSharedCheck_3551_ == 0 {
                        v___x_3539_ = v___x_3536_;
                        v_isShared_3540_ = v_isSharedCheck_3551_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3537_);
                        crate::leanh::lean_dec(v___x_3536_);
                        v___x_3539_ = crate::leanh::lean_box(0);
                        v_isShared_3540_ = v_isSharedCheck_3551_;
                        state = 29;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3534_);
                    crate::leanh::lean_dec_ref(v___y_3533_);
                    crate::leanh::lean_dec(v___y_3531_);
                    crate::leanh::lean_dec_ref(v___x_3442_);
                    crate::leanh::lean_dec_ref(v_arg_3441_);
                    crate::leanh::lean_dec_ref(v_arg_3438_);
                    crate::leanh::lean_dec(v_head_3424_);
                    v_a_3552_ = crate::leanh::lean_ctor_get(v___x_3536_, 0);
                    v_isSharedCheck_3559_ = (!crate::leanh::lean_is_exclusive(v___x_3536_)) as u8;
                    if v_isSharedCheck_3559_ == 0 {
                        v___x_3554_ = v___x_3536_;
                        v_isShared_3555_ = v_isSharedCheck_3559_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3552_);
                        crate::leanh::lean_dec(v___x_3536_);
                        v___x_3554_ = crate::leanh::lean_box(0);
                        v_isShared_3555_ = v_isSharedCheck_3559_;
                        state = 31;
                        continue;
                    }
                }
            }
            29 => {
                v___x_3541_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__7;
                v___x_3542_ = l_Lean_Expr_constLevels_x21(v___x_3442_);
                crate::leanh::lean_dec_ref(v___x_3442_);
                v___x_3543_ = l_Lean_mkConst(v___x_3541_, v___x_3542_);
                v___x_3544_ = l_Lean_mkApp4(
                    v___x_3543_,
                    v_arg_3441_,
                    v___y_3534_,
                    v_arg_3438_,
                    v___y_3533_,
                );
                v___x_3545_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3545_, 0, v_a_3537_);
                crate::leanh::lean_ctor_set(v___x_3545_, 1, v___x_3544_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3545_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_3535_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3545_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_3532_,
                );
                v___x_3546_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3546_, 0, v_head_3424_);
                crate::leanh::lean_ctor_set(v___x_3546_, 1, v___y_3531_);
                v___x_3547_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3547_, 0, v___x_3545_);
                crate::leanh::lean_ctor_set(v___x_3547_, 1, v___x_3546_);
                if v_isShared_3540_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3539_, 0, v___x_3547_);
                    v___x_3549_ = v___x_3539_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3550_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
                    v___x_3549_ = v_reuseFailAlloc_3550_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3549_;
            }
            31 => {
                if v_isShared_3555_ == 0 {
                    v___x_3557_ = v___x_3554_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
                    v___x_3557_ = v_reuseFailAlloc_3558_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3557_;
            }
            33 => {
                if v___y_3565_ == 0 {
                    if crate::leanh::lean_obj_tag(v___y_3564_) == 0 {
                        crate::leanh::lean_dec_ref(v_arg_3438_);
                        v_contextDependent_3566_ =
                            crate::leanh::lean_ctor_get_uint8(v___y_3564_, 1 as u32);
                        crate::leanh::lean_dec_ref_known(v___y_3564_, 0);
                        v___y_3473_ = v___y_3563_;
                        v___y_3474_ = v_contextDependent_3566_;
                        state = 18;
                        continue;
                    } else {
                        v_proof_3567_ = crate::leanh::lean_ctor_get(v___y_3564_, 1);
                        crate::leanh::lean_inc_ref(v_proof_3567_);
                        v_contextDependent_3568_ = crate::leanh::lean_ctor_get_uint8(
                            v___y_3564_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v___y_3564_, 2);
                        v___y_3444_ = v___y_3563_;
                        v_proof_3445_ = v_proof_3567_;
                        v___y_3446_ = v_contextDependent_3568_;
                        state = 13;
                        continue;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v___y_3564_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___y_3564_, 0);
                        crate::leanh::lean_dec_ref(v_arg_3438_);
                        v___y_3473_ = v___y_3563_;
                        v___y_3474_ = v___x_3561_;
                        state = 18;
                        continue;
                    } else {
                        v_proof_3569_ = crate::leanh::lean_ctor_get(v___y_3564_, 1);
                        crate::leanh::lean_inc_ref(v_proof_3569_);
                        crate::leanh::lean_dec_ref_known(v___y_3564_, 2);
                        v___y_3444_ = v___y_3563_;
                        v_proof_3445_ = v_proof_3569_;
                        v___y_3446_ = v___x_3561_;
                        state = 13;
                        continue;
                    }
                }
            }
            34 => {
                crate::leanh::lean_inc_ref(v___y_3573_);
                crate::leanh::lean_inc_ref(v___y_3577_);
                crate::leanh::lean_inc_ref(v___x_3442_);
                v___x_3579_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0(v___x_3442_, v___y_3577_, v___y_3573_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
                if crate::leanh::lean_obj_tag(v___x_3579_) == 0 {
                    v_a_3580_ = crate::leanh::lean_ctor_get(v___x_3579_, 0);
                    crate::leanh::lean_inc(v_a_3580_);
                    crate::leanh::lean_dec_ref_known(v___x_3579_, 1);
                    v___x_3581_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__9;
                    v___x_3582_ = l_Lean_Expr_constLevels_x21(v___x_3442_);
                    crate::leanh::lean_dec_ref(v___x_3442_);
                    v___x_3583_ = l_Lean_mkConst(v___x_3581_, v___x_3582_);
                    v___x_3584_ = l_Lean_mkApp6(
                        v___x_3583_,
                        v_arg_3441_,
                        v___y_3577_,
                        v_arg_3438_,
                        v___y_3573_,
                        v___y_3576_,
                        v___y_3572_,
                    );
                    if v___y_3574_ == 0 {
                        v___y_3427_ = v___x_3584_;
                        v___y_3428_ = v___y_3571_;
                        v___y_3429_ = v___y_3578_;
                        v___y_3430_ = v_a_3580_;
                        v___y_3431_ = v___y_3575_;
                        state = 12;
                        continue;
                    } else {
                        v___y_3427_ = v___x_3584_;
                        v___y_3428_ = v___y_3571_;
                        v___y_3429_ = v___y_3578_;
                        v___y_3430_ = v_a_3580_;
                        v___y_3431_ = v___x_3561_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3577_);
                    crate::leanh::lean_dec_ref(v___y_3576_);
                    crate::leanh::lean_dec_ref(v___y_3573_);
                    crate::leanh::lean_dec_ref(v___y_3572_);
                    crate::leanh::lean_dec(v___y_3571_);
                    crate::leanh::lean_dec_ref(v___x_3442_);
                    crate::leanh::lean_dec_ref(v_arg_3441_);
                    crate::leanh::lean_dec_ref(v_arg_3438_);
                    crate::leanh::lean_dec(v_head_3424_);
                    v_a_3585_ = crate::leanh::lean_ctor_get(v___x_3579_, 0);
                    v_isSharedCheck_3592_ = (!crate::leanh::lean_is_exclusive(v___x_3579_)) as u8;
                    if v_isSharedCheck_3592_ == 0 {
                        v___x_3587_ = v___x_3579_;
                        v_isShared_3588_ = v_isSharedCheck_3592_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3585_);
                        crate::leanh::lean_dec(v___x_3579_);
                        v___x_3587_ = crate::leanh::lean_box(0);
                        v_isShared_3588_ = v_isSharedCheck_3592_;
                        state = 35;
                        continue;
                    }
                }
            }
            35 => {
                if v_isShared_3588_ == 0 {
                    v___x_3590_ = v___x_3587_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
                    v___x_3590_ = v_reuseFailAlloc_3591_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3590_;
            }
            37 => {
                v___x_3602_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_3441_, v_a_3357_);
                crate::leanh::lean_dec_ref(v_arg_3441_);
                if crate::leanh::lean_obj_tag(v___x_3602_) == 0 {
                    v_a_3603_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
                    v_isSharedCheck_3625_ = (!crate::leanh::lean_is_exclusive(v___x_3602_)) as u8;
                    if v_isSharedCheck_3625_ == 0 {
                        v___x_3605_ = v___x_3602_;
                        v_isShared_3606_ = v_isSharedCheck_3625_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3603_);
                        crate::leanh::lean_dec(v___x_3602_);
                        v___x_3605_ = crate::leanh::lean_box(0);
                        v_isShared_3606_ = v_isSharedCheck_3625_;
                        state = 38;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3599_);
                    crate::leanh::lean_dec_ref(v_arg_3438_);
                    crate::leanh::lean_dec_ref_known(v_infos_3352_, 2);
                    v_a_3626_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
                    v_isSharedCheck_3633_ = (!crate::leanh::lean_is_exclusive(v___x_3602_)) as u8;
                    if v_isSharedCheck_3633_ == 0 {
                        v___x_3628_ = v___x_3602_;
                        v_isShared_3629_ = v_isSharedCheck_3633_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3626_);
                        crate::leanh::lean_dec(v___x_3602_);
                        v___x_3628_ = crate::leanh::lean_box(0);
                        v_isShared_3629_ = v_isSharedCheck_3633_;
                        state = 42;
                        continue;
                    }
                }
            }
            38 => {
                v___x_3607_ = (crate::leanh::lean_unbox(v_a_3603_) as u8);
                crate::leanh::lean_dec(v_a_3603_);
                if v___x_3607_ == 0 {
                    crate::leanh::lean_del_object(v___x_3605_);
                    crate::leanh::lean_dec(v___y_3599_);
                    crate::leanh::lean_dec_ref(v_arg_3438_);
                    v___y_3393_ = v___y_3601_;
                    state = 6;
                    continue;
                } else {
                    v___x_3608_ = crate::leanh::lean_box(0);
                    v___x_3609_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_3424_, v___x_3608_);
                    if v___x_3609_ == 0 {
                        crate::leanh::lean_del_object(v___x_3605_);
                        crate::leanh::lean_dec(v___y_3599_);
                        crate::leanh::lean_dec_ref(v_arg_3438_);
                        v___y_3393_ = v___y_3601_;
                        state = 6;
                        continue;
                    } else {
                        v_isSharedCheck_3622_ =
                            (!crate::leanh::lean_is_exclusive(v_infos_3352_)) as u8;
                        if v_isSharedCheck_3622_ == 0 {
                            v_unused_3623_ = crate::leanh::lean_ctor_get(v_infos_3352_, 1);
                            crate::leanh::lean_dec(v_unused_3623_);
                            v_unused_3624_ = crate::leanh::lean_ctor_get(v_infos_3352_, 0);
                            crate::leanh::lean_dec(v_unused_3624_);
                            v___x_3611_ = v_infos_3352_;
                            v_isShared_3612_ = v_isSharedCheck_3622_;
                            state = 39;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_infos_3352_);
                            v___x_3611_ = crate::leanh::lean_box(0);
                            v_isShared_3612_ = v_isSharedCheck_3622_;
                            state = 39;
                            continue;
                        }
                    }
                }
            }
            39 => {
                v___x_3613_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__12);
                crate::leanh::lean_inc_ref(v_arg_3438_);
                v___x_3614_ = l_Lean_Expr_app___override(v___x_3613_, v_arg_3438_);
                v___x_3615_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3615_, 0, v_arg_3438_);
                crate::leanh::lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_3600_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_3601_,
                );
                if v_isShared_3612_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3611_, 0);
                    crate::leanh::lean_ctor_set(v___x_3611_, 1, v___y_3599_);
                    crate::leanh::lean_ctor_set(v___x_3611_, 0, v___x_3615_);
                    v___x_3617_ = v___x_3611_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3621_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 1, v___y_3599_);
                    v___x_3617_ = v_reuseFailAlloc_3621_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_3606_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3605_, 0, v___x_3617_);
                    v___x_3619_ = v___x_3605_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3620_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3617_);
                    v___x_3619_ = v_reuseFailAlloc_3620_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3619_;
            }
            42 => {
                if v_isShared_3629_ == 0 {
                    v___x_3631_ = v___x_3628_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
                    v___x_3631_ = v_reuseFailAlloc_3632_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_3631_;
            }
            44 => {
                v___x_3640_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_3441_, v_a_3357_);
                if crate::leanh::lean_obj_tag(v___x_3640_) == 0 {
                    v_a_3641_ = crate::leanh::lean_ctor_get(v___x_3640_, 0);
                    v_isSharedCheck_3656_ = (!crate::leanh::lean_is_exclusive(v___x_3640_)) as u8;
                    if v_isSharedCheck_3656_ == 0 {
                        v___x_3643_ = v___x_3640_;
                        v_isShared_3644_ = v_isSharedCheck_3656_;
                        state = 45;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3641_);
                        crate::leanh::lean_dec(v___x_3640_);
                        v___x_3643_ = crate::leanh::lean_box(0);
                        v_isShared_3644_ = v_isSharedCheck_3656_;
                        state = 45;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3638_);
                    crate::leanh::lean_dec_ref(v___y_3637_);
                    crate::leanh::lean_dec(v___y_3635_);
                    crate::leanh::lean_dec_ref(v___x_3442_);
                    crate::leanh::lean_dec_ref(v_arg_3441_);
                    crate::leanh::lean_dec_ref(v_arg_3438_);
                    crate::leanh::lean_dec(v_head_3424_);
                    v_a_3657_ = crate::leanh::lean_ctor_get(v___x_3640_, 0);
                    v_isSharedCheck_3664_ = (!crate::leanh::lean_is_exclusive(v___x_3640_)) as u8;
                    if v_isSharedCheck_3664_ == 0 {
                        v___x_3659_ = v___x_3640_;
                        v_isShared_3660_ = v_isSharedCheck_3664_;
                        state = 47;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3657_);
                        crate::leanh::lean_dec(v___x_3640_);
                        v___x_3659_ = crate::leanh::lean_box(0);
                        v_isShared_3660_ = v_isSharedCheck_3664_;
                        state = 47;
                        continue;
                    }
                }
            }
            45 => {
                v___x_3645_ = (crate::leanh::lean_unbox(v_a_3641_) as u8);
                if v___x_3645_ == 0 {
                    crate::leanh::lean_del_object(v___x_3643_);
                    v___x_3646_ = (crate::leanh::lean_unbox(v_a_3641_) as u8);
                    crate::leanh::lean_dec(v_a_3641_);
                    v___y_3501_ = v___y_3635_;
                    v___y_3502_ = v___y_3639_;
                    v___y_3503_ = v___y_3637_;
                    v___y_3504_ = v___y_3638_;
                    v___y_3505_ = v___x_3646_;
                    state = 23;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_3641_);
                    v___x_3647_ = crate::leanh::lean_box(0);
                    v___x_3648_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_3424_, v___x_3647_);
                    if v___x_3648_ == 0 {
                        crate::leanh::lean_del_object(v___x_3643_);
                        v___y_3501_ = v___y_3635_;
                        v___y_3502_ = v___y_3639_;
                        v___y_3503_ = v___y_3637_;
                        v___y_3504_ = v___y_3638_;
                        v___y_3505_ = v___x_3648_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3442_);
                        crate::leanh::lean_dec_ref(v_arg_3441_);
                        crate::leanh::lean_dec(v_head_3424_);
                        v___x_3649_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__15);
                        crate::leanh::lean_inc_ref(v___y_3638_);
                        v___x_3650_ =
                            l_Lean_mkApp3(v___x_3649_, v_arg_3438_, v___y_3638_, v___y_3637_);
                        v___x_3651_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        crate::leanh::lean_ctor_set(v___x_3651_, 0, v___y_3638_);
                        crate::leanh::lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3651_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___y_3636_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3651_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                            v___y_3639_,
                        );
                        v___x_3652_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3652_, 0, v___x_3651_);
                        crate::leanh::lean_ctor_set(v___x_3652_, 1, v___y_3635_);
                        if v_isShared_3644_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3643_, 0, v___x_3652_);
                            v___x_3654_ = v___x_3643_;
                            state = 46;
                            continue;
                        } else {
                            v_reuseFailAlloc_3655_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
                            v___x_3654_ = v_reuseFailAlloc_3655_;
                            state = 46;
                            continue;
                        }
                    }
                }
            }
            46 => {
                return v___x_3654_;
            }
            47 => {
                if v_isShared_3660_ == 0 {
                    v___x_3662_ = v___x_3659_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
                    v___x_3662_ = v_reuseFailAlloc_3663_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_3662_;
            }
            49 => {
                v___x_3671_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___y_3669_, v_a_3357_);
                if crate::leanh::lean_obj_tag(v___x_3671_) == 0 {
                    v_a_3672_ = crate::leanh::lean_ctor_get(v___x_3671_, 0);
                    v_isSharedCheck_3687_ = (!crate::leanh::lean_is_exclusive(v___x_3671_)) as u8;
                    if v_isSharedCheck_3687_ == 0 {
                        v___x_3674_ = v___x_3671_;
                        v_isShared_3675_ = v_isSharedCheck_3687_;
                        state = 50;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3672_);
                        crate::leanh::lean_dec(v___x_3671_);
                        v___x_3674_ = crate::leanh::lean_box(0);
                        v_isShared_3675_ = v_isSharedCheck_3687_;
                        state = 50;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3669_);
                    crate::leanh::lean_dec_ref(v___y_3668_);
                    crate::leanh::lean_dec(v___y_3666_);
                    crate::leanh::lean_dec_ref(v___x_3442_);
                    crate::leanh::lean_dec_ref(v_arg_3441_);
                    crate::leanh::lean_dec_ref(v_arg_3438_);
                    crate::leanh::lean_dec(v_head_3424_);
                    v_a_3688_ = crate::leanh::lean_ctor_get(v___x_3671_, 0);
                    v_isSharedCheck_3695_ = (!crate::leanh::lean_is_exclusive(v___x_3671_)) as u8;
                    if v_isSharedCheck_3695_ == 0 {
                        v___x_3690_ = v___x_3671_;
                        v_isShared_3691_ = v_isSharedCheck_3695_;
                        state = 52;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3688_);
                        crate::leanh::lean_dec(v___x_3671_);
                        v___x_3690_ = crate::leanh::lean_box(0);
                        v_isShared_3691_ = v_isSharedCheck_3695_;
                        state = 52;
                        continue;
                    }
                }
            }
            50 => {
                v___x_3676_ = (crate::leanh::lean_unbox(v_a_3672_) as u8);
                if v___x_3676_ == 0 {
                    crate::leanh::lean_del_object(v___x_3674_);
                    v___x_3677_ = (crate::leanh::lean_unbox(v_a_3672_) as u8);
                    crate::leanh::lean_dec(v_a_3672_);
                    v___y_3531_ = v___y_3666_;
                    v___y_3532_ = v___y_3670_;
                    v___y_3533_ = v___y_3668_;
                    v___y_3534_ = v___y_3669_;
                    v___y_3535_ = v___x_3677_;
                    state = 28;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_3672_);
                    v___x_3678_ = crate::leanh::lean_box(0);
                    v___x_3679_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_3424_, v___x_3678_);
                    if v___x_3679_ == 0 {
                        crate::leanh::lean_del_object(v___x_3674_);
                        v___y_3531_ = v___y_3666_;
                        v___y_3532_ = v___y_3670_;
                        v___y_3533_ = v___y_3668_;
                        v___y_3534_ = v___y_3669_;
                        v___y_3535_ = v___x_3679_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3669_);
                        crate::leanh::lean_dec_ref(v___x_3442_);
                        crate::leanh::lean_dec(v_head_3424_);
                        v___x_3680_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__18);
                        crate::leanh::lean_inc_ref(v_arg_3438_);
                        v___x_3681_ =
                            l_Lean_mkApp3(v___x_3680_, v_arg_3441_, v_arg_3438_, v___y_3668_);
                        v___x_3682_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        crate::leanh::lean_ctor_set(v___x_3682_, 0, v_arg_3438_);
                        crate::leanh::lean_ctor_set(v___x_3682_, 1, v___x_3681_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3682_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___y_3667_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3682_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                            v___y_3670_,
                        );
                        v___x_3683_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3683_, 0, v___x_3682_);
                        crate::leanh::lean_ctor_set(v___x_3683_, 1, v___y_3666_);
                        if v_isShared_3675_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3674_, 0, v___x_3683_);
                            v___x_3685_ = v___x_3674_;
                            state = 51;
                            continue;
                        } else {
                            v_reuseFailAlloc_3686_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3683_);
                            v___x_3685_ = v_reuseFailAlloc_3686_;
                            state = 51;
                            continue;
                        }
                    }
                }
            }
            51 => {
                return v___x_3685_;
            }
            52 => {
                if v_isShared_3691_ == 0 {
                    v___x_3693_ = v___x_3690_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
                    v___x_3693_ = v_reuseFailAlloc_3694_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_3693_;
            }
            54 => {
                crate::leanh::lean_inc(v_tail_3425_);
                crate::leanh::lean_inc_ref(v_arg_3438_);
                v___x_3698_ =
                    l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(
                        v_arg_3438_,
                        v_tail_3425_,
                        v_simpBody_3353_,
                        v_a_3354_,
                        v_a_3355_,
                        v_a_3356_,
                        v_a_3357_,
                        v_a_3358_,
                        v_a_3359_,
                        v_a_3360_,
                        v_a_3361_,
                        v_a_3362_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3698_) == 0 {
                    v_a_3699_ = crate::leanh::lean_ctor_get(v___x_3698_, 0);
                    crate::leanh::lean_inc(v_a_3699_);
                    crate::leanh::lean_dec_ref_known(v___x_3698_, 1);
                    v_fst_3700_ = crate::leanh::lean_ctor_get(v_a_3699_, 0);
                    crate::leanh::lean_inc(v_fst_3700_);
                    v_snd_3701_ = crate::leanh::lean_ctor_get(v_a_3699_, 1);
                    crate::leanh::lean_inc(v_snd_3701_);
                    crate::leanh::lean_dec(v_a_3699_);
                    v___x_3702_ =
                        l_Lean_Meta_Sym_Simp_Result_getResultExpr(v_arg_3438_, v_fst_3700_);
                    v___x_3703_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v___x_3702_, v_a_3357_);
                    crate::leanh::lean_dec_ref(v___x_3702_);
                    if crate::leanh::lean_obj_tag(v___x_3703_) == 0 {
                        v_a_3704_ = crate::leanh::lean_ctor_get(v___x_3703_, 0);
                        crate::leanh::lean_inc(v_a_3704_);
                        crate::leanh::lean_dec_ref_known(v___x_3703_, 1);
                        v___x_3705_ = (crate::leanh::lean_unbox(v_a_3704_) as u8);
                        if v___x_3705_ == 0 {
                            if crate::leanh::lean_obj_tag(v_a_3594_) == 0 {
                                if crate::leanh::lean_obj_tag(v_fst_3700_) == 0 {
                                    crate::leanh::lean_dec_ref(v___x_3442_);
                                    v_contextDependent_3706_ =
                                        crate::leanh::lean_ctor_get_uint8(v_a_3594_, 1 as u32);
                                    crate::leanh::lean_dec_ref_known(v_a_3594_, 0);
                                    if v_contextDependent_3706_ == 0 {
                                        v_contextDependent_3707_ =
                                            crate::leanh::lean_ctor_get_uint8(
                                                v_fst_3700_,
                                                1 as u32,
                                            );
                                        crate::leanh::lean_dec_ref_known(v_fst_3700_, 0);
                                        v___x_3708_ = (crate::leanh::lean_unbox(v_a_3704_) as u8);
                                        crate::leanh::lean_dec(v_a_3704_);
                                        v___y_3599_ = v_snd_3701_;
                                        v___y_3600_ = v___x_3708_;
                                        v___y_3601_ = v_contextDependent_3707_;
                                        state = 37;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_fst_3700_, 0);
                                        v___x_3709_ = (crate::leanh::lean_unbox(v_a_3704_) as u8);
                                        crate::leanh::lean_dec(v_a_3704_);
                                        v___y_3599_ = v_snd_3701_;
                                        v___y_3600_ = v___x_3709_;
                                        v___y_3601_ = v___x_3561_;
                                        state = 37;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_head_3424_);
                                    crate::leanh::lean_dec_ref_known(v_infos_3352_, 2);
                                    v_contextDependent_3710_ =
                                        crate::leanh::lean_ctor_get_uint8(v_a_3594_, 1 as u32);
                                    crate::leanh::lean_dec_ref_known(v_a_3594_, 0);
                                    if v_contextDependent_3710_ == 0 {
                                        v_e_x27_3711_ = crate::leanh::lean_ctor_get(v_fst_3700_, 0);
                                        crate::leanh::lean_inc_ref(v_e_x27_3711_);
                                        v_proof_3712_ = crate::leanh::lean_ctor_get(v_fst_3700_, 1);
                                        crate::leanh::lean_inc_ref(v_proof_3712_);
                                        v_contextDependent_3713_ =
                                            crate::leanh::lean_ctor_get_uint8(
                                                v_fst_3700_,
                                                (core::mem::size_of::<*mut crate::leanh::LeanObject>(
                                                ) * 2
                                                    + 1)
                                                    as u32,
                                            );
                                        crate::leanh::lean_dec_ref_known(v_fst_3700_, 2);
                                        v___x_3714_ = (crate::leanh::lean_unbox(v_a_3704_) as u8);
                                        crate::leanh::lean_dec(v_a_3704_);
                                        v___y_3635_ = v_snd_3701_;
                                        v___y_3636_ = v___x_3714_;
                                        v___y_3637_ = v_proof_3712_;
                                        v___y_3638_ = v_e_x27_3711_;
                                        v___y_3639_ = v_contextDependent_3713_;
                                        state = 44;
                                        continue;
                                    } else {
                                        v_e_x27_3715_ = crate::leanh::lean_ctor_get(v_fst_3700_, 0);
                                        crate::leanh::lean_inc_ref(v_e_x27_3715_);
                                        v_proof_3716_ = crate::leanh::lean_ctor_get(v_fst_3700_, 1);
                                        crate::leanh::lean_inc_ref(v_proof_3716_);
                                        crate::leanh::lean_dec_ref_known(v_fst_3700_, 2);
                                        v___x_3717_ = (crate::leanh::lean_unbox(v_a_3704_) as u8);
                                        crate::leanh::lean_dec(v_a_3704_);
                                        v___y_3635_ = v_snd_3701_;
                                        v___y_3636_ = v___x_3717_;
                                        v___y_3637_ = v_proof_3716_;
                                        v___y_3638_ = v_e_x27_3715_;
                                        v___y_3639_ = v___x_3561_;
                                        state = 44;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_inc(v_head_3424_);
                                crate::leanh::lean_dec_ref_known(v_infos_3352_, 2);
                                if crate::leanh::lean_obj_tag(v_fst_3700_) == 0 {
                                    v_contextDependent_3718_ = crate::leanh::lean_ctor_get_uint8(
                                        v_a_3594_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    if v_contextDependent_3718_ == 0 {
                                        v_e_x27_3719_ = crate::leanh::lean_ctor_get(v_a_3594_, 0);
                                        crate::leanh::lean_inc_ref(v_e_x27_3719_);
                                        v_proof_3720_ = crate::leanh::lean_ctor_get(v_a_3594_, 1);
                                        crate::leanh::lean_inc_ref(v_proof_3720_);
                                        crate::leanh::lean_dec_ref_known(v_a_3594_, 2);
                                        v_contextDependent_3721_ =
                                            crate::leanh::lean_ctor_get_uint8(
                                                v_fst_3700_,
                                                1 as u32,
                                            );
                                        crate::leanh::lean_dec_ref_known(v_fst_3700_, 0);
                                        v___x_3722_ = (crate::leanh::lean_unbox(v_a_3704_) as u8);
                                        crate::leanh::lean_dec(v_a_3704_);
                                        v___y_3666_ = v_snd_3701_;
                                        v___y_3667_ = v___x_3722_;
                                        v___y_3668_ = v_proof_3720_;
                                        v___y_3669_ = v_e_x27_3719_;
                                        v___y_3670_ = v_contextDependent_3721_;
                                        state = 49;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_fst_3700_, 0);
                                        v_e_x27_3723_ = crate::leanh::lean_ctor_get(v_a_3594_, 0);
                                        crate::leanh::lean_inc_ref(v_e_x27_3723_);
                                        v_proof_3724_ = crate::leanh::lean_ctor_get(v_a_3594_, 1);
                                        crate::leanh::lean_inc_ref(v_proof_3724_);
                                        crate::leanh::lean_dec_ref_known(v_a_3594_, 2);
                                        v___x_3725_ = (crate::leanh::lean_unbox(v_a_3704_) as u8);
                                        crate::leanh::lean_dec(v_a_3704_);
                                        v___y_3666_ = v_snd_3701_;
                                        v___y_3667_ = v___x_3725_;
                                        v___y_3668_ = v_proof_3724_;
                                        v___y_3669_ = v_e_x27_3723_;
                                        v___y_3670_ = v___x_3561_;
                                        state = 49;
                                        continue;
                                    }
                                } else {
                                    v_e_x27_3726_ = crate::leanh::lean_ctor_get(v_a_3594_, 0);
                                    crate::leanh::lean_inc_ref(v_e_x27_3726_);
                                    v_proof_3727_ = crate::leanh::lean_ctor_get(v_a_3594_, 1);
                                    crate::leanh::lean_inc_ref(v_proof_3727_);
                                    v_contextDependent_3728_ = crate::leanh::lean_ctor_get_uint8(
                                        v_a_3594_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    crate::leanh::lean_dec_ref_known(v_a_3594_, 2);
                                    v_e_x27_3729_ = crate::leanh::lean_ctor_get(v_fst_3700_, 0);
                                    crate::leanh::lean_inc_ref(v_e_x27_3729_);
                                    v_proof_3730_ = crate::leanh::lean_ctor_get(v_fst_3700_, 1);
                                    crate::leanh::lean_inc_ref(v_proof_3730_);
                                    v_contextDependent_3731_ = crate::leanh::lean_ctor_get_uint8(
                                        v_fst_3700_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    crate::leanh::lean_dec_ref_known(v_fst_3700_, 2);
                                    v___x_3732_ = l_Lean_Meta_Sym_isTrueExpr___redArg(
                                        v_e_x27_3726_,
                                        v_a_3357_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3732_) == 0 {
                                        v_a_3733_ = crate::leanh::lean_ctor_get(v___x_3732_, 0);
                                        crate::leanh::lean_inc(v_a_3733_);
                                        crate::leanh::lean_dec_ref_known(v___x_3732_, 1);
                                        v___x_3734_ = (crate::leanh::lean_unbox(v_a_3733_) as u8);
                                        if v___x_3734_ == 0 {
                                            crate::leanh::lean_dec(v_a_3704_);
                                            v___x_3735_ =
                                                (crate::leanh::lean_unbox(v_a_3733_) as u8);
                                            crate::leanh::lean_dec(v_a_3733_);
                                            v___y_3571_ = v_snd_3701_;
                                            v___y_3572_ = v_proof_3730_;
                                            v___y_3573_ = v_e_x27_3729_;
                                            v___y_3574_ = v_contextDependent_3728_;
                                            v___y_3575_ = v_contextDependent_3731_;
                                            v___y_3576_ = v_proof_3727_;
                                            v___y_3577_ = v_e_x27_3726_;
                                            v___y_3578_ = v___x_3735_;
                                            state = 34;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_3733_);
                                            v___x_3736_ = crate::leanh::lean_box(0);
                                            v___x_3737_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___lam__0(v_head_3424_, v___x_3736_);
                                            if v___x_3737_ == 0 {
                                                crate::leanh::lean_dec(v_a_3704_);
                                                v___y_3571_ = v_snd_3701_;
                                                v___y_3572_ = v_proof_3730_;
                                                v___y_3573_ = v_e_x27_3729_;
                                                v___y_3574_ = v_contextDependent_3728_;
                                                v___y_3575_ = v_contextDependent_3731_;
                                                v___y_3576_ = v_proof_3727_;
                                                v___y_3577_ = v_e_x27_3726_;
                                                v___y_3578_ = v___x_3737_;
                                                state = 34;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v_e_x27_3726_);
                                                crate::leanh::lean_dec_ref(v___x_3442_);
                                                crate::leanh::lean_dec(v_head_3424_);
                                                v___x_3738_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__21);
                                                crate::leanh::lean_inc_ref(v_e_x27_3729_);
                                                v___x_3739_ = l_Lean_mkApp5(
                                                    v___x_3738_,
                                                    v_arg_3441_,
                                                    v_arg_3438_,
                                                    v_e_x27_3729_,
                                                    v_proof_3727_,
                                                    v_proof_3730_,
                                                );
                                                if v_contextDependent_3728_ == 0 {
                                                    v___x_3740_ =
                                                        (crate::leanh::lean_unbox(v_a_3704_) as u8);
                                                    crate::leanh::lean_dec(v_a_3704_);
                                                    v___y_3398_ = v_snd_3701_;
                                                    v___y_3399_ = v___x_3740_;
                                                    v___y_3400_ = v_e_x27_3729_;
                                                    v___y_3401_ = v___x_3739_;
                                                    v___y_3402_ = v_contextDependent_3731_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    v___x_3741_ =
                                                        (crate::leanh::lean_unbox(v_a_3704_) as u8);
                                                    crate::leanh::lean_dec(v_a_3704_);
                                                    v___y_3398_ = v_snd_3701_;
                                                    v___y_3399_ = v___x_3741_;
                                                    v___y_3400_ = v_e_x27_3729_;
                                                    v___y_3401_ = v___x_3739_;
                                                    v___y_3402_ = v___x_3561_;
                                                    state = 7;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_proof_3730_);
                                        crate::leanh::lean_dec_ref(v_e_x27_3729_);
                                        crate::leanh::lean_dec_ref(v_proof_3727_);
                                        crate::leanh::lean_dec_ref(v_e_x27_3726_);
                                        crate::leanh::lean_dec(v_a_3704_);
                                        crate::leanh::lean_dec(v_snd_3701_);
                                        crate::leanh::lean_dec_ref(v___x_3442_);
                                        crate::leanh::lean_dec_ref(v_arg_3441_);
                                        crate::leanh::lean_dec_ref(v_arg_3438_);
                                        crate::leanh::lean_dec(v_head_3424_);
                                        v_a_3742_ = crate::leanh::lean_ctor_get(v___x_3732_, 0);
                                        v_isSharedCheck_3749_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3732_)) as u8;
                                        if v_isSharedCheck_3749_ == 0 {
                                            v___x_3744_ = v___x_3732_;
                                            v_isShared_3745_ = v_isSharedCheck_3749_;
                                            state = 55;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3742_);
                                            crate::leanh::lean_dec(v___x_3732_);
                                            v___x_3744_ = crate::leanh::lean_box(0);
                                            v_isShared_3745_ = v_isSharedCheck_3749_;
                                            state = 55;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_inc(v_head_3424_);
                            crate::leanh::lean_dec(v_a_3704_);
                            crate::leanh::lean_dec(v_snd_3701_);
                            crate::leanh::lean_dec_ref(v___x_3442_);
                            crate::leanh::lean_dec_ref_known(v_infos_3352_, 2);
                            if crate::leanh::lean_obj_tag(v_a_3594_) == 0 {
                                v_contextDependent_3750_ =
                                    crate::leanh::lean_ctor_get_uint8(v_a_3594_, 1 as u32);
                                crate::leanh::lean_dec_ref_known(v_a_3594_, 0);
                                v___y_3563_ = v___y_3697_;
                                v___y_3564_ = v_fst_3700_;
                                v___y_3565_ = v_contextDependent_3750_;
                                state = 33;
                                continue;
                            } else {
                                v_contextDependent_3751_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_3594_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1)
                                        as u32,
                                );
                                crate::leanh::lean_dec_ref_known(v_a_3594_, 2);
                                v___y_3563_ = v___y_3697_;
                                v___y_3564_ = v_fst_3700_;
                                v___y_3565_ = v_contextDependent_3751_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_3701_);
                        crate::leanh::lean_dec(v_fst_3700_);
                        crate::leanh::lean_dec(v_a_3594_);
                        crate::leanh::lean_dec_ref(v___x_3442_);
                        crate::leanh::lean_dec_ref(v_arg_3441_);
                        crate::leanh::lean_dec_ref(v_arg_3438_);
                        crate::leanh::lean_dec_ref_known(v_infos_3352_, 2);
                        v_a_3752_ = crate::leanh::lean_ctor_get(v___x_3703_, 0);
                        v_isSharedCheck_3759_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3703_)) as u8;
                        if v_isSharedCheck_3759_ == 0 {
                            v___x_3754_ = v___x_3703_;
                            v_isShared_3755_ = v_isSharedCheck_3759_;
                            state = 57;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3752_);
                            crate::leanh::lean_dec(v___x_3703_);
                            v___x_3754_ = crate::leanh::lean_box(0);
                            v_isShared_3755_ = v_isSharedCheck_3759_;
                            state = 57;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3594_);
                    crate::leanh::lean_dec_ref(v___x_3442_);
                    crate::leanh::lean_dec_ref(v_arg_3441_);
                    crate::leanh::lean_dec_ref(v_arg_3438_);
                    crate::leanh::lean_dec_ref_known(v_infos_3352_, 2);
                    return v___x_3698_;
                }
            }
            55 => {
                if v_isShared_3745_ == 0 {
                    v___x_3747_ = v___x_3744_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_3748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
                    v___x_3747_ = v_reuseFailAlloc_3748_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_3747_;
            }
            57 => {
                if v_isShared_3755_ == 0 {
                    v___x_3757_ = v___x_3754_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_3758_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
                    v___x_3757_ = v_reuseFailAlloc_3758_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_3757_;
            }
            59 => {
                if crate::leanh::lean_obj_tag(v_a_3594_) == 0 {
                    crate::leanh::lean_dec_ref(v_arg_3441_);
                    v_contextDependent_3767_ =
                        crate::leanh::lean_ctor_get_uint8(v_a_3594_, 1 as u32);
                    crate::leanh::lean_dec_ref_known(v_a_3594_, 0);
                    v___x_3768_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3357_);
                    if crate::leanh::lean_obj_tag(v___x_3768_) == 0 {
                        v_a_3769_ = crate::leanh::lean_ctor_get(v___x_3768_, 0);
                        v_isSharedCheck_3784_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3768_)) as u8;
                        if v_isSharedCheck_3784_ == 0 {
                            v___x_3771_ = v___x_3768_;
                            v_isShared_3772_ = v_isSharedCheck_3784_;
                            state = 60;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3769_);
                            crate::leanh::lean_dec(v___x_3768_);
                            v___x_3771_ = crate::leanh::lean_box(0);
                            v_isShared_3772_ = v_isSharedCheck_3784_;
                            state = 60;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3765_);
                        crate::leanh::lean_dec_ref(v_arg_3438_);
                        v_a_3785_ = crate::leanh::lean_ctor_get(v___x_3768_, 0);
                        v_isSharedCheck_3792_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3768_)) as u8;
                        if v_isSharedCheck_3792_ == 0 {
                            v___x_3787_ = v___x_3768_;
                            v_isShared_3788_ = v_isSharedCheck_3792_;
                            state = 63;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3785_);
                            crate::leanh::lean_dec(v___x_3768_);
                            v___x_3787_ = crate::leanh::lean_box(0);
                            v_isShared_3788_ = v_isSharedCheck_3792_;
                            state = 63;
                            continue;
                        }
                    }
                } else {
                    v_proof_3793_ = crate::leanh::lean_ctor_get(v_a_3594_, 1);
                    v_contextDependent_3794_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_3594_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_3825_ = (!crate::leanh::lean_is_exclusive(v_a_3594_)) as u8;
                    if v_isSharedCheck_3825_ == 0 {
                        v_unused_3826_ = crate::leanh::lean_ctor_get(v_a_3594_, 0);
                        crate::leanh::lean_dec(v_unused_3826_);
                        v___x_3796_ = v_a_3594_;
                        v_isShared_3797_ = v_isSharedCheck_3825_;
                        state = 65;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_proof_3793_);
                        crate::leanh::lean_dec(v_a_3594_);
                        v___x_3796_ = crate::leanh::lean_box(0);
                        v_isShared_3797_ = v_isSharedCheck_3825_;
                        state = 65;
                        continue;
                    }
                }
            }
            60 => {
                v___x_3773_ = crate::leanh::lean_box(0);
                v___x_3774_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__24);
                v___x_3775_ = l_Lean_Expr_app___override(v___x_3774_, v_arg_3438_);
                v___x_3776_ = 0;
                v___x_3777_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3777_, 0, v_a_3769_);
                crate::leanh::lean_ctor_set(v___x_3777_, 1, v___x_3775_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3777_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3776_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3777_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_3767_,
                );
                if v_isShared_3766_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3765_, 0);
                    crate::leanh::lean_ctor_set(v___x_3765_, 1, v___x_3773_);
                    crate::leanh::lean_ctor_set(v___x_3765_, 0, v___x_3777_);
                    v___x_3779_ = v___x_3765_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_3783_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3783_, 1, v___x_3773_);
                    v___x_3779_ = v_reuseFailAlloc_3783_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                if v_isShared_3772_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3771_, 0, v___x_3779_);
                    v___x_3781_ = v___x_3771_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_3782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3779_);
                    v___x_3781_ = v_reuseFailAlloc_3782_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_3781_;
            }
            63 => {
                if v_isShared_3788_ == 0 {
                    v___x_3790_ = v___x_3787_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_3791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
                    v___x_3790_ = v_reuseFailAlloc_3791_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_3790_;
            }
            65 => {
                v___x_3798_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3357_);
                if crate::leanh::lean_obj_tag(v___x_3798_) == 0 {
                    v_a_3799_ = crate::leanh::lean_ctor_get(v___x_3798_, 0);
                    v_isSharedCheck_3816_ = (!crate::leanh::lean_is_exclusive(v___x_3798_)) as u8;
                    if v_isSharedCheck_3816_ == 0 {
                        v___x_3801_ = v___x_3798_;
                        v_isShared_3802_ = v_isSharedCheck_3816_;
                        state = 66;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3799_);
                        crate::leanh::lean_dec(v___x_3798_);
                        v___x_3801_ = crate::leanh::lean_box(0);
                        v_isShared_3802_ = v_isSharedCheck_3816_;
                        state = 66;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3796_);
                    crate::leanh::lean_dec_ref(v_proof_3793_);
                    crate::leanh::lean_del_object(v___x_3765_);
                    crate::leanh::lean_dec_ref(v_arg_3441_);
                    crate::leanh::lean_dec_ref(v_arg_3438_);
                    v_a_3817_ = crate::leanh::lean_ctor_get(v___x_3798_, 0);
                    v_isSharedCheck_3824_ = (!crate::leanh::lean_is_exclusive(v___x_3798_)) as u8;
                    if v_isSharedCheck_3824_ == 0 {
                        v___x_3819_ = v___x_3798_;
                        v_isShared_3820_ = v_isSharedCheck_3824_;
                        state = 70;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3817_);
                        crate::leanh::lean_dec(v___x_3798_);
                        v___x_3819_ = crate::leanh::lean_box(0);
                        v_isShared_3820_ = v_isSharedCheck_3824_;
                        state = 70;
                        continue;
                    }
                }
            }
            66 => {
                v___x_3803_ = crate::leanh::lean_box(0);
                v___x_3804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27_once), _init_l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___closed__27);
                v___x_3805_ = l_Lean_mkApp3(v___x_3804_, v_arg_3441_, v_arg_3438_, v_proof_3793_);
                v___x_3806_ = 0;
                if v_isShared_3797_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3796_, 1, v___x_3805_);
                    crate::leanh::lean_ctor_set(v___x_3796_, 0, v_a_3799_);
                    v___x_3808_ = v___x_3796_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_3815_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 1, v___x_3805_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3815_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_3794_,
                    );
                    v___x_3808_ = v_reuseFailAlloc_3815_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3808_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3806_,
                );
                if v_isShared_3766_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3765_, 0);
                    crate::leanh::lean_ctor_set(v___x_3765_, 1, v___x_3803_);
                    crate::leanh::lean_ctor_set(v___x_3765_, 0, v___x_3808_);
                    v___x_3810_ = v___x_3765_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_3814_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 1, v___x_3803_);
                    v___x_3810_ = v_reuseFailAlloc_3814_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_3802_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3801_, 0, v___x_3810_);
                    v___x_3812_ = v___x_3801_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_3813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
                    v___x_3812_ = v_reuseFailAlloc_3813_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                return v___x_3812_;
            }
            70 => {
                if v_isShared_3820_ == 0 {
                    v___x_3822_ = v___x_3819_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_3823_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
                    v___x_3822_ = v_reuseFailAlloc_3823_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                return v___x_3822_;
            }
            72 => {
                if v_isShared_3833_ == 0 {
                    v___x_3835_ = v___x_3832_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_3836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
                    v___x_3835_ = v_reuseFailAlloc_3836_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_3835_;
            }
            74 => {
                if v_isShared_3841_ == 0 {
                    v___x_3843_ = v___x_3840_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_3844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
                    v___x_3843_ = v_reuseFailAlloc_3844_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                return v___x_3843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows___boxed(
    mut v_e_3846_: *mut crate::leanh::LeanObject,
    mut v_infos_3847_: *mut crate::leanh::LeanObject,
    mut v_simpBody_3848_: *mut crate::leanh::LeanObject,
    mut v_a_3849_: *mut crate::leanh::LeanObject,
    mut v_a_3850_: *mut crate::leanh::LeanObject,
    mut v_a_3851_: *mut crate::leanh::LeanObject,
    mut v_a_3852_: *mut crate::leanh::LeanObject,
    mut v_a_3853_: *mut crate::leanh::LeanObject,
    mut v_a_3854_: *mut crate::leanh::LeanObject,
    mut v_a_3855_: *mut crate::leanh::LeanObject,
    mut v_a_3856_: *mut crate::leanh::LeanObject,
    mut v_a_3857_: *mut crate::leanh::LeanObject,
    mut v_a_3858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3859_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(
        v_e_3846_,
        v_infos_3847_,
        v_simpBody_3848_,
        v_a_3849_,
        v_a_3850_,
        v_a_3851_,
        v_a_3852_,
        v_a_3853_,
        v_a_3854_,
        v_a_3855_,
        v_a_3856_,
        v_a_3857_,
    );
    crate::leanh::lean_dec(v_a_3857_);
    crate::leanh::lean_dec_ref(v_a_3856_);
    crate::leanh::lean_dec(v_a_3855_);
    crate::leanh::lean_dec_ref(v_a_3854_);
    crate::leanh::lean_dec(v_a_3853_);
    crate::leanh::lean_dec_ref(v_a_3852_);
    crate::leanh::lean_dec(v_a_3851_);
    crate::leanh::lean_dec_ref(v_a_3850_);
    crate::leanh::lean_dec(v_a_3849_);
    return v_res_3859_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(
    mut v_f_3860_: *mut crate::leanh::LeanObject,
    mut v_a_3861_: *mut crate::leanh::LeanObject,
    mut v___y_3862_: *mut crate::leanh::LeanObject,
    mut v___y_3863_: *mut crate::leanh::LeanObject,
    mut v___y_3864_: *mut crate::leanh::LeanObject,
    mut v___y_3865_: *mut crate::leanh::LeanObject,
    mut v___y_3866_: *mut crate::leanh::LeanObject,
    mut v___y_3867_: *mut crate::leanh::LeanObject,
    mut v___y_3868_: *mut crate::leanh::LeanObject,
    mut v___y_3869_: *mut crate::leanh::LeanObject,
    mut v___y_3870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3872_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___redArg(v_f_3860_, v_a_3861_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
    return v___x_3872_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0___boxed(
    mut v_f_3873_: *mut crate::leanh::LeanObject,
    mut v_a_3874_: *mut crate::leanh::LeanObject,
    mut v___y_3875_: *mut crate::leanh::LeanObject,
    mut v___y_3876_: *mut crate::leanh::LeanObject,
    mut v___y_3877_: *mut crate::leanh::LeanObject,
    mut v___y_3878_: *mut crate::leanh::LeanObject,
    mut v___y_3879_: *mut crate::leanh::LeanObject,
    mut v___y_3880_: *mut crate::leanh::LeanObject,
    mut v___y_3881_: *mut crate::leanh::LeanObject,
    mut v___y_3882_: *mut crate::leanh::LeanObject,
    mut v___y_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3885_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows_spec__0_spec__0(v_f_3873_, v_a_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
    crate::leanh::lean_dec(v___y_3883_);
    crate::leanh::lean_dec_ref(v___y_3882_);
    crate::leanh::lean_dec(v___y_3881_);
    crate::leanh::lean_dec_ref(v___y_3880_);
    crate::leanh::lean_dec(v___y_3879_);
    crate::leanh::lean_dec_ref(v___y_3878_);
    crate::leanh::lean_dec(v___y_3877_);
    crate::leanh::lean_dec_ref(v___y_3876_);
    crate::leanh::lean_dec(v___y_3875_);
    return v_res_3885_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpArrowTelescope(
    mut v_simpBody_3893_: *mut crate::leanh::LeanObject,
    mut v_e_3894_: *mut crate::leanh::LeanObject,
    mut v_a_3895_: *mut crate::leanh::LeanObject,
    mut v_a_3896_: *mut crate::leanh::LeanObject,
    mut v_a_3897_: *mut crate::leanh::LeanObject,
    mut v_a_3898_: *mut crate::leanh::LeanObject,
    mut v_a_3899_: *mut crate::leanh::LeanObject,
    mut v_a_3900_: *mut crate::leanh::LeanObject,
    mut v_a_3901_: *mut crate::leanh::LeanObject,
    mut v_a_3902_: *mut crate::leanh::LeanObject,
    mut v_a_3903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3905_: u8 = 0;
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arrow_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infos_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3917_: u8 = 0;
    let mut v_fst_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3919_: u8 = 0;
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3927_: u8 = 0;
    let mut v_e_x27_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3930_: u8 = 0;
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3933_: u8 = 0;
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3959_: u8 = 0;
    let mut v_a_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3963_: u8 = 0;
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3967_: u8 = 0;
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut v_isSharedCheck_3969_: u8 = 0;
    let mut v_unused_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3971_: u8 = 0;
    let mut v_a_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3975_: u8 = 0;
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3979_: u8 = 0;
    let mut v_a_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3905_ = l_Lean_Expr_isArrow(v_e_3894_);
                if v___x_3905_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_3894_);
                    crate::leanh::lean_dec_ref(v_simpBody_3893_);
                    v___x_3906_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    crate::leanh::lean_ctor_set_uint8(v___x_3906_, 0 as u32, v___x_3905_);
                    crate::leanh::lean_ctor_set_uint8(v___x_3906_, 1 as u32, v___x_3905_);
                    v___x_3907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3907_, 0, v___x_3906_);
                    return v___x_3907_;
                } else {
                    crate::leanh::lean_inc_ref(v_e_3894_);
                    v___x_3908_ =
                        l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toArrow(
                            v_e_3894_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_,
                            v_a_3903_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3908_) == 0 {
                        v_a_3909_ = crate::leanh::lean_ctor_get(v___x_3908_, 0);
                        crate::leanh::lean_inc(v_a_3909_);
                        crate::leanh::lean_dec_ref_known(v___x_3908_, 1);
                        v_arrow_3910_ = crate::leanh::lean_ctor_get(v_a_3909_, 0);
                        crate::leanh::lean_inc_ref_n(v_arrow_3910_, 2);
                        v_infos_3911_ = crate::leanh::lean_ctor_get(v_a_3909_, 1);
                        crate::leanh::lean_inc(v_infos_3911_);
                        v_v_3912_ = crate::leanh::lean_ctor_get(v_a_3909_, 2);
                        crate::leanh::lean_inc(v_v_3912_);
                        crate::leanh::lean_dec(v_a_3909_);
                        v___x_3913_ =
                            l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpArrows(
                                v_arrow_3910_,
                                v_infos_3911_,
                                v_simpBody_3893_,
                                v_a_3895_,
                                v_a_3896_,
                                v_a_3897_,
                                v_a_3898_,
                                v_a_3899_,
                                v_a_3900_,
                                v_a_3901_,
                                v_a_3902_,
                                v_a_3903_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_3913_) == 0 {
                            v_a_3914_ = crate::leanh::lean_ctor_get(v___x_3913_, 0);
                            v_isSharedCheck_3971_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3913_)) as u8;
                            if v_isSharedCheck_3971_ == 0 {
                                v___x_3916_ = v___x_3913_;
                                v_isShared_3917_ = v_isSharedCheck_3971_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3914_);
                                crate::leanh::lean_dec(v___x_3913_);
                                v___x_3916_ = crate::leanh::lean_box(0);
                                v_isShared_3917_ = v_isSharedCheck_3971_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_v_3912_);
                            crate::leanh::lean_dec_ref(v_arrow_3910_);
                            crate::leanh::lean_dec_ref(v_e_3894_);
                            v_a_3972_ = crate::leanh::lean_ctor_get(v___x_3913_, 0);
                            v_isSharedCheck_3979_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3913_)) as u8;
                            if v_isSharedCheck_3979_ == 0 {
                                v___x_3974_ = v___x_3913_;
                                v_isShared_3975_ = v_isSharedCheck_3979_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3972_);
                                crate::leanh::lean_dec(v___x_3913_);
                                v___x_3974_ = crate::leanh::lean_box(0);
                                v_isShared_3975_ = v_isSharedCheck_3979_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3894_);
                        crate::leanh::lean_dec_ref(v_simpBody_3893_);
                        v_a_3980_ = crate::leanh::lean_ctor_get(v___x_3908_, 0);
                        v_isSharedCheck_3987_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3908_)) as u8;
                        if v_isSharedCheck_3987_ == 0 {
                            v___x_3982_ = v___x_3908_;
                            v_isShared_3983_ = v_isSharedCheck_3987_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3980_);
                            crate::leanh::lean_dec(v___x_3908_);
                            v___x_3982_ = crate::leanh::lean_box(0);
                            v_isShared_3983_ = v_isSharedCheck_3987_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3918_ = crate::leanh::lean_ctor_get(v_a_3914_, 0);
                crate::leanh::lean_inc(v_fst_3918_);
                if crate::leanh::lean_obj_tag(v_fst_3918_) == 0 {
                    crate::leanh::lean_dec(v_a_3914_);
                    crate::leanh::lean_dec(v_v_3912_);
                    crate::leanh::lean_dec_ref(v_arrow_3910_);
                    crate::leanh::lean_dec_ref(v_e_3894_);
                    v_contextDependent_3919_ =
                        crate::leanh::lean_ctor_get_uint8(v_fst_3918_, 1 as u32);
                    crate::leanh::lean_dec_ref_known(v_fst_3918_, 0);
                    v___x_3920_ =
                        l_Lean_Meta_Sym_Simp_mkRflResult(v___x_3905_, v_contextDependent_3919_);
                    if v_isShared_3917_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3916_, 0, v___x_3920_);
                        v___x_3922_ = v___x_3916_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
                        v___x_3922_ = v_reuseFailAlloc_3923_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3916_);
                    v_snd_3924_ = crate::leanh::lean_ctor_get(v_a_3914_, 1);
                    v_isSharedCheck_3969_ = (!crate::leanh::lean_is_exclusive(v_a_3914_)) as u8;
                    if v_isSharedCheck_3969_ == 0 {
                        v_unused_3970_ = crate::leanh::lean_ctor_get(v_a_3914_, 0);
                        crate::leanh::lean_dec(v_unused_3970_);
                        v___x_3926_ = v_a_3914_;
                        v_isShared_3927_ = v_isSharedCheck_3969_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3924_);
                        crate::leanh::lean_dec(v_a_3914_);
                        v___x_3926_ = crate::leanh::lean_box(0);
                        v_isShared_3927_ = v_isSharedCheck_3969_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3922_;
            }
            3 => {
                v_e_x27_3928_ = crate::leanh::lean_ctor_get(v_fst_3918_, 0);
                v_proof_3929_ = crate::leanh::lean_ctor_get(v_fst_3918_, 1);
                v_contextDependent_3930_ = crate::leanh::lean_ctor_get_uint8(
                    v_fst_3918_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                );
                v_isSharedCheck_3968_ = (!crate::leanh::lean_is_exclusive(v_fst_3918_)) as u8;
                if v_isSharedCheck_3968_ == 0 {
                    v___x_3932_ = v_fst_3918_;
                    v_isShared_3933_ = v_isSharedCheck_3968_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_proof_3929_);
                    crate::leanh::lean_inc(v_e_x27_3928_);
                    crate::leanh::lean_dec(v_fst_3918_);
                    v___x_3932_ = crate::leanh::lean_box(0);
                    v_isShared_3933_ = v_isSharedCheck_3968_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_e_x27_3928_);
                v___x_3934_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_toForall(
                    v_e_x27_3928_,
                    v_snd_3924_,
                    v_a_3898_,
                    v_a_3899_,
                    v_a_3900_,
                    v_a_3901_,
                    v_a_3902_,
                    v_a_3903_,
                );
                if crate::leanh::lean_obj_tag(v___x_3934_) == 0 {
                    v_a_3935_ = crate::leanh::lean_ctor_get(v___x_3934_, 0);
                    v_isSharedCheck_3959_ = (!crate::leanh::lean_is_exclusive(v___x_3934_)) as u8;
                    if v_isSharedCheck_3959_ == 0 {
                        v___x_3937_ = v___x_3934_;
                        v_isShared_3938_ = v_isSharedCheck_3959_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3935_);
                        crate::leanh::lean_dec(v___x_3934_);
                        v___x_3937_ = crate::leanh::lean_box(0);
                        v_isShared_3938_ = v_isSharedCheck_3959_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3932_);
                    crate::leanh::lean_dec_ref(v_proof_3929_);
                    crate::leanh::lean_dec_ref(v_e_x27_3928_);
                    crate::leanh::lean_del_object(v___x_3926_);
                    crate::leanh::lean_dec(v_v_3912_);
                    crate::leanh::lean_dec_ref(v_arrow_3910_);
                    crate::leanh::lean_dec_ref(v_e_3894_);
                    v_a_3960_ = crate::leanh::lean_ctor_get(v___x_3934_, 0);
                    v_isSharedCheck_3967_ = (!crate::leanh::lean_is_exclusive(v___x_3934_)) as u8;
                    if v_isSharedCheck_3967_ == 0 {
                        v___x_3962_ = v___x_3934_;
                        v_isShared_3963_ = v_isSharedCheck_3967_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3960_);
                        crate::leanh::lean_dec(v___x_3934_);
                        v___x_3962_ = crate::leanh::lean_box(0);
                        v_isShared_3963_ = v_isSharedCheck_3967_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_v_3912_);
                v___x_3939_ = l_Lean_mkSort(v_v_3912_);
                v___x_3940_ = l_Lean_Level_succ___override(v_v_3912_);
                v___x_3941_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__1;
                v___x_3942_ = crate::leanh::lean_box(0);
                if v_isShared_3927_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3926_, 1);
                    crate::leanh::lean_ctor_set(v___x_3926_, 1, v___x_3942_);
                    crate::leanh::lean_ctor_set(v___x_3926_, 0, v___x_3940_);
                    v___x_3944_ = v___x_3926_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3958_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3958_, 1, v___x_3942_);
                    v___x_3944_ = v_reuseFailAlloc_3958_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___x_3944_);
                v___x_3945_ = l_Lean_mkConst(v___x_3941_, v___x_3944_);
                v___x_3946_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope___closed__2;
                v___x_3947_ = l_Lean_mkConst(v___x_3946_, v___x_3944_);
                crate::leanh::lean_inc_ref(v_arrow_3910_);
                crate::leanh::lean_inc_ref_n(v___x_3939_, 3);
                crate::leanh::lean_inc_ref(v___x_3947_);
                v___x_3948_ = l_Lean_mkAppB(v___x_3947_, v___x_3939_, v_arrow_3910_);
                crate::leanh::lean_inc_ref(v_e_x27_3928_);
                crate::leanh::lean_inc_ref(v_e_3894_);
                crate::leanh::lean_inc_ref(v___x_3945_);
                v___x_3949_ = l_Lean_mkApp6(
                    v___x_3945_,
                    v___x_3939_,
                    v_e_3894_,
                    v_arrow_3910_,
                    v_e_x27_3928_,
                    v___x_3948_,
                    v_proof_3929_,
                );
                crate::leanh::lean_inc_n(v_a_3935_, 2);
                v___x_3950_ = l_Lean_mkAppB(v___x_3947_, v___x_3939_, v_a_3935_);
                v___x_3951_ = l_Lean_mkApp6(
                    v___x_3945_,
                    v___x_3939_,
                    v_e_3894_,
                    v_e_x27_3928_,
                    v_a_3935_,
                    v___x_3949_,
                    v___x_3950_,
                );
                if v_isShared_3933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3932_, 1, v___x_3951_);
                    crate::leanh::lean_ctor_set(v___x_3932_, 0, v_a_3935_);
                    v___x_3953_ = v___x_3932_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3957_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 1, v___x_3951_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3957_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_3930_,
                    );
                    v___x_3953_ = v_reuseFailAlloc_3957_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3953_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_3905_,
                );
                if v_isShared_3938_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3937_, 0, v___x_3953_);
                    v___x_3955_ = v___x_3937_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
                    v___x_3955_ = v_reuseFailAlloc_3956_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3955_;
            }
            9 => {
                if v_isShared_3963_ == 0 {
                    v___x_3965_ = v___x_3962_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
                    v___x_3965_ = v_reuseFailAlloc_3966_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3965_;
            }
            11 => {
                if v_isShared_3975_ == 0 {
                    v___x_3977_ = v___x_3974_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3978_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
                    v___x_3977_ = v_reuseFailAlloc_3978_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3977_;
            }
            13 => {
                if v_isShared_3983_ == 0 {
                    v___x_3985_ = v___x_3982_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3986_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
                    v___x_3985_ = v_reuseFailAlloc_3986_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpArrowTelescope___boxed(
    mut v_simpBody_3988_: *mut crate::leanh::LeanObject,
    mut v_e_3989_: *mut crate::leanh::LeanObject,
    mut v_a_3990_: *mut crate::leanh::LeanObject,
    mut v_a_3991_: *mut crate::leanh::LeanObject,
    mut v_a_3992_: *mut crate::leanh::LeanObject,
    mut v_a_3993_: *mut crate::leanh::LeanObject,
    mut v_a_3994_: *mut crate::leanh::LeanObject,
    mut v_a_3995_: *mut crate::leanh::LeanObject,
    mut v_a_3996_: *mut crate::leanh::LeanObject,
    mut v_a_3997_: *mut crate::leanh::LeanObject,
    mut v_a_3998_: *mut crate::leanh::LeanObject,
    mut v_a_3999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4000_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(
        v_simpBody_3988_,
        v_e_3989_,
        v_a_3990_,
        v_a_3991_,
        v_a_3992_,
        v_a_3993_,
        v_a_3994_,
        v_a_3995_,
        v_a_3996_,
        v_a_3997_,
        v_a_3998_,
    );
    crate::leanh::lean_dec(v_a_3998_);
    crate::leanh::lean_dec_ref(v_a_3997_);
    crate::leanh::lean_dec(v_a_3996_);
    crate::leanh::lean_dec_ref(v_a_3995_);
    crate::leanh::lean_dec(v_a_3994_);
    crate::leanh::lean_dec_ref(v_a_3993_);
    crate::leanh::lean_dec(v_a_3992_);
    crate::leanh::lean_dec_ref(v_a_3991_);
    crate::leanh::lean_dec(v_a_3990_);
    return v_res_4000_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(
    mut v_x_4001_: *mut crate::leanh::LeanObject,
    mut v_bi_4002_: u8,
    mut v_t_4003_: *mut crate::leanh::LeanObject,
    mut v_b_4004_: *mut crate::leanh::LeanObject,
    mut v___y_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4017_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4027_: u8 = 0;
    let mut v_a_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4031_: u8 = 0;
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4016_ = lean_st_ref_get(v___y_4006_);
                v_debug_4017_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4016_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_4016_);
                if v_debug_4017_ == 0 {
                    v___y_4013_ = v___y_4006_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_t_4003_);
                    v___x_4018_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_t_4003_,
                        v___y_4005_,
                        v___y_4006_,
                        v___y_4007_,
                        v___y_4008_,
                        v___y_4009_,
                        v___y_4010_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4018_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4018_, 1);
                        crate::leanh::lean_inc_ref(v_b_4004_);
                        v___x_4019_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_b_4004_,
                            v___y_4005_,
                            v___y_4006_,
                            v___y_4007_,
                            v___y_4008_,
                            v___y_4009_,
                            v___y_4010_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4019_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4019_, 1);
                            v___y_4013_ = v___y_4006_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_4004_);
                            crate::leanh::lean_dec_ref(v_t_4003_);
                            crate::leanh::lean_dec(v_x_4001_);
                            v_a_4020_ = crate::leanh::lean_ctor_get(v___x_4019_, 0);
                            v_isSharedCheck_4027_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4019_)) as u8;
                            if v_isSharedCheck_4027_ == 0 {
                                v___x_4022_ = v___x_4019_;
                                v_isShared_4023_ = v_isSharedCheck_4027_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4020_);
                                crate::leanh::lean_dec(v___x_4019_);
                                v___x_4022_ = crate::leanh::lean_box(0);
                                v_isShared_4023_ = v_isSharedCheck_4027_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4004_);
                        crate::leanh::lean_dec_ref(v_t_4003_);
                        crate::leanh::lean_dec(v_x_4001_);
                        v_a_4028_ = crate::leanh::lean_ctor_get(v___x_4018_, 0);
                        v_isSharedCheck_4035_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4018_)) as u8;
                        if v_isSharedCheck_4035_ == 0 {
                            v___x_4030_ = v___x_4018_;
                            v_isShared_4031_ = v_isSharedCheck_4035_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4028_);
                            crate::leanh::lean_dec(v___x_4018_);
                            v___x_4030_ = crate::leanh::lean_box(0);
                            v_isShared_4031_ = v_isSharedCheck_4035_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4014_ =
                    l_Lean_Expr_forallE___override(v_x_4001_, v_t_4003_, v_b_4004_, v_bi_4002_);
                v___x_4015_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_4014_, v___y_4013_);
                return v___x_4015_;
            }
            2 => {
                if v_isShared_4023_ == 0 {
                    v___x_4025_ = v___x_4022_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4026_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
                    v___x_4025_ = v_reuseFailAlloc_4026_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4025_;
            }
            4 => {
                if v_isShared_4031_ == 0 {
                    v___x_4033_ = v___x_4030_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4034_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
                    v___x_4033_ = v_reuseFailAlloc_4034_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg___boxed(
    mut v_x_4036_: *mut crate::leanh::LeanObject,
    mut v_bi_4037_: *mut crate::leanh::LeanObject,
    mut v_t_4038_: *mut crate::leanh::LeanObject,
    mut v_b_4039_: *mut crate::leanh::LeanObject,
    mut v___y_4040_: *mut crate::leanh::LeanObject,
    mut v___y_4041_: *mut crate::leanh::LeanObject,
    mut v___y_4042_: *mut crate::leanh::LeanObject,
    mut v___y_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4047_: u8 = 0;
    let mut v_res_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4047_ = (crate::leanh::lean_unbox(v_bi_4037_) as u8);
    v_res_4048_ =
        l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(
            v_x_4036_,
            v_bi_boxed_4047_,
            v_t_4038_,
            v_b_4039_,
            v___y_4040_,
            v___y_4041_,
            v___y_4042_,
            v___y_4043_,
            v___y_4044_,
            v___y_4045_,
        );
    crate::leanh::lean_dec(v___y_4045_);
    crate::leanh::lean_dec_ref(v___y_4044_);
    crate::leanh::lean_dec(v___y_4043_);
    crate::leanh::lean_dec_ref(v___y_4042_);
    crate::leanh::lean_dec(v___y_4041_);
    crate::leanh::lean_dec_ref(v___y_4040_);
    return v_res_4048_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(
    mut v_x_4049_: *mut crate::leanh::LeanObject,
    mut v_bi_4050_: u8,
    mut v_t_4051_: *mut crate::leanh::LeanObject,
    mut v_b_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
    mut v___y_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
    mut v___y_4059_: *mut crate::leanh::LeanObject,
    mut v___y_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4063_ =
        l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(
            v_x_4049_,
            v_bi_4050_,
            v_t_4051_,
            v_b_4052_,
            v___y_4056_,
            v___y_4057_,
            v___y_4058_,
            v___y_4059_,
            v___y_4060_,
            v___y_4061_,
        );
    return v___x_4063_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___boxed(
    mut v_x_4064_: *mut crate::leanh::LeanObject,
    mut v_bi_4065_: *mut crate::leanh::LeanObject,
    mut v_t_4066_: *mut crate::leanh::LeanObject,
    mut v_b_4067_: *mut crate::leanh::LeanObject,
    mut v___y_4068_: *mut crate::leanh::LeanObject,
    mut v___y_4069_: *mut crate::leanh::LeanObject,
    mut v___y_4070_: *mut crate::leanh::LeanObject,
    mut v___y_4071_: *mut crate::leanh::LeanObject,
    mut v___y_4072_: *mut crate::leanh::LeanObject,
    mut v___y_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
    mut v___y_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4078_: u8 = 0;
    let mut v_res_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4078_ = (crate::leanh::lean_unbox(v_bi_4065_) as u8);
    v_res_4079_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0(
        v_x_4064_,
        v_bi_boxed_4078_,
        v_t_4066_,
        v_b_4067_,
        v___y_4068_,
        v___y_4069_,
        v___y_4070_,
        v___y_4071_,
        v___y_4072_,
        v___y_4073_,
        v___y_4074_,
        v___y_4075_,
        v___y_4076_,
    );
    crate::leanh::lean_dec(v___y_4076_);
    crate::leanh::lean_dec_ref(v___y_4075_);
    crate::leanh::lean_dec(v___y_4074_);
    crate::leanh::lean_dec_ref(v___y_4073_);
    crate::leanh::lean_dec(v___y_4072_);
    crate::leanh::lean_dec_ref(v___y_4071_);
    crate::leanh::lean_dec(v___y_4070_);
    crate::leanh::lean_dec_ref(v___y_4069_);
    crate::leanh::lean_dec(v___y_4068_);
    return v_res_4079_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4080_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_4080_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(
    mut v_msg_4085_: *mut crate::leanh::LeanObject,
    mut v___y_4086_: *mut crate::leanh::LeanObject,
    mut v___y_4087_: *mut crate::leanh::LeanObject,
    mut v___y_4088_: *mut crate::leanh::LeanObject,
    mut v___y_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v_toFunctor_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___f_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4125_: u8 = 0;
    let mut v_toFunctor_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4132_: u8 = 0;
    let mut v___f_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_23189__overap_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_unused_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4158_: u8 = 0;
    let mut v_unused_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4162_: u8 = 0;
    let mut v_unused_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut v_unused_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4096_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0_once
                    ),
                    _init_l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__0,
                );
                v___x_4097_ = l_StateRefT_x27_instMonad___redArg(v___x_4096_);
                v_toApplicative_4098_ = crate::leanh::lean_ctor_get(v___x_4097_, 0);
                v_isSharedCheck_4164_ = (!crate::leanh::lean_is_exclusive(v___x_4097_)) as u8;
                if v_isSharedCheck_4164_ == 0 {
                    v_unused_4165_ = crate::leanh::lean_ctor_get(v___x_4097_, 1);
                    crate::leanh::lean_dec(v_unused_4165_);
                    v___x_4100_ = v___x_4097_;
                    v_isShared_4101_ = v_isSharedCheck_4164_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4098_);
                    crate::leanh::lean_dec(v___x_4097_);
                    v___x_4100_ = crate::leanh::lean_box(0);
                    v_isShared_4101_ = v_isSharedCheck_4164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4102_ = crate::leanh::lean_ctor_get(v_toApplicative_4098_, 0);
                v_toSeq_4103_ = crate::leanh::lean_ctor_get(v_toApplicative_4098_, 2);
                v_toSeqLeft_4104_ = crate::leanh::lean_ctor_get(v_toApplicative_4098_, 3);
                v_toSeqRight_4105_ = crate::leanh::lean_ctor_get(v_toApplicative_4098_, 4);
                v_isSharedCheck_4162_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4098_)) as u8;
                if v_isSharedCheck_4162_ == 0 {
                    v_unused_4163_ = crate::leanh::lean_ctor_get(v_toApplicative_4098_, 1);
                    crate::leanh::lean_dec(v_unused_4163_);
                    v___x_4107_ = v_toApplicative_4098_;
                    v_isShared_4108_ = v_isSharedCheck_4162_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4105_);
                    crate::leanh::lean_inc(v_toSeqLeft_4104_);
                    crate::leanh::lean_inc(v_toSeq_4103_);
                    crate::leanh::lean_inc(v_toFunctor_4102_);
                    crate::leanh::lean_dec(v_toApplicative_4098_);
                    v___x_4107_ = crate::leanh::lean_box(0);
                    v_isShared_4108_ = v_isSharedCheck_4162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4109_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__1;
                v___f_4110_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_4102_);
                v___f_4111_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4111_, 0, v_toFunctor_4102_);
                v___f_4112_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4112_, 0, v_toFunctor_4102_);
                v___x_4113_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4113_, 0, v___f_4111_);
                crate::leanh::lean_ctor_set(v___x_4113_, 1, v___f_4112_);
                v___f_4114_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4114_, 0, v_toSeqRight_4105_);
                v___f_4115_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4115_, 0, v_toSeqLeft_4104_);
                v___f_4116_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4116_, 0, v_toSeq_4103_);
                if v_isShared_4108_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4107_, 4, v___f_4114_);
                    crate::leanh::lean_ctor_set(v___x_4107_, 3, v___f_4115_);
                    crate::leanh::lean_ctor_set(v___x_4107_, 2, v___f_4116_);
                    crate::leanh::lean_ctor_set(v___x_4107_, 1, v___f_4109_);
                    crate::leanh::lean_ctor_set(v___x_4107_, 0, v___x_4113_);
                    v___x_4118_ = v___x_4107_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4161_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 1, v___f_4109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 2, v___f_4116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 3, v___f_4115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 4, v___f_4114_);
                    v___x_4118_ = v_reuseFailAlloc_4161_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4101_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4100_, 1, v___f_4110_);
                    crate::leanh::lean_ctor_set(v___x_4100_, 0, v___x_4118_);
                    v___x_4120_ = v___x_4100_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4160_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4160_, 1, v___f_4110_);
                    v___x_4120_ = v_reuseFailAlloc_4160_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4121_ = l_StateRefT_x27_instMonad___redArg(v___x_4120_);
                v_toApplicative_4122_ = crate::leanh::lean_ctor_get(v___x_4121_, 0);
                v_isSharedCheck_4158_ = (!crate::leanh::lean_is_exclusive(v___x_4121_)) as u8;
                if v_isSharedCheck_4158_ == 0 {
                    v_unused_4159_ = crate::leanh::lean_ctor_get(v___x_4121_, 1);
                    crate::leanh::lean_dec(v_unused_4159_);
                    v___x_4124_ = v___x_4121_;
                    v_isShared_4125_ = v_isSharedCheck_4158_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4122_);
                    crate::leanh::lean_dec(v___x_4121_);
                    v___x_4124_ = crate::leanh::lean_box(0);
                    v_isShared_4125_ = v_isSharedCheck_4158_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_4126_ = crate::leanh::lean_ctor_get(v_toApplicative_4122_, 0);
                v_toSeq_4127_ = crate::leanh::lean_ctor_get(v_toApplicative_4122_, 2);
                v_toSeqLeft_4128_ = crate::leanh::lean_ctor_get(v_toApplicative_4122_, 3);
                v_toSeqRight_4129_ = crate::leanh::lean_ctor_get(v_toApplicative_4122_, 4);
                v_isSharedCheck_4156_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4122_)) as u8;
                if v_isSharedCheck_4156_ == 0 {
                    v_unused_4157_ = crate::leanh::lean_ctor_get(v_toApplicative_4122_, 1);
                    crate::leanh::lean_dec(v_unused_4157_);
                    v___x_4131_ = v_toApplicative_4122_;
                    v_isShared_4132_ = v_isSharedCheck_4156_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4129_);
                    crate::leanh::lean_inc(v_toSeqLeft_4128_);
                    crate::leanh::lean_inc(v_toSeq_4127_);
                    crate::leanh::lean_inc(v_toFunctor_4126_);
                    crate::leanh::lean_dec(v_toApplicative_4122_);
                    v___x_4131_ = crate::leanh::lean_box(0);
                    v_isShared_4132_ = v_isSharedCheck_4156_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_4133_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__3;
                v___f_4134_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_4126_);
                v___f_4135_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4135_, 0, v_toFunctor_4126_);
                v___f_4136_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4136_, 0, v_toFunctor_4126_);
                v___x_4137_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4137_, 0, v___f_4135_);
                crate::leanh::lean_ctor_set(v___x_4137_, 1, v___f_4136_);
                v___f_4138_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4138_, 0, v_toSeqRight_4129_);
                v___f_4139_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4139_, 0, v_toSeqLeft_4128_);
                v___f_4140_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4140_, 0, v_toSeq_4127_);
                if v_isShared_4132_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4131_, 4, v___f_4138_);
                    crate::leanh::lean_ctor_set(v___x_4131_, 3, v___f_4139_);
                    crate::leanh::lean_ctor_set(v___x_4131_, 2, v___f_4140_);
                    crate::leanh::lean_ctor_set(v___x_4131_, 1, v___f_4133_);
                    crate::leanh::lean_ctor_set(v___x_4131_, 0, v___x_4137_);
                    v___x_4142_ = v___x_4131_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 1, v___f_4133_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 2, v___f_4140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 3, v___f_4139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 4, v___f_4138_);
                    v___x_4142_ = v_reuseFailAlloc_4155_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4125_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4124_, 1, v___f_4134_);
                    crate::leanh::lean_ctor_set(v___x_4124_, 0, v___x_4142_);
                    v___x_4144_ = v___x_4124_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4154_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4142_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4154_, 1, v___f_4134_);
                    v___x_4144_ = v_reuseFailAlloc_4154_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4145_ = l_StateRefT_x27_instMonad___redArg(v___x_4144_);
                v___x_4146_ = l_ReaderT_instMonad___redArg(v___x_4145_);
                v___x_4147_ = l_StateRefT_x27_instMonad___redArg(v___x_4146_);
                v___x_4148_ = l_ReaderT_instMonad___redArg(v___x_4147_);
                v___x_4149_ = l_ReaderT_instMonad___redArg(v___x_4148_);
                v___x_4150_ = l_Lean_instInhabitedExpr;
                v___x_4151_ = l_instInhabitedOfMonad___redArg(v___x_4149_, v___x_4150_);
                v___x_23189__overap_4152_ = lean_panic_fn_borrowed(v___x_4151_, v_msg_4085_);
                crate::leanh::lean_dec(v___x_4151_);
                crate::leanh::lean_inc(v___y_4094_);
                crate::leanh::lean_inc_ref(v___y_4093_);
                crate::leanh::lean_inc(v___y_4092_);
                crate::leanh::lean_inc_ref(v___y_4091_);
                crate::leanh::lean_inc(v___y_4090_);
                crate::leanh::lean_inc_ref(v___y_4089_);
                crate::leanh::lean_inc(v___y_4088_);
                crate::leanh::lean_inc_ref(v___y_4087_);
                crate::leanh::lean_inc(v___y_4086_);
                v___x_4153_ = crate::leanh::lean_apply_10(
                    v___x_23189__overap_4152_,
                    v___y_4086_,
                    v___y_4087_,
                    v___y_4088_,
                    v___y_4089_,
                    v___y_4090_,
                    v___y_4091_,
                    v___y_4092_,
                    v___y_4093_,
                    v___y_4094_,
                    crate::leanh::lean_box(0),
                );
                return v___x_4153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1___boxed(
    mut v_msg_4166_: *mut crate::leanh::LeanObject,
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
    let mut v_res_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4177_ = l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(
        v_msg_4166_,
        v___y_4167_,
        v___y_4168_,
        v___y_4169_,
        v___y_4170_,
        v___y_4171_,
        v___y_4172_,
        v___y_4173_,
        v___y_4174_,
        v___y_4175_,
    );
    crate::leanh::lean_dec(v___y_4175_);
    crate::leanh::lean_dec_ref(v___y_4174_);
    crate::leanh::lean_dec(v___y_4173_);
    crate::leanh::lean_dec_ref(v___y_4172_);
    crate::leanh::lean_dec(v___y_4171_);
    crate::leanh::lean_dec_ref(v___y_4170_);
    crate::leanh::lean_dec(v___y_4169_);
    crate::leanh::lean_dec_ref(v___y_4168_);
    crate::leanh::lean_dec(v___y_4167_);
    return v_res_4177_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4184_ = l_Lean_Meta_Sym_Simp_simpArrow___closed__4;
    v___x_4185_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_4186_ = crate::leanh::lean_unsigned_to_nat(160);
    v___x_4187_ = l_Lean_Meta_Sym_Simp_simpArrow___closed__3;
    v___x_4188_ = l_Lean_Meta_Sym_Simp_simpArrow___closed__2;
    v___x_4189_ = l_mkPanicMessageWithDecl(
        v___x_4188_,
        v___x_4187_,
        v___x_4186_,
        v___x_4185_,
        v___x_4184_,
    );
    return v___x_4189_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpArrow(
    mut v_e_4196_: *mut crate::leanh::LeanObject,
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_a_4198_: *mut crate::leanh::LeanObject,
    mut v_a_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_a_4201_: *mut crate::leanh::LeanObject,
    mut v_a_4202_: *mut crate::leanh::LeanObject,
    mut v_a_4203_: *mut crate::leanh::LeanObject,
    mut v_a_4204_: *mut crate::leanh::LeanObject,
    mut v_a_4205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4210_: u8 = 0;
    let mut v___y_4211_: u8 = 0;
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4217_: u8 = 0;
    let mut v___y_4218_: u8 = 0;
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4224_: u8 = 0;
    let mut v___y_4225_: u8 = 0;
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4236_: u8 = 0;
    let mut v___y_4238_: u8 = 0;
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4243_: u8 = 0;
    let mut v_contextDependent_4244_: u8 = 0;
    let mut v_contextDependent_4245_: u8 = 0;
    let mut v_e_x27_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4248_: u8 = 0;
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: u8 = 0;
    let mut v___y_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4268_: u8 = 0;
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_binderName_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4276_: u8 = 0;
    let mut v___y_4278_: u8 = 0;
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: u8 = 0;
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut v_a_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4299_: u8 = 0;
    let mut v_e_x27_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4302_: u8 = 0;
    let mut v_contextDependent_4303_: u8 = 0;
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: u8 = 0;
    let mut v___y_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4323_: u8 = 0;
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4327_: u8 = 0;
    let mut v_binderName_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4331_: u8 = 0;
    let mut v___y_4333_: u8 = 0;
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    let mut v___x_4336_: u8 = 0;
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_a_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4350_: u8 = 0;
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4354_: u8 = 0;
    let mut v_e_x27_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4357_: u8 = 0;
    let mut v_e_x27_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4360_: u8 = 0;
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: u8 = 0;
    let mut v___y_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut v_binderName_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4388_: u8 = 0;
    let mut v___y_4390_: u8 = 0;
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: u8 = 0;
    let mut v___x_4393_: u8 = 0;
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4399_: u8 = 0;
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4403_: u8 = 0;
    let mut v_a_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4407_: u8 = 0;
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4411_: u8 = 0;
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_p_4228_ = l_Lean_Expr_bindingDomain_x21(v_e_4196_);
                crate::leanh::lean_inc(v_a_4205_);
                crate::leanh::lean_inc_ref(v_a_4204_);
                crate::leanh::lean_inc(v_a_4203_);
                crate::leanh::lean_inc_ref(v_a_4202_);
                crate::leanh::lean_inc(v_a_4201_);
                crate::leanh::lean_inc_ref(v_a_4200_);
                crate::leanh::lean_inc(v_a_4199_);
                crate::leanh::lean_inc_ref(v_a_4198_);
                crate::leanh::lean_inc(v_a_4197_);
                crate::leanh::lean_inc_ref(v_p_4228_);
                v___x_4229_ = lean_sym_simp(
                    v_p_4228_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_,
                    v_a_4203_, v_a_4204_, v_a_4205_,
                );
                if crate::leanh::lean_obj_tag(v___x_4229_) == 0 {
                    v_a_4230_ = crate::leanh::lean_ctor_get(v___x_4229_, 0);
                    crate::leanh::lean_inc(v_a_4230_);
                    crate::leanh::lean_dec_ref_known(v___x_4229_, 1);
                    v_q_4231_ = l_Lean_Expr_bindingBody_x21(v_e_4196_);
                    crate::leanh::lean_inc(v_a_4205_);
                    crate::leanh::lean_inc_ref(v_a_4204_);
                    crate::leanh::lean_inc(v_a_4203_);
                    crate::leanh::lean_inc_ref(v_a_4202_);
                    crate::leanh::lean_inc(v_a_4201_);
                    crate::leanh::lean_inc_ref(v_a_4200_);
                    crate::leanh::lean_inc(v_a_4199_);
                    crate::leanh::lean_inc_ref(v_a_4198_);
                    crate::leanh::lean_inc(v_a_4197_);
                    crate::leanh::lean_inc_ref(v_q_4231_);
                    v___x_4232_ = lean_sym_simp(
                        v_q_4231_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_,
                        v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4232_) == 0 {
                        v_a_4233_ = crate::leanh::lean_ctor_get(v___x_4232_, 0);
                        v_isSharedCheck_4412_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4232_)) as u8;
                        if v_isSharedCheck_4412_ == 0 {
                            v___x_4235_ = v___x_4232_;
                            v_isShared_4236_ = v_isSharedCheck_4412_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4233_);
                            crate::leanh::lean_dec(v___x_4232_);
                            v___x_4235_ = crate::leanh::lean_box(0);
                            v_isShared_4236_ = v_isSharedCheck_4412_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_q_4231_);
                        crate::leanh::lean_dec(v_a_4230_);
                        crate::leanh::lean_dec_ref(v_p_4228_);
                        crate::leanh::lean_dec_ref(v_e_4196_);
                        return v___x_4232_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_4228_);
                    crate::leanh::lean_dec_ref(v_e_4196_);
                    return v___x_4229_;
                }
            }
            1 => {
                v___x_4212_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4212_, 0, v___y_4209_);
                crate::leanh::lean_ctor_set(v___x_4212_, 1, v___y_4208_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4212_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_4210_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4212_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_4211_,
                );
                v___x_4213_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4213_, 0, v___x_4212_);
                return v___x_4213_;
            }
            2 => {
                v___x_4219_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4219_, 0, v___y_4216_);
                crate::leanh::lean_ctor_set(v___x_4219_, 1, v___y_4215_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4219_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_4217_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4219_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_4218_,
                );
                v___x_4220_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4220_, 0, v___x_4219_);
                return v___x_4220_;
            }
            3 => {
                v___x_4226_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4226_, 0, v___y_4223_);
                crate::leanh::lean_ctor_set(v___x_4226_, 1, v___y_4222_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4226_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_4224_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4226_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_4225_,
                );
                v___x_4227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4227_, 0, v___x_4226_);
                return v___x_4227_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_4230_) == 0 {
                    if crate::leanh::lean_obj_tag(v_a_4233_) == 0 {
                        crate::leanh::lean_dec_ref(v_q_4231_);
                        crate::leanh::lean_dec_ref(v_p_4228_);
                        crate::leanh::lean_dec_ref(v_e_4196_);
                        v_contextDependent_4243_ =
                            crate::leanh::lean_ctor_get_uint8(v_a_4230_, 1 as u32);
                        crate::leanh::lean_dec_ref_known(v_a_4230_, 0);
                        if v_contextDependent_4243_ == 0 {
                            v_contextDependent_4244_ =
                                crate::leanh::lean_ctor_get_uint8(v_a_4233_, 1 as u32);
                            crate::leanh::lean_dec_ref_known(v_a_4233_, 0);
                            v___y_4238_ = v_contextDependent_4244_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_4233_, 0);
                            v___y_4238_ = v_contextDependent_4243_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4235_);
                        v_contextDependent_4245_ =
                            crate::leanh::lean_ctor_get_uint8(v_a_4230_, 1 as u32);
                        crate::leanh::lean_dec_ref_known(v_a_4230_, 0);
                        v_e_x27_4246_ = crate::leanh::lean_ctor_get(v_a_4233_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_4246_);
                        v_proof_4247_ = crate::leanh::lean_ctor_get(v_a_4233_, 1);
                        crate::leanh::lean_inc_ref(v_proof_4247_);
                        v_contextDependent_4248_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_4233_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v_a_4233_, 2);
                        crate::leanh::lean_inc_ref(v_p_4228_);
                        v___x_4249_ = l_Lean_Meta_Sym_getLevel___redArg(
                            v_p_4228_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4249_) == 0 {
                            v_a_4250_ = crate::leanh::lean_ctor_get(v___x_4249_, 0);
                            crate::leanh::lean_inc(v_a_4250_);
                            crate::leanh::lean_dec_ref_known(v___x_4249_, 1);
                            crate::leanh::lean_inc_ref(v_q_4231_);
                            v___x_4251_ = l_Lean_Meta_Sym_getLevel___redArg(
                                v_q_4231_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4251_) == 0 {
                                v_a_4252_ = crate::leanh::lean_ctor_get(v___x_4251_, 0);
                                crate::leanh::lean_inc(v_a_4252_);
                                crate::leanh::lean_dec_ref_known(v___x_4251_, 1);
                                if crate::leanh::lean_obj_tag(v_e_4196_) == 7 {
                                    v_binderName_4273_ = crate::leanh::lean_ctor_get(v_e_4196_, 0);
                                    v_binderType_4274_ = crate::leanh::lean_ctor_get(v_e_4196_, 1);
                                    v_body_4275_ = crate::leanh::lean_ctor_get(v_e_4196_, 2);
                                    v_binderInfo_4276_ = crate::leanh::lean_ctor_get_uint8(
                                        v_e_4196_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    v___x_4280_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_4274_, v_p_4228_);
                                    if v___x_4280_ == 0 {
                                        v___y_4278_ = v___x_4280_;
                                        state = 11;
                                        continue;
                                    } else {
                                        v___x_4281_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_4275_, v_e_x27_4246_);
                                        v___y_4278_ = v___x_4281_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_e_4196_);
                                    v___x_4282_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_Simp_simpArrow___closed__5
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once
                                        ),
                                        _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5,
                                    );
                                    v___x_4283_ =
                                        l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(
                                            v___x_4282_,
                                            v_a_4197_,
                                            v_a_4198_,
                                            v_a_4199_,
                                            v_a_4200_,
                                            v_a_4201_,
                                            v_a_4202_,
                                            v_a_4203_,
                                            v_a_4204_,
                                            v_a_4205_,
                                        );
                                    v___y_4263_ = v___x_4283_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4250_);
                                crate::leanh::lean_dec_ref(v_proof_4247_);
                                crate::leanh::lean_dec_ref(v_e_x27_4246_);
                                crate::leanh::lean_dec_ref(v_q_4231_);
                                crate::leanh::lean_dec_ref(v_p_4228_);
                                crate::leanh::lean_dec_ref(v_e_4196_);
                                v_a_4284_ = crate::leanh::lean_ctor_get(v___x_4251_, 0);
                                v_isSharedCheck_4291_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4251_)) as u8;
                                if v_isSharedCheck_4291_ == 0 {
                                    v___x_4286_ = v___x_4251_;
                                    v_isShared_4287_ = v_isSharedCheck_4291_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4284_);
                                    crate::leanh::lean_dec(v___x_4251_);
                                    v___x_4286_ = crate::leanh::lean_box(0);
                                    v_isShared_4287_ = v_isSharedCheck_4291_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_proof_4247_);
                            crate::leanh::lean_dec_ref(v_e_x27_4246_);
                            crate::leanh::lean_dec_ref(v_q_4231_);
                            crate::leanh::lean_dec_ref(v_p_4228_);
                            crate::leanh::lean_dec_ref(v_e_4196_);
                            v_a_4292_ = crate::leanh::lean_ctor_get(v___x_4249_, 0);
                            v_isSharedCheck_4299_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4249_)) as u8;
                            if v_isSharedCheck_4299_ == 0 {
                                v___x_4294_ = v___x_4249_;
                                v_isShared_4295_ = v_isSharedCheck_4299_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4292_);
                                crate::leanh::lean_dec(v___x_4249_);
                                v___x_4294_ = crate::leanh::lean_box(0);
                                v_isShared_4295_ = v_isSharedCheck_4299_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4235_);
                    if crate::leanh::lean_obj_tag(v_a_4233_) == 0 {
                        v_e_x27_4300_ = crate::leanh::lean_ctor_get(v_a_4230_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_4300_);
                        v_proof_4301_ = crate::leanh::lean_ctor_get(v_a_4230_, 1);
                        crate::leanh::lean_inc_ref(v_proof_4301_);
                        v_contextDependent_4302_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_4230_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v_a_4230_, 2);
                        v_contextDependent_4303_ =
                            crate::leanh::lean_ctor_get_uint8(v_a_4233_, 1 as u32);
                        crate::leanh::lean_dec_ref_known(v_a_4233_, 0);
                        crate::leanh::lean_inc_ref(v_p_4228_);
                        v___x_4304_ = l_Lean_Meta_Sym_getLevel___redArg(
                            v_p_4228_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4304_) == 0 {
                            v_a_4305_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                            crate::leanh::lean_inc(v_a_4305_);
                            crate::leanh::lean_dec_ref_known(v___x_4304_, 1);
                            crate::leanh::lean_inc_ref(v_q_4231_);
                            v___x_4306_ = l_Lean_Meta_Sym_getLevel___redArg(
                                v_q_4231_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4306_) == 0 {
                                v_a_4307_ = crate::leanh::lean_ctor_get(v___x_4306_, 0);
                                crate::leanh::lean_inc(v_a_4307_);
                                crate::leanh::lean_dec_ref_known(v___x_4306_, 1);
                                if crate::leanh::lean_obj_tag(v_e_4196_) == 7 {
                                    v_binderName_4328_ = crate::leanh::lean_ctor_get(v_e_4196_, 0);
                                    v_binderType_4329_ = crate::leanh::lean_ctor_get(v_e_4196_, 1);
                                    v_body_4330_ = crate::leanh::lean_ctor_get(v_e_4196_, 2);
                                    v_binderInfo_4331_ = crate::leanh::lean_ctor_get_uint8(
                                        v_e_4196_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    v___x_4335_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_4329_, v_e_x27_4300_);
                                    if v___x_4335_ == 0 {
                                        v___y_4333_ = v___x_4335_;
                                        state = 20;
                                        continue;
                                    } else {
                                        v___x_4336_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_4330_, v_q_4231_);
                                        v___y_4333_ = v___x_4336_;
                                        state = 20;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_e_4196_);
                                    v___x_4337_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_Simp_simpArrow___closed__5
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once
                                        ),
                                        _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5,
                                    );
                                    v___x_4338_ =
                                        l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(
                                            v___x_4337_,
                                            v_a_4197_,
                                            v_a_4198_,
                                            v_a_4199_,
                                            v_a_4200_,
                                            v_a_4201_,
                                            v_a_4202_,
                                            v_a_4203_,
                                            v_a_4204_,
                                            v_a_4205_,
                                        );
                                    v___y_4318_ = v___x_4338_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4305_);
                                crate::leanh::lean_dec_ref(v_proof_4301_);
                                crate::leanh::lean_dec_ref(v_e_x27_4300_);
                                crate::leanh::lean_dec_ref(v_q_4231_);
                                crate::leanh::lean_dec_ref(v_p_4228_);
                                crate::leanh::lean_dec_ref(v_e_4196_);
                                v_a_4339_ = crate::leanh::lean_ctor_get(v___x_4306_, 0);
                                v_isSharedCheck_4346_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4306_)) as u8;
                                if v_isSharedCheck_4346_ == 0 {
                                    v___x_4341_ = v___x_4306_;
                                    v_isShared_4342_ = v_isSharedCheck_4346_;
                                    state = 21;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4339_);
                                    crate::leanh::lean_dec(v___x_4306_);
                                    v___x_4341_ = crate::leanh::lean_box(0);
                                    v_isShared_4342_ = v_isSharedCheck_4346_;
                                    state = 21;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_proof_4301_);
                            crate::leanh::lean_dec_ref(v_e_x27_4300_);
                            crate::leanh::lean_dec_ref(v_q_4231_);
                            crate::leanh::lean_dec_ref(v_p_4228_);
                            crate::leanh::lean_dec_ref(v_e_4196_);
                            v_a_4347_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                            v_isSharedCheck_4354_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4304_)) as u8;
                            if v_isSharedCheck_4354_ == 0 {
                                v___x_4349_ = v___x_4304_;
                                v_isShared_4350_ = v_isSharedCheck_4354_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4347_);
                                crate::leanh::lean_dec(v___x_4304_);
                                v___x_4349_ = crate::leanh::lean_box(0);
                                v_isShared_4350_ = v_isSharedCheck_4354_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        v_e_x27_4355_ = crate::leanh::lean_ctor_get(v_a_4230_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_4355_);
                        v_proof_4356_ = crate::leanh::lean_ctor_get(v_a_4230_, 1);
                        crate::leanh::lean_inc_ref(v_proof_4356_);
                        v_contextDependent_4357_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_4230_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v_a_4230_, 2);
                        v_e_x27_4358_ = crate::leanh::lean_ctor_get(v_a_4233_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_4358_);
                        v_proof_4359_ = crate::leanh::lean_ctor_get(v_a_4233_, 1);
                        crate::leanh::lean_inc_ref(v_proof_4359_);
                        v_contextDependent_4360_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_4233_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v_a_4233_, 2);
                        crate::leanh::lean_inc_ref(v_p_4228_);
                        v___x_4361_ = l_Lean_Meta_Sym_getLevel___redArg(
                            v_p_4228_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4361_) == 0 {
                            v_a_4362_ = crate::leanh::lean_ctor_get(v___x_4361_, 0);
                            crate::leanh::lean_inc(v_a_4362_);
                            crate::leanh::lean_dec_ref_known(v___x_4361_, 1);
                            crate::leanh::lean_inc_ref(v_q_4231_);
                            v___x_4363_ = l_Lean_Meta_Sym_getLevel___redArg(
                                v_q_4231_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4363_) == 0 {
                                v_a_4364_ = crate::leanh::lean_ctor_get(v___x_4363_, 0);
                                crate::leanh::lean_inc(v_a_4364_);
                                crate::leanh::lean_dec_ref_known(v___x_4363_, 1);
                                if crate::leanh::lean_obj_tag(v_e_4196_) == 7 {
                                    v_binderName_4385_ = crate::leanh::lean_ctor_get(v_e_4196_, 0);
                                    v_binderType_4386_ = crate::leanh::lean_ctor_get(v_e_4196_, 1);
                                    v_body_4387_ = crate::leanh::lean_ctor_get(v_e_4196_, 2);
                                    v_binderInfo_4388_ = crate::leanh::lean_ctor_get_uint8(
                                        v_e_4196_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    v___x_4392_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_binderType_4386_, v_e_x27_4355_);
                                    if v___x_4392_ == 0 {
                                        v___y_4390_ = v___x_4392_;
                                        state = 29;
                                        continue;
                                    } else {
                                        v___x_4393_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_body_4387_, v_e_x27_4358_);
                                        v___y_4390_ = v___x_4393_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_e_4196_);
                                    v___x_4394_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_Simp_simpArrow___closed__5
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_Simp_simpArrow___closed__5_once
                                        ),
                                        _init_l_Lean_Meta_Sym_Simp_simpArrow___closed__5,
                                    );
                                    v___x_4395_ =
                                        l_panic___at___00Lean_Meta_Sym_Simp_simpArrow_spec__1(
                                            v___x_4394_,
                                            v_a_4197_,
                                            v_a_4198_,
                                            v_a_4199_,
                                            v_a_4200_,
                                            v_a_4201_,
                                            v_a_4202_,
                                            v_a_4203_,
                                            v_a_4204_,
                                            v_a_4205_,
                                        );
                                    v___y_4375_ = v___x_4395_;
                                    state = 26;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4362_);
                                crate::leanh::lean_dec_ref(v_proof_4359_);
                                crate::leanh::lean_dec_ref(v_e_x27_4358_);
                                crate::leanh::lean_dec_ref(v_proof_4356_);
                                crate::leanh::lean_dec_ref(v_e_x27_4355_);
                                crate::leanh::lean_dec_ref(v_q_4231_);
                                crate::leanh::lean_dec_ref(v_p_4228_);
                                crate::leanh::lean_dec_ref(v_e_4196_);
                                v_a_4396_ = crate::leanh::lean_ctor_get(v___x_4363_, 0);
                                v_isSharedCheck_4403_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4363_)) as u8;
                                if v_isSharedCheck_4403_ == 0 {
                                    v___x_4398_ = v___x_4363_;
                                    v_isShared_4399_ = v_isSharedCheck_4403_;
                                    state = 30;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4396_);
                                    crate::leanh::lean_dec(v___x_4363_);
                                    v___x_4398_ = crate::leanh::lean_box(0);
                                    v_isShared_4399_ = v_isSharedCheck_4403_;
                                    state = 30;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_proof_4359_);
                            crate::leanh::lean_dec_ref(v_e_x27_4358_);
                            crate::leanh::lean_dec_ref(v_proof_4356_);
                            crate::leanh::lean_dec_ref(v_e_x27_4355_);
                            crate::leanh::lean_dec_ref(v_q_4231_);
                            crate::leanh::lean_dec_ref(v_p_4228_);
                            crate::leanh::lean_dec_ref(v_e_4196_);
                            v_a_4404_ = crate::leanh::lean_ctor_get(v___x_4361_, 0);
                            v_isSharedCheck_4411_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4361_)) as u8;
                            if v_isSharedCheck_4411_ == 0 {
                                v___x_4406_ = v___x_4361_;
                                v_isShared_4407_ = v_isSharedCheck_4411_;
                                state = 32;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4404_);
                                crate::leanh::lean_dec(v___x_4361_);
                                v___x_4406_ = crate::leanh::lean_box(0);
                                v_isShared_4407_ = v_isSharedCheck_4411_;
                                state = 32;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                v___x_4239_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_4238_);
                if v_isShared_4236_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4235_, 0, v___x_4239_);
                    v___x_4241_ = v___x_4235_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4242_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4239_);
                    v___x_4241_ = v_reuseFailAlloc_4242_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4241_;
            }
            7 => {
                v___x_4255_ = l_Lean_Meta_Sym_Simp_simpArrow___closed__1;
                v___x_4256_ = crate::leanh::lean_box(0);
                v___x_4257_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4257_, 0, v_a_4252_);
                crate::leanh::lean_ctor_set(v___x_4257_, 1, v___x_4256_);
                v___x_4258_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4258_, 0, v_a_4250_);
                crate::leanh::lean_ctor_set(v___x_4258_, 1, v___x_4257_);
                v___x_4259_ = l_Lean_mkConst(v___x_4255_, v___x_4258_);
                v___x_4260_ = l_Lean_mkApp4(
                    v___x_4259_,
                    v_p_4228_,
                    v_q_4231_,
                    v_e_x27_4246_,
                    v_proof_4247_,
                );
                v___x_4261_ = 0;
                if v_contextDependent_4245_ == 0 {
                    v___y_4215_ = v___x_4260_;
                    v___y_4216_ = v_a_4254_;
                    v___y_4217_ = v___x_4261_;
                    v___y_4218_ = v_contextDependent_4248_;
                    state = 2;
                    continue;
                } else {
                    v___y_4215_ = v___x_4260_;
                    v___y_4216_ = v_a_4254_;
                    v___y_4217_ = v___x_4261_;
                    v___y_4218_ = v_contextDependent_4245_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v___y_4263_) == 0 {
                    v_a_4264_ = crate::leanh::lean_ctor_get(v___y_4263_, 0);
                    crate::leanh::lean_inc(v_a_4264_);
                    crate::leanh::lean_dec_ref_known(v___y_4263_, 1);
                    v_a_4254_ = v_a_4264_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_4252_);
                    crate::leanh::lean_dec(v_a_4250_);
                    crate::leanh::lean_dec_ref(v_proof_4247_);
                    crate::leanh::lean_dec_ref(v_e_x27_4246_);
                    crate::leanh::lean_dec_ref(v_q_4231_);
                    crate::leanh::lean_dec_ref(v_p_4228_);
                    v_a_4265_ = crate::leanh::lean_ctor_get(v___y_4263_, 0);
                    v_isSharedCheck_4272_ = (!crate::leanh::lean_is_exclusive(v___y_4263_)) as u8;
                    if v_isSharedCheck_4272_ == 0 {
                        v___x_4267_ = v___y_4263_;
                        v_isShared_4268_ = v_isSharedCheck_4272_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4265_);
                        crate::leanh::lean_dec(v___y_4263_);
                        v___x_4267_ = crate::leanh::lean_box(0);
                        v_isShared_4268_ = v_isSharedCheck_4272_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4268_ == 0 {
                    v___x_4270_ = v___x_4267_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
                    v___x_4270_ = v_reuseFailAlloc_4271_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4270_;
            }
            11 => {
                if v___y_4278_ == 0 {
                    crate::leanh::lean_inc(v_binderName_4273_);
                    crate::leanh::lean_dec_ref_known(v_e_4196_, 3);
                    crate::leanh::lean_inc_ref(v_e_x27_4246_);
                    crate::leanh::lean_inc_ref(v_p_4228_);
                    v___x_4279_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_4273_, v_binderInfo_4276_, v_p_4228_, v_e_x27_4246_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
                    v___y_4263_ = v___x_4279_;
                    state = 8;
                    continue;
                } else {
                    v_a_4254_ = v_e_4196_;
                    state = 7;
                    continue;
                }
            }
            12 => {
                if v_isShared_4287_ == 0 {
                    v___x_4289_ = v___x_4286_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4289_;
            }
            14 => {
                if v_isShared_4295_ == 0 {
                    v___x_4297_ = v___x_4294_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
                    v___x_4297_ = v_reuseFailAlloc_4298_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4297_;
            }
            16 => {
                v___x_4310_ = l_Lean_Meta_Sym_Simp_simpArrow___closed__7;
                v___x_4311_ = crate::leanh::lean_box(0);
                v___x_4312_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4312_, 0, v_a_4307_);
                crate::leanh::lean_ctor_set(v___x_4312_, 1, v___x_4311_);
                v___x_4313_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4313_, 0, v_a_4305_);
                crate::leanh::lean_ctor_set(v___x_4313_, 1, v___x_4312_);
                v___x_4314_ = l_Lean_mkConst(v___x_4310_, v___x_4313_);
                v___x_4315_ = l_Lean_mkApp4(
                    v___x_4314_,
                    v_p_4228_,
                    v_e_x27_4300_,
                    v_q_4231_,
                    v_proof_4301_,
                );
                v___x_4316_ = 0;
                if v_contextDependent_4302_ == 0 {
                    v___y_4208_ = v___x_4315_;
                    v___y_4209_ = v_a_4309_;
                    v___y_4210_ = v___x_4316_;
                    v___y_4211_ = v_contextDependent_4303_;
                    state = 1;
                    continue;
                } else {
                    v___y_4208_ = v___x_4315_;
                    v___y_4209_ = v_a_4309_;
                    v___y_4210_ = v___x_4316_;
                    v___y_4211_ = v_contextDependent_4302_;
                    state = 1;
                    continue;
                }
            }
            17 => {
                if crate::leanh::lean_obj_tag(v___y_4318_) == 0 {
                    v_a_4319_ = crate::leanh::lean_ctor_get(v___y_4318_, 0);
                    crate::leanh::lean_inc(v_a_4319_);
                    crate::leanh::lean_dec_ref_known(v___y_4318_, 1);
                    v_a_4309_ = v_a_4319_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_4307_);
                    crate::leanh::lean_dec(v_a_4305_);
                    crate::leanh::lean_dec_ref(v_proof_4301_);
                    crate::leanh::lean_dec_ref(v_e_x27_4300_);
                    crate::leanh::lean_dec_ref(v_q_4231_);
                    crate::leanh::lean_dec_ref(v_p_4228_);
                    v_a_4320_ = crate::leanh::lean_ctor_get(v___y_4318_, 0);
                    v_isSharedCheck_4327_ = (!crate::leanh::lean_is_exclusive(v___y_4318_)) as u8;
                    if v_isSharedCheck_4327_ == 0 {
                        v___x_4322_ = v___y_4318_;
                        v_isShared_4323_ = v_isSharedCheck_4327_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4320_);
                        crate::leanh::lean_dec(v___y_4318_);
                        v___x_4322_ = crate::leanh::lean_box(0);
                        v_isShared_4323_ = v_isSharedCheck_4327_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4323_ == 0 {
                    v___x_4325_ = v___x_4322_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4326_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
                    v___x_4325_ = v_reuseFailAlloc_4326_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4325_;
            }
            20 => {
                if v___y_4333_ == 0 {
                    crate::leanh::lean_inc(v_binderName_4328_);
                    crate::leanh::lean_dec_ref_known(v_e_4196_, 3);
                    crate::leanh::lean_inc_ref(v_q_4231_);
                    crate::leanh::lean_inc_ref(v_e_x27_4300_);
                    v___x_4334_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_4328_, v_binderInfo_4331_, v_e_x27_4300_, v_q_4231_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
                    v___y_4318_ = v___x_4334_;
                    state = 17;
                    continue;
                } else {
                    v_a_4309_ = v_e_4196_;
                    state = 16;
                    continue;
                }
            }
            21 => {
                if v_isShared_4342_ == 0 {
                    v___x_4344_ = v___x_4341_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
                    v___x_4344_ = v_reuseFailAlloc_4345_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4344_;
            }
            23 => {
                if v_isShared_4350_ == 0 {
                    v___x_4352_ = v___x_4349_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
                    v___x_4352_ = v_reuseFailAlloc_4353_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4352_;
            }
            25 => {
                v___x_4367_ = l_Lean_Meta_Sym_Simp_simpArrow___closed__9;
                v___x_4368_ = crate::leanh::lean_box(0);
                v___x_4369_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4369_, 0, v_a_4364_);
                crate::leanh::lean_ctor_set(v___x_4369_, 1, v___x_4368_);
                v___x_4370_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4370_, 0, v_a_4362_);
                crate::leanh::lean_ctor_set(v___x_4370_, 1, v___x_4369_);
                v___x_4371_ = l_Lean_mkConst(v___x_4367_, v___x_4370_);
                v___x_4372_ = l_Lean_mkApp6(
                    v___x_4371_,
                    v_p_4228_,
                    v_e_x27_4355_,
                    v_q_4231_,
                    v_e_x27_4358_,
                    v_proof_4356_,
                    v_proof_4359_,
                );
                v___x_4373_ = 0;
                if v_contextDependent_4357_ == 0 {
                    v___y_4222_ = v___x_4372_;
                    v___y_4223_ = v_a_4366_;
                    v___y_4224_ = v___x_4373_;
                    v___y_4225_ = v_contextDependent_4360_;
                    state = 3;
                    continue;
                } else {
                    v___y_4222_ = v___x_4372_;
                    v___y_4223_ = v_a_4366_;
                    v___y_4224_ = v___x_4373_;
                    v___y_4225_ = v_contextDependent_4357_;
                    state = 3;
                    continue;
                }
            }
            26 => {
                if crate::leanh::lean_obj_tag(v___y_4375_) == 0 {
                    v_a_4376_ = crate::leanh::lean_ctor_get(v___y_4375_, 0);
                    crate::leanh::lean_inc(v_a_4376_);
                    crate::leanh::lean_dec_ref_known(v___y_4375_, 1);
                    v_a_4366_ = v_a_4376_;
                    state = 25;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_4364_);
                    crate::leanh::lean_dec(v_a_4362_);
                    crate::leanh::lean_dec_ref(v_proof_4359_);
                    crate::leanh::lean_dec_ref(v_e_x27_4358_);
                    crate::leanh::lean_dec_ref(v_proof_4356_);
                    crate::leanh::lean_dec_ref(v_e_x27_4355_);
                    crate::leanh::lean_dec_ref(v_q_4231_);
                    crate::leanh::lean_dec_ref(v_p_4228_);
                    v_a_4377_ = crate::leanh::lean_ctor_get(v___y_4375_, 0);
                    v_isSharedCheck_4384_ = (!crate::leanh::lean_is_exclusive(v___y_4375_)) as u8;
                    if v_isSharedCheck_4384_ == 0 {
                        v___x_4379_ = v___y_4375_;
                        v_isShared_4380_ = v_isSharedCheck_4384_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4377_);
                        crate::leanh::lean_dec(v___y_4375_);
                        v___x_4379_ = crate::leanh::lean_box(0);
                        v_isShared_4380_ = v_isSharedCheck_4384_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_4380_ == 0 {
                    v___x_4382_ = v___x_4379_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
                    v___x_4382_ = v_reuseFailAlloc_4383_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4382_;
            }
            29 => {
                if v___y_4390_ == 0 {
                    crate::leanh::lean_inc(v_binderName_4385_);
                    crate::leanh::lean_dec_ref_known(v_e_4196_, 3);
                    crate::leanh::lean_inc_ref(v_e_x27_4358_);
                    crate::leanh::lean_inc_ref(v_e_x27_4355_);
                    v___x_4391_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_Simp_simpArrow_spec__0___redArg(v_binderName_4385_, v_binderInfo_4388_, v_e_x27_4355_, v_e_x27_4358_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
                    v___y_4375_ = v___x_4391_;
                    state = 26;
                    continue;
                } else {
                    v_a_4366_ = v_e_4196_;
                    state = 25;
                    continue;
                }
            }
            30 => {
                if v_isShared_4399_ == 0 {
                    v___x_4401_ = v___x_4398_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4402_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
                    v___x_4401_ = v_reuseFailAlloc_4402_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4401_;
            }
            32 => {
                if v_isShared_4407_ == 0 {
                    v___x_4409_ = v___x_4406_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4410_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
                    v___x_4409_ = v_reuseFailAlloc_4410_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4409_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpArrow___boxed(
    mut v_e_4413_: *mut crate::leanh::LeanObject,
    mut v_a_4414_: *mut crate::leanh::LeanObject,
    mut v_a_4415_: *mut crate::leanh::LeanObject,
    mut v_a_4416_: *mut crate::leanh::LeanObject,
    mut v_a_4417_: *mut crate::leanh::LeanObject,
    mut v_a_4418_: *mut crate::leanh::LeanObject,
    mut v_a_4419_: *mut crate::leanh::LeanObject,
    mut v_a_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4424_ = l_Lean_Meta_Sym_Simp_simpArrow(
        v_e_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_,
        v_a_4421_, v_a_4422_,
    );
    crate::leanh::lean_dec(v_a_4422_);
    crate::leanh::lean_dec_ref(v_a_4421_);
    crate::leanh::lean_dec(v_a_4420_);
    crate::leanh::lean_dec_ref(v_a_4419_);
    crate::leanh::lean_dec(v_a_4418_);
    crate::leanh::lean_dec_ref(v_a_4417_);
    crate::leanh::lean_dec(v_a_4416_);
    crate::leanh::lean_dec_ref(v_a_4415_);
    crate::leanh::lean_dec(v_a_4414_);
    return v_res_4424_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(
    mut v_simpBody_4425_: *mut crate::leanh::LeanObject,
    mut v_xs_4426_: *mut crate::leanh::LeanObject,
    mut v_b_4427_: *mut crate::leanh::LeanObject,
    mut v_a_4428_: *mut crate::leanh::LeanObject,
    mut v_a_4429_: *mut crate::leanh::LeanObject,
    mut v_a_4430_: *mut crate::leanh::LeanObject,
    mut v_a_4431_: *mut crate::leanh::LeanObject,
    mut v_a_4432_: *mut crate::leanh::LeanObject,
    mut v_a_4433_: *mut crate::leanh::LeanObject,
    mut v_a_4434_: *mut crate::leanh::LeanObject,
    mut v_a_4435_: *mut crate::leanh::LeanObject,
    mut v_a_4436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4442_: u8 = 0;
    let mut v_contextDependent_4443_: u8 = 0;
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4450_: u8 = 0;
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4453_: u8 = 0;
    let mut v___x_4454_: u8 = 0;
    let mut v___x_4455_: u8 = 0;
    let mut v___x_4456_: u8 = 0;
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4471_: u8 = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v_a_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4483_: u8 = 0;
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4487_: u8 = 0;
    let mut v_a_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4495_: u8 = 0;
    let mut v_a_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4499_: u8 = 0;
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4503_: u8 = 0;
    let mut v_a_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4507_: u8 = 0;
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4511_: u8 = 0;
    let mut v_a_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4515_: u8 = 0;
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4519_: u8 = 0;
    let mut v_a_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4523_: u8 = 0;
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4527_: u8 = 0;
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_4436_);
                crate::leanh::lean_inc_ref(v_a_4435_);
                crate::leanh::lean_inc(v_a_4434_);
                crate::leanh::lean_inc_ref(v_a_4433_);
                crate::leanh::lean_inc(v_a_4432_);
                crate::leanh::lean_inc_ref(v_a_4431_);
                crate::leanh::lean_inc(v_a_4430_);
                crate::leanh::lean_inc_ref(v_a_4429_);
                crate::leanh::lean_inc(v_a_4428_);
                crate::leanh::lean_inc_ref(v_b_4427_);
                v___x_4438_ = crate::leanh::lean_apply_11(
                    v_simpBody_4425_,
                    v_b_4427_,
                    v_a_4428_,
                    v_a_4429_,
                    v_a_4430_,
                    v_a_4431_,
                    v_a_4432_,
                    v_a_4433_,
                    v_a_4434_,
                    v_a_4435_,
                    v_a_4436_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4438_) == 0 {
                    v_a_4439_ = crate::leanh::lean_ctor_get(v___x_4438_, 0);
                    v_isSharedCheck_4529_ = (!crate::leanh::lean_is_exclusive(v___x_4438_)) as u8;
                    if v_isSharedCheck_4529_ == 0 {
                        v___x_4441_ = v___x_4438_;
                        v_isShared_4442_ = v_isSharedCheck_4529_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4439_);
                        crate::leanh::lean_dec(v___x_4438_);
                        v___x_4441_ = crate::leanh::lean_box(0);
                        v_isShared_4442_ = v_isSharedCheck_4529_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_4427_);
                    crate::leanh::lean_dec_ref(v_xs_4426_);
                    return v___x_4438_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4439_) == 0 {
                    crate::leanh::lean_dec_ref(v_b_4427_);
                    crate::leanh::lean_dec_ref(v_xs_4426_);
                    v_contextDependent_4443_ =
                        crate::leanh::lean_ctor_get_uint8(v_a_4439_, 1 as u32);
                    crate::leanh::lean_dec_ref_known(v_a_4439_, 0);
                    v___x_4444_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v_contextDependent_4443_);
                    if v_isShared_4442_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4441_, 0, v___x_4444_);
                        v___x_4446_ = v___x_4441_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4447_, 0, v___x_4444_);
                        v___x_4446_ = v_reuseFailAlloc_4447_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4441_);
                    v_e_x27_4448_ = crate::leanh::lean_ctor_get(v_a_4439_, 0);
                    v_proof_4449_ = crate::leanh::lean_ctor_get(v_a_4439_, 1);
                    v_contextDependent_4450_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4439_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    );
                    v_isSharedCheck_4528_ = (!crate::leanh::lean_is_exclusive(v_a_4439_)) as u8;
                    if v_isSharedCheck_4528_ == 0 {
                        v___x_4452_ = v_a_4439_;
                        v_isShared_4453_ = v_isSharedCheck_4528_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_proof_4449_);
                        crate::leanh::lean_inc(v_e_x27_4448_);
                        crate::leanh::lean_dec(v_a_4439_);
                        v___x_4452_ = crate::leanh::lean_box(0);
                        v_isShared_4453_ = v_isSharedCheck_4528_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4446_;
            }
            3 => {
                v___x_4454_ = 0;
                v___x_4455_ = 1;
                v___x_4456_ = 1;
                v___x_4457_ = l_Lean_Meta_mkLambdaFVars(
                    v_xs_4426_,
                    v_proof_4449_,
                    v___x_4454_,
                    v___x_4455_,
                    v___x_4454_,
                    v___x_4455_,
                    v___x_4456_,
                    v_a_4433_,
                    v_a_4434_,
                    v_a_4435_,
                    v_a_4436_,
                );
                if crate::leanh::lean_obj_tag(v___x_4457_) == 0 {
                    v_a_4458_ = crate::leanh::lean_ctor_get(v___x_4457_, 0);
                    crate::leanh::lean_inc(v_a_4458_);
                    crate::leanh::lean_dec_ref_known(v___x_4457_, 1);
                    crate::leanh::lean_inc_ref(v_e_x27_4448_);
                    v___x_4459_ = l_Lean_Meta_mkForallFVars(
                        v_xs_4426_,
                        v_e_x27_4448_,
                        v___x_4454_,
                        v___x_4455_,
                        v___x_4455_,
                        v___x_4456_,
                        v_a_4433_,
                        v_a_4434_,
                        v_a_4435_,
                        v_a_4436_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4459_) == 0 {
                        v_a_4460_ = crate::leanh::lean_ctor_get(v___x_4459_, 0);
                        crate::leanh::lean_inc(v_a_4460_);
                        crate::leanh::lean_dec_ref_known(v___x_4459_, 1);
                        v___x_4461_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_4460_, v_a_4432_);
                        if crate::leanh::lean_obj_tag(v___x_4461_) == 0 {
                            v_a_4462_ = crate::leanh::lean_ctor_get(v___x_4461_, 0);
                            crate::leanh::lean_inc(v_a_4462_);
                            crate::leanh::lean_dec_ref_known(v___x_4461_, 1);
                            crate::leanh::lean_inc_ref(v_xs_4426_);
                            v___x_4463_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_4426_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_);
                            if crate::leanh::lean_obj_tag(v___x_4463_) == 0 {
                                v_a_4464_ = crate::leanh::lean_ctor_get(v___x_4463_, 0);
                                crate::leanh::lean_inc(v_a_4464_);
                                crate::leanh::lean_dec_ref_known(v___x_4463_, 1);
                                v___x_4465_ = l_Lean_Meta_mkLambdaFVars(
                                    v_xs_4426_,
                                    v_b_4427_,
                                    v___x_4454_,
                                    v___x_4455_,
                                    v___x_4454_,
                                    v___x_4455_,
                                    v___x_4456_,
                                    v_a_4433_,
                                    v_a_4434_,
                                    v_a_4435_,
                                    v_a_4436_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4465_) == 0 {
                                    v_a_4466_ = crate::leanh::lean_ctor_get(v___x_4465_, 0);
                                    crate::leanh::lean_inc(v_a_4466_);
                                    crate::leanh::lean_dec_ref_known(v___x_4465_, 1);
                                    v___x_4467_ = l_Lean_Meta_mkLambdaFVars(
                                        v_xs_4426_,
                                        v_e_x27_4448_,
                                        v___x_4454_,
                                        v___x_4455_,
                                        v___x_4454_,
                                        v___x_4455_,
                                        v___x_4456_,
                                        v_a_4433_,
                                        v_a_4434_,
                                        v_a_4435_,
                                        v_a_4436_,
                                    );
                                    crate::leanh::lean_dec_ref(v_xs_4426_);
                                    if crate::leanh::lean_obj_tag(v___x_4467_) == 0 {
                                        v_a_4468_ = crate::leanh::lean_ctor_get(v___x_4467_, 0);
                                        v_isSharedCheck_4479_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4467_)) as u8;
                                        if v_isSharedCheck_4479_ == 0 {
                                            v___x_4470_ = v___x_4467_;
                                            v_isShared_4471_ = v_isSharedCheck_4479_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4468_);
                                            crate::leanh::lean_dec(v___x_4467_);
                                            v___x_4470_ = crate::leanh::lean_box(0);
                                            v_isShared_4471_ = v_isSharedCheck_4479_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_4466_);
                                        crate::leanh::lean_dec(v_a_4464_);
                                        crate::leanh::lean_dec(v_a_4462_);
                                        crate::leanh::lean_dec(v_a_4458_);
                                        crate::leanh::lean_del_object(v___x_4452_);
                                        v_a_4480_ = crate::leanh::lean_ctor_get(v___x_4467_, 0);
                                        v_isSharedCheck_4487_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4467_)) as u8;
                                        if v_isSharedCheck_4487_ == 0 {
                                            v___x_4482_ = v___x_4467_;
                                            v_isShared_4483_ = v_isSharedCheck_4487_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4480_);
                                            crate::leanh::lean_dec(v___x_4467_);
                                            v___x_4482_ = crate::leanh::lean_box(0);
                                            v_isShared_4483_ = v_isSharedCheck_4487_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4464_);
                                    crate::leanh::lean_dec(v_a_4462_);
                                    crate::leanh::lean_dec(v_a_4458_);
                                    crate::leanh::lean_del_object(v___x_4452_);
                                    crate::leanh::lean_dec_ref(v_e_x27_4448_);
                                    crate::leanh::lean_dec_ref(v_xs_4426_);
                                    v_a_4488_ = crate::leanh::lean_ctor_get(v___x_4465_, 0);
                                    v_isSharedCheck_4495_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4465_)) as u8;
                                    if v_isSharedCheck_4495_ == 0 {
                                        v___x_4490_ = v___x_4465_;
                                        v_isShared_4491_ = v_isSharedCheck_4495_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4488_);
                                        crate::leanh::lean_dec(v___x_4465_);
                                        v___x_4490_ = crate::leanh::lean_box(0);
                                        v_isShared_4491_ = v_isSharedCheck_4495_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4462_);
                                crate::leanh::lean_dec(v_a_4458_);
                                crate::leanh::lean_del_object(v___x_4452_);
                                crate::leanh::lean_dec_ref(v_e_x27_4448_);
                                crate::leanh::lean_dec_ref(v_b_4427_);
                                crate::leanh::lean_dec_ref(v_xs_4426_);
                                v_a_4496_ = crate::leanh::lean_ctor_get(v___x_4463_, 0);
                                v_isSharedCheck_4503_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4463_)) as u8;
                                if v_isSharedCheck_4503_ == 0 {
                                    v___x_4498_ = v___x_4463_;
                                    v_isShared_4499_ = v_isSharedCheck_4503_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4496_);
                                    crate::leanh::lean_dec(v___x_4463_);
                                    v___x_4498_ = crate::leanh::lean_box(0);
                                    v_isShared_4499_ = v_isSharedCheck_4503_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4458_);
                            crate::leanh::lean_del_object(v___x_4452_);
                            crate::leanh::lean_dec_ref(v_e_x27_4448_);
                            crate::leanh::lean_dec_ref(v_b_4427_);
                            crate::leanh::lean_dec_ref(v_xs_4426_);
                            v_a_4504_ = crate::leanh::lean_ctor_get(v___x_4461_, 0);
                            v_isSharedCheck_4511_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4461_)) as u8;
                            if v_isSharedCheck_4511_ == 0 {
                                v___x_4506_ = v___x_4461_;
                                v_isShared_4507_ = v_isSharedCheck_4511_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4504_);
                                crate::leanh::lean_dec(v___x_4461_);
                                v___x_4506_ = crate::leanh::lean_box(0);
                                v_isShared_4507_ = v_isSharedCheck_4511_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4458_);
                        crate::leanh::lean_del_object(v___x_4452_);
                        crate::leanh::lean_dec_ref(v_e_x27_4448_);
                        crate::leanh::lean_dec_ref(v_b_4427_);
                        crate::leanh::lean_dec_ref(v_xs_4426_);
                        v_a_4512_ = crate::leanh::lean_ctor_get(v___x_4459_, 0);
                        v_isSharedCheck_4519_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4459_)) as u8;
                        if v_isSharedCheck_4519_ == 0 {
                            v___x_4514_ = v___x_4459_;
                            v_isShared_4515_ = v_isSharedCheck_4519_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4512_);
                            crate::leanh::lean_dec(v___x_4459_);
                            v___x_4514_ = crate::leanh::lean_box(0);
                            v_isShared_4515_ = v_isSharedCheck_4519_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4452_);
                    crate::leanh::lean_dec_ref(v_e_x27_4448_);
                    crate::leanh::lean_dec_ref(v_b_4427_);
                    crate::leanh::lean_dec_ref(v_xs_4426_);
                    v_a_4520_ = crate::leanh::lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4527_ = (!crate::leanh::lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4527_ == 0 {
                        v___x_4522_ = v___x_4457_;
                        v_isShared_4523_ = v_isSharedCheck_4527_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4520_);
                        crate::leanh::lean_dec(v___x_4457_);
                        v___x_4522_ = crate::leanh::lean_box(0);
                        v_isShared_4523_ = v_isSharedCheck_4527_;
                        state = 17;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4472_ = l_Lean_mkApp3(v_a_4464_, v_a_4466_, v_a_4468_, v_a_4458_);
                if v_isShared_4453_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4452_, 1, v___x_4472_);
                    crate::leanh::lean_ctor_set(v___x_4452_, 0, v_a_4462_);
                    v___x_4474_ = v___x_4452_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4478_ = crate::leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4478_, 1, v___x_4472_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4478_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_4450_,
                    );
                    v___x_4474_ = v_reuseFailAlloc_4478_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4474_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4454_,
                );
                if v_isShared_4471_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4470_, 0, v___x_4474_);
                    v___x_4476_ = v___x_4470_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4474_);
                    v___x_4476_ = v_reuseFailAlloc_4477_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4476_;
            }
            7 => {
                if v_isShared_4483_ == 0 {
                    v___x_4485_ = v___x_4482_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4486_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
                    v___x_4485_ = v_reuseFailAlloc_4486_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4485_;
            }
            9 => {
                if v_isShared_4491_ == 0 {
                    v___x_4493_ = v___x_4490_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
                    v___x_4493_ = v_reuseFailAlloc_4494_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4493_;
            }
            11 => {
                if v_isShared_4499_ == 0 {
                    v___x_4501_ = v___x_4498_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4502_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
                    v___x_4501_ = v_reuseFailAlloc_4502_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4501_;
            }
            13 => {
                if v_isShared_4507_ == 0 {
                    v___x_4509_ = v___x_4506_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4510_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
                    v___x_4509_ = v_reuseFailAlloc_4510_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4509_;
            }
            15 => {
                if v_isShared_4515_ == 0 {
                    v___x_4517_ = v___x_4514_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
                    v___x_4517_ = v_reuseFailAlloc_4518_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4517_;
            }
            17 => {
                if v_isShared_4523_ == 0 {
                    v___x_4525_ = v___x_4522_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4526_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
                    v___x_4525_ = v_reuseFailAlloc_4526_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main___boxed(
    mut v_simpBody_4530_: *mut crate::leanh::LeanObject,
    mut v_xs_4531_: *mut crate::leanh::LeanObject,
    mut v_b_4532_: *mut crate::leanh::LeanObject,
    mut v_a_4533_: *mut crate::leanh::LeanObject,
    mut v_a_4534_: *mut crate::leanh::LeanObject,
    mut v_a_4535_: *mut crate::leanh::LeanObject,
    mut v_a_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: *mut crate::leanh::LeanObject,
    mut v_a_4540_: *mut crate::leanh::LeanObject,
    mut v_a_4541_: *mut crate::leanh::LeanObject,
    mut v_a_4542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4543_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(
        v_simpBody_4530_,
        v_xs_4531_,
        v_b_4532_,
        v_a_4533_,
        v_a_4534_,
        v_a_4535_,
        v_a_4536_,
        v_a_4537_,
        v_a_4538_,
        v_a_4539_,
        v_a_4540_,
        v_a_4541_,
    );
    crate::leanh::lean_dec(v_a_4541_);
    crate::leanh::lean_dec_ref(v_a_4540_);
    crate::leanh::lean_dec(v_a_4539_);
    crate::leanh::lean_dec_ref(v_a_4538_);
    crate::leanh::lean_dec(v_a_4537_);
    crate::leanh::lean_dec_ref(v_a_4536_);
    crate::leanh::lean_dec(v_a_4535_);
    crate::leanh::lean_dec_ref(v_a_4534_);
    crate::leanh::lean_dec(v_a_4533_);
    return v_res_4543_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(
    mut v_e_4544_: *mut crate::leanh::LeanObject,
    mut v_n_4545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_body_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: u8 = 0;
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_4544_) == 7 {
                    v_body_4546_ = crate::leanh::lean_ctor_get(v_e_4544_, 2);
                    v___x_4547_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4548_ = lean_expr_has_loose_bvar(v_body_4546_, v___x_4547_);
                    if v___x_4548_ == 0 {
                        return v_n_4545_;
                    } else {
                        v___x_4549_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4550_ = lean_nat_add(v_n_4545_, v___x_4549_);
                        crate::leanh::lean_dec(v_n_4545_);
                        v_e_4544_ = v_body_4546_;
                        v_n_4545_ = v___x_4550_;
                        state = 0;
                        continue;
                    }
                } else {
                    return v_n_4545_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize___boxed(
    mut v_e_4552_: *mut crate::leanh::LeanObject,
    mut v_n_4553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4554_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(v_e_4552_, v_n_4553_);
    crate::leanh::lean_dec_ref(v_e_4552_);
    return v_res_4554_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(
    mut v_k_4555_: *mut crate::leanh::LeanObject,
    mut v___y_4556_: *mut crate::leanh::LeanObject,
    mut v___y_4557_: *mut crate::leanh::LeanObject,
    mut v___y_4558_: *mut crate::leanh::LeanObject,
    mut v___y_4559_: *mut crate::leanh::LeanObject,
    mut v___y_4560_: *mut crate::leanh::LeanObject,
    mut v_b_4561_: *mut crate::leanh::LeanObject,
    mut v_c_4562_: *mut crate::leanh::LeanObject,
    mut v___y_4563_: *mut crate::leanh::LeanObject,
    mut v___y_4564_: *mut crate::leanh::LeanObject,
    mut v___y_4565_: *mut crate::leanh::LeanObject,
    mut v___y_4566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4566_);
    crate::leanh::lean_inc_ref(v___y_4565_);
    crate::leanh::lean_inc(v___y_4564_);
    crate::leanh::lean_inc_ref(v___y_4563_);
    crate::leanh::lean_inc(v___y_4560_);
    crate::leanh::lean_inc_ref(v___y_4559_);
    crate::leanh::lean_inc(v___y_4558_);
    crate::leanh::lean_inc_ref(v___y_4557_);
    crate::leanh::lean_inc(v___y_4556_);
    v___x_4568_ = crate::leanh::lean_apply_12(
        v_k_4555_,
        v_b_4561_,
        v_c_4562_,
        v___y_4556_,
        v___y_4557_,
        v___y_4558_,
        v___y_4559_,
        v___y_4560_,
        v___y_4563_,
        v___y_4564_,
        v___y_4565_,
        v___y_4566_,
        crate::leanh::lean_box(0),
    );
    return v___x_4568_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed(
    mut v_k_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
    mut v___y_4573_: *mut crate::leanh::LeanObject,
    mut v___y_4574_: *mut crate::leanh::LeanObject,
    mut v_b_4575_: *mut crate::leanh::LeanObject,
    mut v_c_4576_: *mut crate::leanh::LeanObject,
    mut v___y_4577_: *mut crate::leanh::LeanObject,
    mut v___y_4578_: *mut crate::leanh::LeanObject,
    mut v___y_4579_: *mut crate::leanh::LeanObject,
    mut v___y_4580_: *mut crate::leanh::LeanObject,
    mut v___y_4581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4582_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0(v_k_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v_b_4575_, v_c_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
    crate::leanh::lean_dec(v___y_4580_);
    crate::leanh::lean_dec_ref(v___y_4579_);
    crate::leanh::lean_dec(v___y_4578_);
    crate::leanh::lean_dec_ref(v___y_4577_);
    crate::leanh::lean_dec(v___y_4574_);
    crate::leanh::lean_dec_ref(v___y_4573_);
    crate::leanh::lean_dec(v___y_4572_);
    crate::leanh::lean_dec_ref(v___y_4571_);
    crate::leanh::lean_dec(v___y_4570_);
    return v_res_4582_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(
    mut v_type_4583_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4584_: *mut crate::leanh::LeanObject,
    mut v_k_4585_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4586_: u8,
    mut v_whnfType_4587_: u8,
    mut v___y_4588_: *mut crate::leanh::LeanObject,
    mut v___y_4589_: *mut crate::leanh::LeanObject,
    mut v___y_4590_: *mut crate::leanh::LeanObject,
    mut v___y_4591_: *mut crate::leanh::LeanObject,
    mut v___y_4592_: *mut crate::leanh::LeanObject,
    mut v___y_4593_: *mut crate::leanh::LeanObject,
    mut v___y_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4603_: u8 = 0;
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4607_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4592_);
                crate::leanh::lean_inc_ref(v___y_4591_);
                crate::leanh::lean_inc(v___y_4590_);
                crate::leanh::lean_inc_ref(v___y_4589_);
                crate::leanh::lean_inc(v___y_4588_);
                v___f_4598_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 6);
                crate::leanh::lean_closure_set(v___f_4598_, 0, v_k_4585_);
                crate::leanh::lean_closure_set(v___f_4598_, 1, v___y_4588_);
                crate::leanh::lean_closure_set(v___f_4598_, 2, v___y_4589_);
                crate::leanh::lean_closure_set(v___f_4598_, 3, v___y_4590_);
                crate::leanh::lean_closure_set(v___f_4598_, 4, v___y_4591_);
                crate::leanh::lean_closure_set(v___f_4598_, 5, v___y_4592_);
                v___x_4599_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_4583_,
                    v_maxFVars_x3f_4584_,
                    v___f_4598_,
                    v_cleanupAnnotations_4586_,
                    v_whnfType_4587_,
                    v___y_4593_,
                    v___y_4594_,
                    v___y_4595_,
                    v___y_4596_,
                );
                if crate::leanh::lean_obj_tag(v___x_4599_) == 0 {
                    return v___x_4599_;
                } else {
                    v_a_4600_ = crate::leanh::lean_ctor_get(v___x_4599_, 0);
                    v_isSharedCheck_4607_ = (!crate::leanh::lean_is_exclusive(v___x_4599_)) as u8;
                    if v_isSharedCheck_4607_ == 0 {
                        v___x_4602_ = v___x_4599_;
                        v_isShared_4603_ = v_isSharedCheck_4607_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4600_);
                        crate::leanh::lean_dec(v___x_4599_);
                        v___x_4602_ = crate::leanh::lean_box(0);
                        v_isShared_4603_ = v_isSharedCheck_4607_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4603_ == 0 {
                    v___x_4605_ = v___x_4602_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
                    v___x_4605_ = v_reuseFailAlloc_4606_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg___boxed(
    mut v_type_4608_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4609_: *mut crate::leanh::LeanObject,
    mut v_k_4610_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4611_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4612_: *mut crate::leanh::LeanObject,
    mut v___y_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
    mut v___y_4616_: *mut crate::leanh::LeanObject,
    mut v___y_4617_: *mut crate::leanh::LeanObject,
    mut v___y_4618_: *mut crate::leanh::LeanObject,
    mut v___y_4619_: *mut crate::leanh::LeanObject,
    mut v___y_4620_: *mut crate::leanh::LeanObject,
    mut v___y_4621_: *mut crate::leanh::LeanObject,
    mut v___y_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4623_: u8 = 0;
    let mut v_whnfType_boxed_4624_: u8 = 0;
    let mut v_res_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4623_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4611_) as u8);
    v_whnfType_boxed_4624_ = (crate::leanh::lean_unbox(v_whnfType_4612_) as u8);
    v_res_4625_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_4608_, v_maxFVars_x3f_4609_, v_k_4610_, v_cleanupAnnotations_boxed_4623_, v_whnfType_boxed_4624_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
    crate::leanh::lean_dec(v___y_4621_);
    crate::leanh::lean_dec_ref(v___y_4620_);
    crate::leanh::lean_dec(v___y_4619_);
    crate::leanh::lean_dec_ref(v___y_4618_);
    crate::leanh::lean_dec(v___y_4617_);
    crate::leanh::lean_dec_ref(v___y_4616_);
    crate::leanh::lean_dec(v___y_4615_);
    crate::leanh::lean_dec_ref(v___y_4614_);
    crate::leanh::lean_dec(v___y_4613_);
    return v_res_4625_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(
    mut v_00_u03b1_4626_: *mut crate::leanh::LeanObject,
    mut v_type_4627_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4628_: *mut crate::leanh::LeanObject,
    mut v_k_4629_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4630_: u8,
    mut v_whnfType_4631_: u8,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4642_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_type_4627_, v_maxFVars_x3f_4628_, v_k_4629_, v_cleanupAnnotations_4630_, v_whnfType_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
    return v___x_4642_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___boxed(
    mut v_00_u03b1_4643_: *mut crate::leanh::LeanObject,
    mut v_type_4644_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4645_: *mut crate::leanh::LeanObject,
    mut v_k_4646_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4647_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
    mut v___y_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4659_: u8 = 0;
    let mut v_whnfType_boxed_4660_: u8 = 0;
    let mut v_res_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4659_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4647_) as u8);
    v_whnfType_boxed_4660_ = (crate::leanh::lean_unbox(v_whnfType_4648_) as u8);
    v_res_4661_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0(
            v_00_u03b1_4643_,
            v_type_4644_,
            v_maxFVars_x3f_4645_,
            v_k_4646_,
            v_cleanupAnnotations_boxed_4659_,
            v_whnfType_boxed_4660_,
            v___y_4649_,
            v___y_4650_,
            v___y_4651_,
            v___y_4652_,
            v___y_4653_,
            v___y_4654_,
            v___y_4655_,
            v___y_4656_,
            v___y_4657_,
        );
    crate::leanh::lean_dec(v___y_4657_);
    crate::leanh::lean_dec_ref(v___y_4656_);
    crate::leanh::lean_dec(v___y_4655_);
    crate::leanh::lean_dec_ref(v___y_4654_);
    crate::leanh::lean_dec(v___y_4653_);
    crate::leanh::lean_dec_ref(v___y_4652_);
    crate::leanh::lean_dec(v___y_4651_);
    crate::leanh::lean_dec_ref(v___y_4650_);
    crate::leanh::lean_dec(v___y_4649_);
    return v_res_4661_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(
    mut v___y_4662_: *mut crate::leanh::LeanObject,
    mut v_transientCache_4663_: *mut crate::leanh::LeanObject,
    mut v_funext_4664_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSteps_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_persistentCache_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4672_: u8 = 0;
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4679_: u8 = 0;
    let mut v_unused_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4667_ = lean_st_ref_take(v___y_4662_);
                v_numSteps_4668_ = crate::leanh::lean_ctor_get(v___x_4667_, 0);
                v_persistentCache_4669_ = crate::leanh::lean_ctor_get(v___x_4667_, 1);
                v_isSharedCheck_4679_ = (!crate::leanh::lean_is_exclusive(v___x_4667_)) as u8;
                if v_isSharedCheck_4679_ == 0 {
                    v_unused_4680_ = crate::leanh::lean_ctor_get(v___x_4667_, 3);
                    crate::leanh::lean_dec(v_unused_4680_);
                    v_unused_4681_ = crate::leanh::lean_ctor_get(v___x_4667_, 2);
                    crate::leanh::lean_dec(v_unused_4681_);
                    v___x_4671_ = v___x_4667_;
                    v_isShared_4672_ = v_isSharedCheck_4679_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_persistentCache_4669_);
                    crate::leanh::lean_inc(v_numSteps_4668_);
                    crate::leanh::lean_dec(v___x_4667_);
                    v___x_4671_ = crate::leanh::lean_box(0);
                    v_isShared_4672_ = v_isSharedCheck_4679_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4672_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4671_, 3, v_funext_4664_);
                    crate::leanh::lean_ctor_set(v___x_4671_, 2, v_transientCache_4663_);
                    v___x_4674_ = v___x_4671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4678_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_numSteps_4668_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4678_, 1, v_persistentCache_4669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4678_, 2, v_transientCache_4663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4678_, 3, v_funext_4664_);
                    v___x_4674_ = v_reuseFailAlloc_4678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4675_ = lean_st_ref_set(v___y_4662_, v___x_4674_);
                v___x_4676_ = crate::leanh::lean_box(0);
                v___x_4677_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4677_, 0, v___x_4676_);
                return v___x_4677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0___boxed(
    mut v___y_4682_: *mut crate::leanh::LeanObject,
    mut v_transientCache_4683_: *mut crate::leanh::LeanObject,
    mut v_funext_4684_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4685_: *mut crate::leanh::LeanObject,
    mut v___y_4686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4687_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(
        v___y_4682_,
        v_transientCache_4683_,
        v_funext_4684_,
        v_a_x3f_4685_,
    );
    crate::leanh::lean_dec(v_a_x3f_4685_);
    crate::leanh::lean_dec(v___y_4682_);
    return v_res_4687_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(
    mut v_simpBody_4688_: *mut crate::leanh::LeanObject,
    mut v_xs_4689_: *mut crate::leanh::LeanObject,
    mut v_b_4690_: *mut crate::leanh::LeanObject,
    mut v___y_4691_: *mut crate::leanh::LeanObject,
    mut v___y_4692_: *mut crate::leanh::LeanObject,
    mut v___y_4693_: *mut crate::leanh::LeanObject,
    mut v___y_4694_: *mut crate::leanh::LeanObject,
    mut v___y_4695_: *mut crate::leanh::LeanObject,
    mut v___y_4696_: *mut crate::leanh::LeanObject,
    mut v___y_4697_: *mut crate::leanh::LeanObject,
    mut v___y_4698_: *mut crate::leanh::LeanObject,
    mut v___y_4699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_transientCache_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funext_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4711_: u8 = 0;
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4715_: u8 = 0;
    let mut v_unused_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4723_: u8 = 0;
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4729_: u8 = 0;
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4733_: u8 = 0;
    let mut v_unused_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v_a_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4701_ = lean_st_ref_get(v___y_4693_);
                v___x_4702_ = lean_st_ref_get(v___y_4693_);
                v_transientCache_4703_ = crate::leanh::lean_ctor_get(v___x_4701_, 2);
                crate::leanh::lean_inc_ref(v_transientCache_4703_);
                crate::leanh::lean_dec(v___x_4701_);
                v_funext_4704_ = crate::leanh::lean_ctor_get(v___x_4702_, 3);
                crate::leanh::lean_inc_ref(v_funext_4704_);
                crate::leanh::lean_dec(v___x_4702_);
                v___x_4717_ = l_Lean_Meta_Sym_shareCommon___redArg(v_b_4690_, v___y_4695_);
                if crate::leanh::lean_obj_tag(v___x_4717_) == 0 {
                    v_a_4718_ = crate::leanh::lean_ctor_get(v___x_4717_, 0);
                    crate::leanh::lean_inc(v_a_4718_);
                    crate::leanh::lean_dec_ref_known(v___x_4717_, 1);
                    v___x_4719_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_main(v_simpBody_4688_, v_xs_4689_, v_a_4718_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
                    if crate::leanh::lean_obj_tag(v___x_4719_) == 0 {
                        v_a_4720_ = crate::leanh::lean_ctor_get(v___x_4719_, 0);
                        v_isSharedCheck_4736_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4719_)) as u8;
                        if v_isSharedCheck_4736_ == 0 {
                            v___x_4722_ = v___x_4719_;
                            v_isShared_4723_ = v_isSharedCheck_4736_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4720_);
                            crate::leanh::lean_dec(v___x_4719_);
                            v___x_4722_ = crate::leanh::lean_box(0);
                            v_isShared_4723_ = v_isSharedCheck_4736_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_4737_ = crate::leanh::lean_ctor_get(v___x_4719_, 0);
                        crate::leanh::lean_inc(v_a_4737_);
                        crate::leanh::lean_dec_ref_known(v___x_4719_, 1);
                        v_a_4706_ = v_a_4737_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_xs_4689_);
                    crate::leanh::lean_dec_ref(v_simpBody_4688_);
                    v_a_4738_ = crate::leanh::lean_ctor_get(v___x_4717_, 0);
                    crate::leanh::lean_inc(v_a_4738_);
                    crate::leanh::lean_dec_ref_known(v___x_4717_, 1);
                    v_a_4706_ = v_a_4738_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4707_ = crate::leanh::lean_box(0);
                v___x_4708_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(
                    v___y_4693_,
                    v_transientCache_4703_,
                    v_funext_4704_,
                    v___x_4707_,
                );
                v_isSharedCheck_4715_ = (!crate::leanh::lean_is_exclusive(v___x_4708_)) as u8;
                if v_isSharedCheck_4715_ == 0 {
                    v_unused_4716_ = crate::leanh::lean_ctor_get(v___x_4708_, 0);
                    crate::leanh::lean_dec(v_unused_4716_);
                    v___x_4710_ = v___x_4708_;
                    v_isShared_4711_ = v_isSharedCheck_4715_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4708_);
                    v___x_4710_ = crate::leanh::lean_box(0);
                    v_isShared_4711_ = v_isSharedCheck_4715_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4711_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4710_, 1);
                    crate::leanh::lean_ctor_set(v___x_4710_, 0, v_a_4706_);
                    v___x_4713_ = v___x_4710_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4714_, 0, v_a_4706_);
                    v___x_4713_ = v_reuseFailAlloc_4714_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4713_;
            }
            4 => {
                crate::leanh::lean_inc(v_a_4720_);
                if v_isShared_4723_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4722_, 1);
                    v___x_4725_ = v___x_4722_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4720_);
                    v___x_4725_ = v_reuseFailAlloc_4735_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4726_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__0(
                    v___y_4693_,
                    v_transientCache_4703_,
                    v_funext_4704_,
                    v___x_4725_,
                );
                crate::leanh::lean_dec_ref(v___x_4725_);
                v_isSharedCheck_4733_ = (!crate::leanh::lean_is_exclusive(v___x_4726_)) as u8;
                if v_isSharedCheck_4733_ == 0 {
                    v_unused_4734_ = crate::leanh::lean_ctor_get(v___x_4726_, 0);
                    crate::leanh::lean_dec(v_unused_4734_);
                    v___x_4728_ = v___x_4726_;
                    v_isShared_4729_ = v_isSharedCheck_4733_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4726_);
                    v___x_4728_ = crate::leanh::lean_box(0);
                    v_isShared_4729_ = v_isSharedCheck_4733_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4729_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4728_, 0, v_a_4720_);
                    v___x_4731_ = v___x_4728_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4732_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4720_);
                    v___x_4731_ = v_reuseFailAlloc_4732_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed(
    mut v_simpBody_4739_: *mut crate::leanh::LeanObject,
    mut v_xs_4740_: *mut crate::leanh::LeanObject,
    mut v_b_4741_: *mut crate::leanh::LeanObject,
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
    let mut v_res_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4752_ = l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1(
        v_simpBody_4739_,
        v_xs_4740_,
        v_b_4741_,
        v___y_4742_,
        v___y_4743_,
        v___y_4744_,
        v___y_4745_,
        v___y_4746_,
        v___y_4747_,
        v___y_4748_,
        v___y_4749_,
        v___y_4750_,
    );
    crate::leanh::lean_dec(v___y_4750_);
    crate::leanh::lean_dec_ref(v___y_4749_);
    crate::leanh::lean_dec(v___y_4748_);
    crate::leanh::lean_dec_ref(v___y_4747_);
    crate::leanh::lean_dec(v___y_4746_);
    crate::leanh::lean_dec_ref(v___y_4745_);
    crate::leanh::lean_dec(v___y_4744_);
    crate::leanh::lean_dec_ref(v___y_4743_);
    crate::leanh::lean_dec(v___y_4742_);
    return v_res_4752_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpForall_x27(
    mut v_simpArrow_4753_: *mut crate::leanh::LeanObject,
    mut v_simpBody_4754_: *mut crate::leanh::LeanObject,
    mut v_e_4755_: *mut crate::leanh::LeanObject,
    mut v_a_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_a_4758_: *mut crate::leanh::LeanObject,
    mut v_a_4759_: *mut crate::leanh::LeanObject,
    mut v_a_4760_: *mut crate::leanh::LeanObject,
    mut v_a_4761_: *mut crate::leanh::LeanObject,
    mut v_a_4762_: *mut crate::leanh::LeanObject,
    mut v_a_4763_: *mut crate::leanh::LeanObject,
    mut v_a_4764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4766_: u8 = 0;
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4771_: u8 = 0;
    let mut v___x_4772_: u8 = 0;
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: u8 = 0;
    let mut v___x_4775_: u8 = 0;
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4785_: u8 = 0;
    let mut v_a_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4789_: u8 = 0;
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4793_: u8 = 0;
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4766_ = l_Lean_Expr_isArrow(v_e_4755_);
                if v___x_4766_ == 0 {
                    crate::leanh::lean_dec_ref(v_simpArrow_4753_);
                    crate::leanh::lean_inc_ref(v_e_4755_);
                    v___x_4767_ =
                        l_Lean_Meta_isProp(v_e_4755_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_);
                    if crate::leanh::lean_obj_tag(v___x_4767_) == 0 {
                        v_a_4768_ = crate::leanh::lean_ctor_get(v___x_4767_, 0);
                        v_isSharedCheck_4785_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4767_)) as u8;
                        if v_isSharedCheck_4785_ == 0 {
                            v___x_4770_ = v___x_4767_;
                            v_isShared_4771_ = v_isSharedCheck_4785_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4768_);
                            crate::leanh::lean_dec(v___x_4767_);
                            v___x_4770_ = crate::leanh::lean_box(0);
                            v_isShared_4771_ = v_isSharedCheck_4785_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4755_);
                        crate::leanh::lean_dec_ref(v_simpBody_4754_);
                        v_a_4786_ = crate::leanh::lean_ctor_get(v___x_4767_, 0);
                        v_isSharedCheck_4793_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4767_)) as u8;
                        if v_isSharedCheck_4793_ == 0 {
                            v___x_4788_ = v___x_4767_;
                            v_isShared_4789_ = v_isSharedCheck_4793_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4786_);
                            crate::leanh::lean_dec(v___x_4767_);
                            v___x_4788_ = crate::leanh::lean_box(0);
                            v_isShared_4789_ = v_isSharedCheck_4793_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_simpBody_4754_);
                    crate::leanh::lean_inc(v_a_4764_);
                    crate::leanh::lean_inc_ref(v_a_4763_);
                    crate::leanh::lean_inc(v_a_4762_);
                    crate::leanh::lean_inc_ref(v_a_4761_);
                    crate::leanh::lean_inc(v_a_4760_);
                    crate::leanh::lean_inc_ref(v_a_4759_);
                    crate::leanh::lean_inc(v_a_4758_);
                    crate::leanh::lean_inc_ref(v_a_4757_);
                    crate::leanh::lean_inc(v_a_4756_);
                    v___x_4794_ = crate::leanh::lean_apply_11(
                        v_simpArrow_4753_,
                        v_e_4755_,
                        v_a_4756_,
                        v_a_4757_,
                        v_a_4758_,
                        v_a_4759_,
                        v_a_4760_,
                        v_a_4761_,
                        v_a_4762_,
                        v_a_4763_,
                        v_a_4764_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4794_;
                }
            }
            1 => {
                v___x_4772_ = (crate::leanh::lean_unbox(v_a_4768_) as u8);
                if v___x_4772_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_4755_);
                    crate::leanh::lean_dec_ref(v_simpBody_4754_);
                    v___x_4773_ = crate::leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    v___x_4774_ = (crate::leanh::lean_unbox(v_a_4768_) as u8);
                    crate::leanh::lean_ctor_set_uint8(v___x_4773_, 0 as u32, v___x_4774_);
                    v___x_4775_ = (crate::leanh::lean_unbox(v_a_4768_) as u8);
                    crate::leanh::lean_dec(v_a_4768_);
                    crate::leanh::lean_ctor_set_uint8(v___x_4773_, 1 as u32, v___x_4775_);
                    if v_isShared_4771_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4770_, 0, v___x_4773_);
                        v___x_4777_ = v___x_4770_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4778_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4773_);
                        v___x_4777_ = v_reuseFailAlloc_4778_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4770_);
                    crate::leanh::lean_dec(v_a_4768_);
                    v___f_4779_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Sym_Simp_simpForall_x27___lam__1___boxed
                            as *mut core::ffi::c_void,
                        13,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4779_, 0, v_simpBody_4754_);
                    v___x_4780_ = l_Lean_Expr_bindingBody_x21(v_e_4755_);
                    v___x_4781_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4782_ = l___private_Lean_Meta_Sym_Simp_Forall_0__Lean_Meta_Sym_Simp_simpForall_x27_getForallTelescopeSize(v___x_4780_, v___x_4781_);
                    crate::leanh::lean_dec_ref(v___x_4780_);
                    v___x_4783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4783_, 0, v___x_4782_);
                    v___x_4784_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_Sym_Simp_simpForall_x27_spec__0___redArg(v_e_4755_, v___x_4783_, v___f_4779_, v___x_4766_, v___x_4766_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_);
                    return v___x_4784_;
                }
            }
            2 => {
                return v___x_4777_;
            }
            3 => {
                if v_isShared_4789_ == 0 {
                    v___x_4791_ = v___x_4788_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4792_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
                    v___x_4791_ = v_reuseFailAlloc_4792_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpForall_x27___boxed(
    mut v_simpArrow_4795_: *mut crate::leanh::LeanObject,
    mut v_simpBody_4796_: *mut crate::leanh::LeanObject,
    mut v_e_4797_: *mut crate::leanh::LeanObject,
    mut v_a_4798_: *mut crate::leanh::LeanObject,
    mut v_a_4799_: *mut crate::leanh::LeanObject,
    mut v_a_4800_: *mut crate::leanh::LeanObject,
    mut v_a_4801_: *mut crate::leanh::LeanObject,
    mut v_a_4802_: *mut crate::leanh::LeanObject,
    mut v_a_4803_: *mut crate::leanh::LeanObject,
    mut v_a_4804_: *mut crate::leanh::LeanObject,
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
    mut v_a_4807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4808_ = l_Lean_Meta_Sym_Simp_simpForall_x27(
        v_simpArrow_4795_,
        v_simpBody_4796_,
        v_e_4797_,
        v_a_4798_,
        v_a_4799_,
        v_a_4800_,
        v_a_4801_,
        v_a_4802_,
        v_a_4803_,
        v_a_4804_,
        v_a_4805_,
        v_a_4806_,
    );
    crate::leanh::lean_dec(v_a_4806_);
    crate::leanh::lean_dec_ref(v_a_4805_);
    crate::leanh::lean_dec(v_a_4804_);
    crate::leanh::lean_dec_ref(v_a_4803_);
    crate::leanh::lean_dec(v_a_4802_);
    crate::leanh::lean_dec_ref(v_a_4801_);
    crate::leanh::lean_dec(v_a_4800_);
    crate::leanh::lean_dec_ref(v_a_4799_);
    crate::leanh::lean_dec(v_a_4798_);
    return v_res_4808_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpForall(
    mut v_e_4811_: *mut crate::leanh::LeanObject,
    mut v_a_4812_: *mut crate::leanh::LeanObject,
    mut v_a_4813_: *mut crate::leanh::LeanObject,
    mut v_a_4814_: *mut crate::leanh::LeanObject,
    mut v_a_4815_: *mut crate::leanh::LeanObject,
    mut v_a_4816_: *mut crate::leanh::LeanObject,
    mut v_a_4817_: *mut crate::leanh::LeanObject,
    mut v_a_4818_: *mut crate::leanh::LeanObject,
    mut v_a_4819_: *mut crate::leanh::LeanObject,
    mut v_a_4820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4822_ = l_Lean_Meta_Sym_Simp_simpForall___closed__0;
    v___x_4823_ = l_Lean_Meta_Sym_Simp_simpForall___closed__1;
    v___x_4824_ = l_Lean_Meta_Sym_Simp_simpForall_x27(
        v___x_4822_,
        v___x_4823_,
        v_e_4811_,
        v_a_4812_,
        v_a_4813_,
        v_a_4814_,
        v_a_4815_,
        v_a_4816_,
        v_a_4817_,
        v_a_4818_,
        v_a_4819_,
        v_a_4820_,
    );
    return v___x_4824_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_simpForall___boxed(
    mut v_e_4825_: *mut crate::leanh::LeanObject,
    mut v_a_4826_: *mut crate::leanh::LeanObject,
    mut v_a_4827_: *mut crate::leanh::LeanObject,
    mut v_a_4828_: *mut crate::leanh::LeanObject,
    mut v_a_4829_: *mut crate::leanh::LeanObject,
    mut v_a_4830_: *mut crate::leanh::LeanObject,
    mut v_a_4831_: *mut crate::leanh::LeanObject,
    mut v_a_4832_: *mut crate::leanh::LeanObject,
    mut v_a_4833_: *mut crate::leanh::LeanObject,
    mut v_a_4834_: *mut crate::leanh::LeanObject,
    mut v_a_4835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4836_ = l_Lean_Meta_Sym_Simp_simpForall(
        v_e_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_,
        v_a_4833_, v_a_4834_,
    );
    crate::leanh::lean_dec(v_a_4834_);
    crate::leanh::lean_dec_ref(v_a_4833_);
    crate::leanh::lean_dec(v_a_4832_);
    crate::leanh::lean_dec_ref(v_a_4831_);
    crate::leanh::lean_dec(v_a_4830_);
    crate::leanh::lean_dec_ref(v_a_4829_);
    crate::leanh::lean_dec(v_a_4828_);
    crate::leanh::lean_dec_ref(v_a_4827_);
    crate::leanh::lean_dec(v_a_4826_);
    return v_res_4836_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp_Forall(
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
    res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp_Forall(
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
pub unsafe fn initialize_Lean_Meta_Sym_Simp_Forall(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp_Forall(builtin);
}
