// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.PP
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_int_dec_eq, lean_int_dec_lt, lean_mk_thunk, lean_nat_abs,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_to_int, lean_st_ref_get,
    lean_thunk_get_own, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::State::{l_StateT_get, l_instMonadStateOfStateTOfMonad___redArg};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instMonadStateOfMonadStateOf___redArg, l_modify,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Nat_mkType, l_Lean_instInhabitedExpr, l_Lean_mkApp3,
    l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNatLit, l_Lean_mkNot,
    l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_ofNat, l_Lean_Level_succ___override};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::DenoteExpr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Functions::l_Lean_Meta_Grind_Arith_CommRing_checkInst;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p, l_Lean_Meta_Grind_Arith_CommRing_ringExt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types,
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__2_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__5_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0: f64 = 0.0;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [66, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [82, 105, 110, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__3_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__2_value) as *mut leanh::LeanObject,10806710915646349764 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__3_value) as *mut leanh::LeanObject,10040236838748678500 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__5_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__5_value) as *mut leanh::LeanObject,9626815015619986526 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__7_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__7_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__5_value) as *mut leanh::LeanObject,9626815015619986526 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__7_value) as *mut leanh::LeanObject,17185717442815859305 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__3_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__5_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__5_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__5_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__2_value) as *mut leanh::LeanObject,9341924117480681831 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__0_value) as *mut leanh::LeanObject,18134279130838690737 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__5_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__2_value) as *mut leanh::LeanObject,7102027102192867304 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__4_value) as *mut leanh::LeanObject,2929883540436775422 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__6_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__4_value) as *mut leanh::LeanObject,2929883540436775422 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__6_value) as *mut leanh::LeanObject,1611444129324655608 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__0_value) as *mut leanh::LeanObject,12847922472053947547 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 112, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__3_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__5_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__3_value) as *mut leanh::LeanObject,18388652353510661091 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__5_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__0_value) as *mut leanh::LeanObject,12847922472053947547 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__5_value) as *mut leanh::LeanObject,10422657989269798688 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__0_value) as *mut leanh::LeanObject,9594062259507646949 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__2_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__5_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__2_value) as *mut leanh::LeanObject,5442360487226035463 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__4_value) as *mut leanh::LeanObject,10393083817453678557 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__6_value) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__4_value) as *mut leanh::LeanObject,10393083817453678557 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__6_value) as *mut leanh::LeanObject,10680564408669940870 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__7_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject,13286986945483979944 as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__1_value) as *mut leanh::LeanObject,6004542540932731919 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [68, 105, 115, 101, 113, 117, 97, 108, 105, 116, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 105, 115, 101, 113, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__1_value) as *mut leanh::LeanObject,12150963035389937170 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [82, 105, 110, 103, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___closed__0_value) as *mut leanh::LeanObject,12468264359339847837 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__1_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [82, 105, 110, 103, 115, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__2_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [108, 105, 109, 105, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__0_value)
            as *mut leanh::LeanObject,
        6724977332459863754 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__2_value:
    leanh::LeanStringObject<74> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 74,
    m_capacity: 74,
    m_length: 73,
    m_data: [
        109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 114,
        105, 110, 103, 32, 115, 116, 101, 112, 115, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32,
        114, 101, 97, 99, 104, 101, 100, 44, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 58,
        32, 96, 40, 114, 105, 110, 103, 83, 116, 101, 112, 115, 32, 58, 61, 32, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__4_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [41, 96, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___lam__0(
    mut v_e_2301_: *mut leanh::LeanObject,
    mut v___y_2302_: *mut leanh::LeanObject,
    mut v___y_2303_: *mut leanh::LeanObject,
    mut v___y_2304_: *mut leanh::LeanObject,
    mut v___y_2305_: *mut leanh::LeanObject,
    mut v___y_2306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2308_, 0, v_e_2301_);
    leanh::lean_ctor_set(v___x_2308_, 1, v___y_2302_);
    v___x_2309_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2309_, 0, v___x_2308_);
    return v___x_2309_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___lam__0___boxed(
    mut v_e_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
    mut v___y_2314_: *mut leanh::LeanObject,
    mut v___y_2315_: *mut leanh::LeanObject,
    mut v___y_2316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2317_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___lam__0(v_e_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
    leanh::lean_dec(v___y_2315_);
    leanh::lean_dec_ref(v___y_2314_);
    leanh::lean_dec(v___y_2313_);
    leanh::lean_dec_ref(v___y_2312_);
    return v_res_2317_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___lam__1(
    mut v_e_2318_: *mut leanh::LeanObject,
    mut v___y_2319_: *mut leanh::LeanObject,
    mut v___y_2320_: *mut leanh::LeanObject,
    mut v___y_2321_: *mut leanh::LeanObject,
    mut v___y_2322_: *mut leanh::LeanObject,
    mut v___y_2323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2330_: u8 = 0;
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2335_: u8 = 0;
    let mut v_a_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2339_: u8 = 0;
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2325_ = leanh::lean_box(0);
                v___x_2326_ = l_Lean_Meta_synthInstance_x3f(
                    v_e_2318_,
                    v___x_2325_,
                    v___y_2320_,
                    v___y_2321_,
                    v___y_2322_,
                    v___y_2323_,
                );
                if leanh::lean_obj_tag(v___x_2326_) == 0 {
                    v_a_2327_ = leanh::lean_ctor_get(v___x_2326_, 0);
                    v_isSharedCheck_2335_ = (!leanh::lean_is_exclusive(v___x_2326_)) as u8;
                    if v_isSharedCheck_2335_ == 0 {
                        v___x_2329_ = v___x_2326_;
                        v_isShared_2330_ = v_isSharedCheck_2335_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2327_);
                        leanh::lean_dec(v___x_2326_);
                        v___x_2329_ = leanh::lean_box(0);
                        v_isShared_2330_ = v_isSharedCheck_2335_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2319_);
                    v_a_2336_ = leanh::lean_ctor_get(v___x_2326_, 0);
                    v_isSharedCheck_2343_ = (!leanh::lean_is_exclusive(v___x_2326_)) as u8;
                    if v_isSharedCheck_2343_ == 0 {
                        v___x_2338_ = v___x_2326_;
                        v_isShared_2339_ = v_isSharedCheck_2343_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2336_);
                        leanh::lean_dec(v___x_2326_);
                        v___x_2338_ = leanh::lean_box(0);
                        v_isShared_2339_ = v_isSharedCheck_2343_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2331_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2331_, 0, v_a_2327_);
                leanh::lean_ctor_set(v___x_2331_, 1, v___y_2319_);
                if v_isShared_2330_ == 0 {
                    leanh::lean_ctor_set(v___x_2329_, 0, v___x_2331_);
                    v___x_2333_ = v___x_2329_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2334_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
                    v___x_2333_ = v_reuseFailAlloc_2334_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2333_;
            }
            3 => {
                if v_isShared_2339_ == 0 {
                    v___x_2341_ = v___x_2338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
                    v___x_2341_ = v_reuseFailAlloc_2342_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___lam__1___boxed(
    mut v_e_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
    mut v___y_2346_: *mut leanh::LeanObject,
    mut v___y_2347_: *mut leanh::LeanObject,
    mut v___y_2348_: *mut leanh::LeanObject,
    mut v___y_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2351_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCanonM___lam__1(v_e_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
    leanh::lean_dec(v___y_2349_);
    leanh::lean_dec_ref(v___y_2348_);
    leanh::lean_dec(v___y_2347_);
    leanh::lean_dec_ref(v___y_2346_);
    return v_res_2351_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2358_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2359_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__0);
    v___x_2360_ = l_StateRefT_x27_instMonad___redArg(v___x_2359_);
    return v___x_2360_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM()
-> *mut leanh::LeanObject {
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2385_: u8 = 0;
    let mut v_toFunctor_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___f_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2412_: u8 = 0;
    let mut v_unused_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2414_: u8 = 0;
    let mut v_unused_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2365_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__1);
                v_toApplicative_2366_ = leanh::lean_ctor_get(v___x_2365_, 0);
                v_toFunctor_2367_ = leanh::lean_ctor_get(v_toApplicative_2366_, 0);
                v_toSeq_2368_ = leanh::lean_ctor_get(v_toApplicative_2366_, 2);
                v_toSeqLeft_2369_ = leanh::lean_ctor_get(v_toApplicative_2366_, 3);
                v_toSeqRight_2370_ = leanh::lean_ctor_get(v_toApplicative_2366_, 4);
                v___f_2371_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__2;
                v___f_2372_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_2367_, 2);
                v___f_2373_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2373_, 0, v_toFunctor_2367_);
                v___f_2374_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2374_, 0, v_toFunctor_2367_);
                v___x_2375_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2375_, 0, v___f_2373_);
                leanh::lean_ctor_set(v___x_2375_, 1, v___f_2374_);
                leanh::lean_inc(v_toSeqRight_2370_);
                v___f_2376_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2376_, 0, v_toSeqRight_2370_);
                leanh::lean_inc(v_toSeqLeft_2369_);
                v___f_2377_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2377_, 0, v_toSeqLeft_2369_);
                leanh::lean_inc(v_toSeq_2368_);
                v___f_2378_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2378_, 0, v_toSeq_2368_);
                v___x_2379_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2379_, 0, v___x_2375_);
                leanh::lean_ctor_set(v___x_2379_, 1, v___f_2371_);
                leanh::lean_ctor_set(v___x_2379_, 2, v___f_2378_);
                leanh::lean_ctor_set(v___x_2379_, 3, v___f_2377_);
                leanh::lean_ctor_set(v___x_2379_, 4, v___f_2376_);
                v___x_2380_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2380_, 0, v___x_2379_);
                leanh::lean_ctor_set(v___x_2380_, 1, v___f_2372_);
                v___x_2381_ = l_StateRefT_x27_instMonad___redArg(v___x_2380_);
                v_toApplicative_2382_ = leanh::lean_ctor_get(v___x_2381_, 0);
                v_isSharedCheck_2414_ = (!leanh::lean_is_exclusive(v___x_2381_)) as u8;
                if v_isSharedCheck_2414_ == 0 {
                    v_unused_2415_ = leanh::lean_ctor_get(v___x_2381_, 1);
                    leanh::lean_dec(v_unused_2415_);
                    v___x_2384_ = v___x_2381_;
                    v_isShared_2385_ = v_isSharedCheck_2414_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2382_);
                    leanh::lean_dec(v___x_2381_);
                    v___x_2384_ = leanh::lean_box(0);
                    v_isShared_2385_ = v_isSharedCheck_2414_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2386_ = leanh::lean_ctor_get(v_toApplicative_2382_, 0);
                v_toSeq_2387_ = leanh::lean_ctor_get(v_toApplicative_2382_, 2);
                v_toSeqLeft_2388_ = leanh::lean_ctor_get(v_toApplicative_2382_, 3);
                v_toSeqRight_2389_ = leanh::lean_ctor_get(v_toApplicative_2382_, 4);
                v_isSharedCheck_2412_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2382_)) as u8;
                if v_isSharedCheck_2412_ == 0 {
                    v_unused_2413_ = leanh::lean_ctor_get(v_toApplicative_2382_, 1);
                    leanh::lean_dec(v_unused_2413_);
                    v___x_2391_ = v_toApplicative_2382_;
                    v_isShared_2392_ = v_isSharedCheck_2412_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2389_);
                    leanh::lean_inc(v_toSeqLeft_2388_);
                    leanh::lean_inc(v_toSeq_2387_);
                    leanh::lean_inc(v_toFunctor_2386_);
                    leanh::lean_dec(v_toApplicative_2382_);
                    v___x_2391_ = leanh::lean_box(0);
                    v_isShared_2392_ = v_isSharedCheck_2412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2393_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__4;
                v___f_2394_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM___closed__5;
                leanh::lean_inc_ref(v_toFunctor_2386_);
                v___f_2395_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2395_, 0, v_toFunctor_2386_);
                v___f_2396_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2396_, 0, v_toFunctor_2386_);
                v___x_2397_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2397_, 0, v___f_2395_);
                leanh::lean_ctor_set(v___x_2397_, 1, v___f_2396_);
                v___f_2398_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2398_, 0, v_toSeqRight_2389_);
                v___f_2399_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2399_, 0, v_toSeqLeft_2388_);
                v___f_2400_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2400_, 0, v_toSeq_2387_);
                if v_isShared_2392_ == 0 {
                    leanh::lean_ctor_set(v___x_2391_, 4, v___f_2398_);
                    leanh::lean_ctor_set(v___x_2391_, 3, v___f_2399_);
                    leanh::lean_ctor_set(v___x_2391_, 2, v___f_2400_);
                    leanh::lean_ctor_set(v___x_2391_, 1, v___f_2393_);
                    leanh::lean_ctor_set(v___x_2391_, 0, v___x_2397_);
                    v___x_2402_ = v___x_2391_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2411_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2397_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___f_2393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2411_, 2, v___f_2400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2411_, 3, v___f_2399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2411_, 4, v___f_2398_);
                    v___x_2402_ = v_reuseFailAlloc_2411_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2385_ == 0 {
                    leanh::lean_ctor_set(v___x_2384_, 1, v___f_2394_);
                    leanh::lean_ctor_set(v___x_2384_, 0, v___x_2402_);
                    v___x_2404_ = v___x_2384_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2410_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2402_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2410_, 1, v___f_2394_);
                    v___x_2404_ = v_reuseFailAlloc_2410_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v___x_2404_);
                v___x_2405_ = l_instMonadStateOfStateTOfMonad___redArg(v___x_2404_);
                v___x_2406_ = l_instMonadStateOfMonadStateOf___redArg(v___x_2405_);
                v___x_2407_ =
                    leanh::lean_alloc_closure(l_StateT_get as *mut core::ffi::c_void, 4, 3);
                leanh::lean_closure_set(v___x_2407_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2407_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2407_, 2, v___x_2404_);
                v___x_2408_ =
                    leanh::lean_alloc_closure(l_modify as *mut core::ffi::c_void, 4, 3);
                leanh::lean_closure_set(v___x_2408_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2408_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2408_, 2, v___x_2406_);
                v___x_2409_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2409_, 0, v___x_2407_);
                leanh::lean_ctor_set(v___x_2409_, 1, v___x_2408_);
                return v___x_2409_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0()
-> f64 {
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: f64 = 0.0;
    v___x_2416_ = leanh::lean_unsigned_to_nat(0);
    v___x_2417_ = lean_float_of_nat(v___x_2416_);
    return v___x_2417_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption(
    mut v_cls_2419_: *mut leanh::LeanObject,
    mut v_header_2420_: *mut leanh::LeanObject,
    mut v_msgs_2421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: u8 = 0;
    v___x_2422_ = lean_array_get_size(v_msgs_2421_);
    v___x_2423_ = leanh::lean_unsigned_to_nat(0);
    v___x_2424_ = lean_nat_dec_eq(v___x_2422_, v___x_2423_);
    if v___x_2424_ == 0 {
        let mut v___x_2425_: u8 = 0;
        let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2427_: f64 = 0.0;
        let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2425_ = 1;
        v___x_2426_ = leanh::lean_box(0);
        v___x_2427_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0);
        v___x_2428_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__1;
        v___x_2429_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
        leanh::lean_ctor_set(v___x_2429_, 0, v_cls_2419_);
        leanh::lean_ctor_set(v___x_2429_, 1, v___x_2426_);
        leanh::lean_ctor_set(v___x_2429_, 2, v___x_2428_);
        leanh::lean_ctor_set_float(
            v___x_2429_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            v___x_2427_,
        );
        leanh::lean_ctor_set_float(
            v___x_2429_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            v___x_2427_,
        );
        leanh::lean_ctor_set_uint8(
            v___x_2429_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
            v___x_2425_,
        );
        v___x_2430_ = lean_thunk_get_own(v_header_2420_);
        v___x_2431_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2431_, 0, v___x_2429_);
        leanh::lean_ctor_set(v___x_2431_, 1, v___x_2430_);
        leanh::lean_ctor_set(v___x_2431_, 2, v_msgs_2421_);
        v___x_2432_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2432_, 0, v___x_2431_);
        return v___x_2432_;
    } else {
        let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_msgs_2421_);
        leanh::lean_dec(v_cls_2419_);
        v___x_2433_ = leanh::lean_box(0);
        return v___x_2433_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___boxed(
    mut v_cls_2434_: *mut leanh::LeanObject,
    mut v_header_2435_: *mut leanh::LeanObject,
    mut v_msgs_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption(v_cls_2434_, v_header_2435_, v_msgs_2436_);
    leanh::lean_dec_ref(v_header_2435_);
    return v_res_2437_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_push(
    mut v_msgs_2438_: *mut leanh::LeanObject,
    mut v_msg_x3f_2439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_msg_x3f_2439_) == 1 {
        let mut v_val_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2440_ = leanh::lean_ctor_get(v_msg_x3f_2439_, 0);
        leanh::lean_inc(v_val_2440_);
        leanh::lean_dec_ref_known(v_msg_x3f_2439_, 1);
        v___x_2441_ = lean_array_push(v_msgs_2438_, v_val_2440_);
        return v___x_2441_;
    } else {
        leanh::lean_dec(v_msg_x3f_2439_);
        return v_msgs_2438_;
    }
}
pub unsafe fn l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1(
    mut v_e_2444_: *mut leanh::LeanObject,
    mut v_cls_2445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: f64 = 0.0;
    let mut v___x_2448_: u8 = 0;
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = leanh::lean_box(0);
    v___x_2447_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0);
    v___x_2448_ = 1;
    v___x_2449_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__1;
    v___x_2450_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
    leanh::lean_ctor_set(v___x_2450_, 0, v_cls_2445_);
    leanh::lean_ctor_set(v___x_2450_, 1, v___x_2446_);
    leanh::lean_ctor_set(v___x_2450_, 2, v___x_2449_);
    leanh::lean_ctor_set_float(
        v___x_2450_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2447_,
    );
    leanh::lean_ctor_set_float(
        v___x_2450_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        v___x_2447_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2450_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
        v___x_2448_,
    );
    v___x_2451_ = l_Lean_MessageData_ofExpr(v_e_2444_);
    v___x_2452_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1___closed__0;
    v___x_2453_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2453_, 0, v___x_2450_);
    leanh::lean_ctor_set(v___x_2453_, 1, v___x_2451_);
    leanh::lean_ctor_set(v___x_2453_, 2, v___x_2452_);
    return v___x_2453_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__1;
    v___x_2458_ = l_Lean_MessageData_ofFormat(v___x_2457_);
    return v___x_2458_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0(
    mut v_x_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2460_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___lam__0___closed__2);
    return v___x_2460_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg(
    mut v_a_2464_: *mut leanh::LeanObject,
    mut v_b_2465_: *mut leanh::LeanObject,
    mut v___y_2466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toRing_2468_ = leanh::lean_ctor_get(v___y_2466_, 0);
    v_type_2469_ = leanh::lean_ctor_get(v_toRing_2468_, 1);
    v_u_2470_ = leanh::lean_ctor_get(v_toRing_2468_, 2);
    v___x_2471_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg___closed__1;
    leanh::lean_inc(v_u_2470_);
    v___x_2472_ = l_Lean_Level_succ___override(v_u_2470_);
    v___x_2473_ = leanh::lean_box(0);
    v___x_2474_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2474_, 0, v___x_2472_);
    leanh::lean_ctor_set(v___x_2474_, 1, v___x_2473_);
    v___x_2475_ = l_Lean_mkConst(v___x_2471_, v___x_2474_);
    leanh::lean_inc_ref(v_type_2469_);
    v___x_2476_ = l_Lean_mkApp3(v___x_2475_, v_type_2469_, v_a_2464_, v_b_2465_);
    v___x_2477_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2477_, 0, v___x_2476_);
    leanh::lean_ctor_set(v___x_2477_, 1, v___y_2466_);
    v___x_2478_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2478_, 0, v___x_2477_);
    return v___x_2478_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg___boxed(
    mut v_a_2479_: *mut leanh::LeanObject,
    mut v_b_2480_: *mut leanh::LeanObject,
    mut v___y_2481_: *mut leanh::LeanObject,
    mut v___y_2482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2483_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg(v_a_2479_, v_b_2480_, v___y_2481_);
    return v_res_2483_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17_spec__19(
    mut v_msgData_2484_: *mut leanh::LeanObject,
    mut v___y_2485_: *mut leanh::LeanObject,
    mut v___y_2486_: *mut leanh::LeanObject,
    mut v___y_2487_: *mut leanh::LeanObject,
    mut v___y_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2490_ = lean_st_ref_get(v___y_2488_);
    v_env_2491_ = leanh::lean_ctor_get(v___x_2490_, 0);
    leanh::lean_inc_ref(v_env_2491_);
    leanh::lean_dec(v___x_2490_);
    v___x_2492_ = lean_st_ref_get(v___y_2486_);
    v_mctx_2493_ = leanh::lean_ctor_get(v___x_2492_, 0);
    leanh::lean_inc_ref(v_mctx_2493_);
    leanh::lean_dec(v___x_2492_);
    v_lctx_2494_ = leanh::lean_ctor_get(v___y_2485_, 2);
    v_options_2495_ = leanh::lean_ctor_get(v___y_2487_, 2);
    leanh::lean_inc_ref(v_options_2495_);
    leanh::lean_inc_ref(v_lctx_2494_);
    v___x_2496_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2496_, 0, v_env_2491_);
    leanh::lean_ctor_set(v___x_2496_, 1, v_mctx_2493_);
    leanh::lean_ctor_set(v___x_2496_, 2, v_lctx_2494_);
    leanh::lean_ctor_set(v___x_2496_, 3, v_options_2495_);
    v___x_2497_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2497_, 0, v___x_2496_);
    leanh::lean_ctor_set(v___x_2497_, 1, v_msgData_2484_);
    v___x_2498_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2498_, 0, v___x_2497_);
    return v___x_2498_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17_spec__19___boxed(
    mut v_msgData_2499_: *mut leanh::LeanObject,
    mut v___y_2500_: *mut leanh::LeanObject,
    mut v___y_2501_: *mut leanh::LeanObject,
    mut v___y_2502_: *mut leanh::LeanObject,
    mut v___y_2503_: *mut leanh::LeanObject,
    mut v___y_2504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2505_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17_spec__19(v_msgData_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
    leanh::lean_dec(v___y_2503_);
    leanh::lean_dec_ref(v___y_2502_);
    leanh::lean_dec(v___y_2501_);
    leanh::lean_dec_ref(v___y_2500_);
    return v_res_2505_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17___redArg(
    mut v_msg_2506_: *mut leanh::LeanObject,
    mut v___y_2507_: *mut leanh::LeanObject,
    mut v___y_2508_: *mut leanh::LeanObject,
    mut v___y_2509_: *mut leanh::LeanObject,
    mut v___y_2510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2517_: u8 = 0;
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2512_ = leanh::lean_ctor_get(v___y_2509_, 5);
                v___x_2513_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17_spec__19(v_msg_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
                v_a_2514_ = leanh::lean_ctor_get(v___x_2513_, 0);
                v_isSharedCheck_2522_ = (!leanh::lean_is_exclusive(v___x_2513_)) as u8;
                if v_isSharedCheck_2522_ == 0 {
                    v___x_2516_ = v___x_2513_;
                    v_isShared_2517_ = v_isSharedCheck_2522_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2514_);
                    leanh::lean_dec(v___x_2513_);
                    v___x_2516_ = leanh::lean_box(0);
                    v_isShared_2517_ = v_isSharedCheck_2522_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2512_);
                v___x_2518_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2518_, 0, v_ref_2512_);
                leanh::lean_ctor_set(v___x_2518_, 1, v_a_2514_);
                if v_isShared_2517_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2516_, 1);
                    leanh::lean_ctor_set(v___x_2516_, 0, v___x_2518_);
                    v___x_2520_ = v___x_2516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
                    v___x_2520_ = v_reuseFailAlloc_2521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17___redArg___boxed(
    mut v_msg_2523_: *mut leanh::LeanObject,
    mut v___y_2524_: *mut leanh::LeanObject,
    mut v___y_2525_: *mut leanh::LeanObject,
    mut v___y_2526_: *mut leanh::LeanObject,
    mut v___y_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17___redArg(v_msg_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
    leanh::lean_dec(v___y_2527_);
    leanh::lean_dec_ref(v___y_2526_);
    leanh::lean_dec(v___y_2525_);
    leanh::lean_dec_ref(v___y_2524_);
    return v_res_2529_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2531_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___closed__0;
    v___x_2532_ = l_Lean_stringToMessageData(v___x_2531_);
    return v___x_2532_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15(
    mut v_type_2533_: *mut leanh::LeanObject,
    mut v___y_2534_: *mut leanh::LeanObject,
    mut v___y_2535_: *mut leanh::LeanObject,
    mut v___y_2536_: *mut leanh::LeanObject,
    mut v___y_2537_: *mut leanh::LeanObject,
    mut v___y_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2545_: u8 = 0;
    let mut v_val_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2555_: u8 = 0;
    let mut v_a_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2540_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_type_2533_);
                v___x_2541_ = l_Lean_Meta_synthInstance_x3f(
                    v_type_2533_,
                    v___x_2540_,
                    v___y_2535_,
                    v___y_2536_,
                    v___y_2537_,
                    v___y_2538_,
                );
                if leanh::lean_obj_tag(v___x_2541_) == 0 {
                    v_a_2542_ = leanh::lean_ctor_get(v___x_2541_, 0);
                    v_isSharedCheck_2555_ = (!leanh::lean_is_exclusive(v___x_2541_)) as u8;
                    if v_isSharedCheck_2555_ == 0 {
                        v___x_2544_ = v___x_2541_;
                        v_isShared_2545_ = v_isSharedCheck_2555_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2542_);
                        leanh::lean_dec(v___x_2541_);
                        v___x_2544_ = leanh::lean_box(0);
                        v_isShared_2545_ = v_isSharedCheck_2555_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2534_);
                    leanh::lean_dec_ref(v_type_2533_);
                    v_a_2556_ = leanh::lean_ctor_get(v___x_2541_, 0);
                    v_isSharedCheck_2563_ = (!leanh::lean_is_exclusive(v___x_2541_)) as u8;
                    if v_isSharedCheck_2563_ == 0 {
                        v___x_2558_ = v___x_2541_;
                        v_isShared_2559_ = v_isSharedCheck_2563_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2556_);
                        leanh::lean_dec(v___x_2541_);
                        v___x_2558_ = leanh::lean_box(0);
                        v_isShared_2559_ = v_isSharedCheck_2563_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2542_) == 1 {
                    leanh::lean_dec_ref(v_type_2533_);
                    v_val_2546_ = leanh::lean_ctor_get(v_a_2542_, 0);
                    leanh::lean_inc(v_val_2546_);
                    leanh::lean_dec_ref_known(v_a_2542_, 1);
                    v___x_2547_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2547_, 0, v_val_2546_);
                    leanh::lean_ctor_set(v___x_2547_, 1, v___y_2534_);
                    if v_isShared_2545_ == 0 {
                        leanh::lean_ctor_set(v___x_2544_, 0, v___x_2547_);
                        v___x_2549_ = v___x_2544_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2550_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
                        v___x_2549_ = v_reuseFailAlloc_2550_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2544_);
                    leanh::lean_dec(v_a_2542_);
                    leanh::lean_dec_ref(v___y_2534_);
                    v___x_2551_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___closed__1_once), _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___closed__1);
                    v___x_2552_ = l_Lean_indentExpr(v_type_2533_);
                    v___x_2553_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2553_, 0, v___x_2551_);
                    leanh::lean_ctor_set(v___x_2553_, 1, v___x_2552_);
                    v___x_2554_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17___redArg(v___x_2553_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
                    return v___x_2554_;
                }
            }
            2 => {
                return v___x_2549_;
            }
            3 => {
                if v_isShared_2559_ == 0 {
                    v___x_2561_ = v___x_2558_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
                    v___x_2561_ = v_reuseFailAlloc_2562_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2561_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15___boxed(
    mut v_type_2564_: *mut leanh::LeanObject,
    mut v___y_2565_: *mut leanh::LeanObject,
    mut v___y_2566_: *mut leanh::LeanObject,
    mut v___y_2567_: *mut leanh::LeanObject,
    mut v___y_2568_: *mut leanh::LeanObject,
    mut v___y_2569_: *mut leanh::LeanObject,
    mut v___y_2570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2571_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15(v_type_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
    leanh::lean_dec(v___y_2569_);
    leanh::lean_dec_ref(v___y_2568_);
    leanh::lean_dec(v___y_2567_);
    leanh::lean_dec_ref(v___y_2566_);
    return v_res_2571_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11(
    mut v_type_2572_: *mut leanh::LeanObject,
    mut v_u_2573_: *mut leanh::LeanObject,
    mut v_instDeclName_2574_: *mut leanh::LeanObject,
    mut v_declName_2575_: *mut leanh::LeanObject,
    mut v_expectedInst_2576_: *mut leanh::LeanObject,
    mut v___y_2577_: *mut leanh::LeanObject,
    mut v___y_2578_: *mut leanh::LeanObject,
    mut v___y_2579_: *mut leanh::LeanObject,
    mut v___y_2580_: *mut leanh::LeanObject,
    mut v___y_2581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2593_: u8 = 0;
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2597_: u8 = 0;
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut v_unused_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2611_: u8 = 0;
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2583_ = leanh::lean_box(0);
                v___x_2584_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2584_, 0, v_u_2573_);
                leanh::lean_ctor_set(v___x_2584_, 1, v___x_2583_);
                leanh::lean_inc_ref(v___x_2584_);
                v___x_2585_ = l_Lean_mkConst(v_instDeclName_2574_, v___x_2584_);
                leanh::lean_inc_ref(v_type_2572_);
                v___x_2586_ = l_Lean_Expr_app___override(v___x_2585_, v_type_2572_);
                v___x_2587_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15(v___x_2586_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
                if leanh::lean_obj_tag(v___x_2587_) == 0 {
                    v_a_2588_ = leanh::lean_ctor_get(v___x_2587_, 0);
                    leanh::lean_inc(v_a_2588_);
                    leanh::lean_dec_ref_known(v___x_2587_, 1);
                    v_fst_2589_ = leanh::lean_ctor_get(v_a_2588_, 0);
                    v_snd_2590_ = leanh::lean_ctor_get(v_a_2588_, 1);
                    v_isSharedCheck_2616_ = (!leanh::lean_is_exclusive(v_a_2588_)) as u8;
                    if v_isSharedCheck_2616_ == 0 {
                        v___x_2592_ = v_a_2588_;
                        v_isShared_2593_ = v_isSharedCheck_2616_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2590_);
                        leanh::lean_inc(v_fst_2589_);
                        leanh::lean_dec(v_a_2588_);
                        v___x_2592_ = leanh::lean_box(0);
                        v_isShared_2593_ = v_isSharedCheck_2616_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2584_, 2);
                    leanh::lean_dec_ref(v_expectedInst_2576_);
                    leanh::lean_dec(v_declName_2575_);
                    leanh::lean_dec_ref(v_type_2572_);
                    return v___x_2587_;
                }
            }
            1 => {
                leanh::lean_inc(v_fst_2589_);
                leanh::lean_inc(v_declName_2575_);
                v___x_2594_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                    v_declName_2575_,
                    v_fst_2589_,
                    v_expectedInst_2576_,
                    v___y_2578_,
                    v___y_2579_,
                    v___y_2580_,
                    v___y_2581_,
                );
                if leanh::lean_obj_tag(v___x_2594_) == 0 {
                    v_isSharedCheck_2606_ = (!leanh::lean_is_exclusive(v___x_2594_)) as u8;
                    if v_isSharedCheck_2606_ == 0 {
                        v_unused_2607_ = leanh::lean_ctor_get(v___x_2594_, 0);
                        leanh::lean_dec(v_unused_2607_);
                        v___x_2596_ = v___x_2594_;
                        v_isShared_2597_ = v_isSharedCheck_2606_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2594_);
                        v___x_2596_ = leanh::lean_box(0);
                        v_isShared_2597_ = v_isSharedCheck_2606_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2592_);
                    leanh::lean_dec(v_snd_2590_);
                    leanh::lean_dec(v_fst_2589_);
                    leanh::lean_dec_ref_known(v___x_2584_, 2);
                    leanh::lean_dec(v_declName_2575_);
                    leanh::lean_dec_ref(v_type_2572_);
                    v_a_2608_ = leanh::lean_ctor_get(v___x_2594_, 0);
                    v_isSharedCheck_2615_ = (!leanh::lean_is_exclusive(v___x_2594_)) as u8;
                    if v_isSharedCheck_2615_ == 0 {
                        v___x_2610_ = v___x_2594_;
                        v_isShared_2611_ = v_isSharedCheck_2615_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2608_);
                        leanh::lean_dec(v___x_2594_);
                        v___x_2610_ = leanh::lean_box(0);
                        v_isShared_2611_ = v_isSharedCheck_2615_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2598_ = l_Lean_mkConst(v_declName_2575_, v___x_2584_);
                v___x_2599_ = l_Lean_mkAppB(v___x_2598_, v_type_2572_, v_fst_2589_);
                if v_isShared_2593_ == 0 {
                    leanh::lean_ctor_set(v___x_2592_, 0, v___x_2599_);
                    v___x_2601_ = v___x_2592_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_snd_2590_);
                    v___x_2601_ = v_reuseFailAlloc_2605_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2597_ == 0 {
                    leanh::lean_ctor_set(v___x_2596_, 0, v___x_2601_);
                    v___x_2603_ = v___x_2596_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2604_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
                    v___x_2603_ = v_reuseFailAlloc_2604_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2603_;
            }
            5 => {
                if v_isShared_2611_ == 0 {
                    v___x_2613_ = v___x_2610_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2614_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
                    v___x_2613_ = v_reuseFailAlloc_2614_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2613_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11___boxed(
    mut v_type_2617_: *mut leanh::LeanObject,
    mut v_u_2618_: *mut leanh::LeanObject,
    mut v_instDeclName_2619_: *mut leanh::LeanObject,
    mut v_declName_2620_: *mut leanh::LeanObject,
    mut v_expectedInst_2621_: *mut leanh::LeanObject,
    mut v___y_2622_: *mut leanh::LeanObject,
    mut v___y_2623_: *mut leanh::LeanObject,
    mut v___y_2624_: *mut leanh::LeanObject,
    mut v___y_2625_: *mut leanh::LeanObject,
    mut v___y_2626_: *mut leanh::LeanObject,
    mut v___y_2627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2628_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11(v_type_2617_, v_u_2618_, v_instDeclName_2619_, v_declName_2620_, v_expectedInst_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
    leanh::lean_dec(v___y_2626_);
    leanh::lean_dec_ref(v___y_2625_);
    leanh::lean_dec(v___y_2624_);
    leanh::lean_dec_ref(v___y_2623_);
    return v_res_2628_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5(
    mut v___y_2645_: *mut leanh::LeanObject,
    mut v___y_2646_: *mut leanh::LeanObject,
    mut v___y_2647_: *mut leanh::LeanObject,
    mut v___y_2648_: *mut leanh::LeanObject,
    mut v___y_2649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2656_: u8 = 0;
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2661_: u8 = 0;
    let mut v_type_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2676_: u8 = 0;
    let mut v_snd_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRing_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2682_: u8 = 0;
    let mut v_invFn_x3f_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2696_: u8 = 0;
    let mut v_invSet_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2700_: u8 = 0;
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2703_: u8 = 0;
    let mut v_id_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2722_: u8 = 0;
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut v_unused_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut v_unused_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2740_: u8 = 0;
    let mut v_unused_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2651_ = leanh::lean_ctor_get(v___y_2645_, 0);
                v_negFn_x3f_2652_ = leanh::lean_ctor_get(v_toRing_2651_, 9);
                leanh::lean_inc(v_negFn_x3f_2652_);
                if leanh::lean_obj_tag(v_negFn_x3f_2652_) == 1 {
                    v_val_2653_ = leanh::lean_ctor_get(v_negFn_x3f_2652_, 0);
                    v_isSharedCheck_2661_ =
                        (!leanh::lean_is_exclusive(v_negFn_x3f_2652_)) as u8;
                    if v_isSharedCheck_2661_ == 0 {
                        v___x_2655_ = v_negFn_x3f_2652_;
                        v_isShared_2656_ = v_isSharedCheck_2661_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2653_);
                        leanh::lean_dec(v_negFn_x3f_2652_);
                        v___x_2655_ = leanh::lean_box(0);
                        v_isShared_2656_ = v_isSharedCheck_2661_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_negFn_x3f_2652_);
                    v_type_2662_ = leanh::lean_ctor_get(v_toRing_2651_, 1);
                    leanh::lean_inc_ref_n(v_type_2662_, 2);
                    v_u_2663_ = leanh::lean_ctor_get(v_toRing_2651_, 2);
                    leanh::lean_inc_n(v_u_2663_, 2);
                    v_ringInst_2664_ = leanh::lean_ctor_get(v_toRing_2651_, 3);
                    v___x_2665_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__4;
                    v___x_2666_ = leanh::lean_box(0);
                    v___x_2667_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2667_, 0, v_u_2663_);
                    leanh::lean_ctor_set(v___x_2667_, 1, v___x_2666_);
                    v___x_2668_ = l_Lean_mkConst(v___x_2665_, v___x_2667_);
                    leanh::lean_inc_ref(v_ringInst_2664_);
                    v_expectedInst_2669_ =
                        l_Lean_mkAppB(v___x_2668_, v_type_2662_, v_ringInst_2664_);
                    v___x_2670_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__6;
                    v___x_2671_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___closed__8;
                    v___x_2672_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11(v_type_2662_, v_u_2663_, v___x_2670_, v___x_2671_, v_expectedInst_2669_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
                    if leanh::lean_obj_tag(v___x_2672_) == 0 {
                        v_a_2673_ = leanh::lean_ctor_get(v___x_2672_, 0);
                        v_isSharedCheck_2742_ =
                            (!leanh::lean_is_exclusive(v___x_2672_)) as u8;
                        if v_isSharedCheck_2742_ == 0 {
                            v___x_2675_ = v___x_2672_;
                            v_isShared_2676_ = v_isSharedCheck_2742_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2673_);
                            leanh::lean_dec(v___x_2672_);
                            v___x_2675_ = leanh::lean_box(0);
                            v_isShared_2676_ = v_isSharedCheck_2742_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_2672_;
                    }
                }
            }
            1 => {
                v___x_2657_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2657_, 0, v_val_2653_);
                leanh::lean_ctor_set(v___x_2657_, 1, v___y_2645_);
                if v_isShared_2656_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2655_, 0);
                    leanh::lean_ctor_set(v___x_2655_, 0, v___x_2657_);
                    v___x_2659_ = v___x_2655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2660_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
                    v___x_2659_ = v_reuseFailAlloc_2660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2659_;
            }
            3 => {
                v_snd_2677_ = leanh::lean_ctor_get(v_a_2673_, 1);
                leanh::lean_inc(v_snd_2677_);
                v_toRing_2678_ = leanh::lean_ctor_get(v_snd_2677_, 0);
                leanh::lean_inc_ref(v_toRing_2678_);
                v_fst_2679_ = leanh::lean_ctor_get(v_a_2673_, 0);
                v_isSharedCheck_2740_ = (!leanh::lean_is_exclusive(v_a_2673_)) as u8;
                if v_isSharedCheck_2740_ == 0 {
                    v_unused_2741_ = leanh::lean_ctor_get(v_a_2673_, 1);
                    leanh::lean_dec(v_unused_2741_);
                    v___x_2681_ = v_a_2673_;
                    v_isShared_2682_ = v_isSharedCheck_2740_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_2679_);
                    leanh::lean_dec(v_a_2673_);
                    v___x_2681_ = leanh::lean_box(0);
                    v_isShared_2682_ = v_isSharedCheck_2740_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_invFn_x3f_2683_ = leanh::lean_ctor_get(v_snd_2677_, 1);
                v_semiringId_x3f_2684_ = leanh::lean_ctor_get(v_snd_2677_, 2);
                v_commSemiringInst_2685_ = leanh::lean_ctor_get(v_snd_2677_, 3);
                v_commRingInst_2686_ = leanh::lean_ctor_get(v_snd_2677_, 4);
                v_noZeroDivInst_x3f_2687_ = leanh::lean_ctor_get(v_snd_2677_, 5);
                v_fieldInst_x3f_2688_ = leanh::lean_ctor_get(v_snd_2677_, 6);
                v_powIdentityInst_x3f_2689_ = leanh::lean_ctor_get(v_snd_2677_, 7);
                v_denoteEntries_2690_ = leanh::lean_ctor_get(v_snd_2677_, 8);
                v_nextId_2691_ = leanh::lean_ctor_get(v_snd_2677_, 9);
                v_steps_2692_ = leanh::lean_ctor_get(v_snd_2677_, 10);
                v_queue_2693_ = leanh::lean_ctor_get(v_snd_2677_, 11);
                v_basis_2694_ = leanh::lean_ctor_get(v_snd_2677_, 12);
                v_diseqs_2695_ = leanh::lean_ctor_get(v_snd_2677_, 13);
                v_recheck_2696_ = leanh::lean_ctor_get_uint8(
                    v_snd_2677_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2697_ = leanh::lean_ctor_get(v_snd_2677_, 14);
                v_powIdentityVarCount_2698_ = leanh::lean_ctor_get(v_snd_2677_, 15);
                v_numEq0_x3f_2699_ = leanh::lean_ctor_get(v_snd_2677_, 16);
                v_numEq0Updated_2700_ = leanh::lean_ctor_get_uint8(
                    v_snd_2677_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2738_ = (!leanh::lean_is_exclusive(v_snd_2677_)) as u8;
                if v_isSharedCheck_2738_ == 0 {
                    v_unused_2739_ = leanh::lean_ctor_get(v_snd_2677_, 0);
                    leanh::lean_dec(v_unused_2739_);
                    v___x_2702_ = v_snd_2677_;
                    v_isShared_2703_ = v_isSharedCheck_2738_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_2699_);
                    leanh::lean_inc(v_powIdentityVarCount_2698_);
                    leanh::lean_inc(v_invSet_2697_);
                    leanh::lean_inc(v_diseqs_2695_);
                    leanh::lean_inc(v_basis_2694_);
                    leanh::lean_inc(v_queue_2693_);
                    leanh::lean_inc(v_steps_2692_);
                    leanh::lean_inc(v_nextId_2691_);
                    leanh::lean_inc(v_denoteEntries_2690_);
                    leanh::lean_inc(v_powIdentityInst_x3f_2689_);
                    leanh::lean_inc(v_fieldInst_x3f_2688_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_2687_);
                    leanh::lean_inc(v_commRingInst_2686_);
                    leanh::lean_inc(v_commSemiringInst_2685_);
                    leanh::lean_inc(v_semiringId_x3f_2684_);
                    leanh::lean_inc(v_invFn_x3f_2683_);
                    leanh::lean_dec(v_snd_2677_);
                    v___x_2702_ = leanh::lean_box(0);
                    v_isShared_2703_ = v_isSharedCheck_2738_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_id_2704_ = leanh::lean_ctor_get(v_toRing_2678_, 0);
                v_type_2705_ = leanh::lean_ctor_get(v_toRing_2678_, 1);
                v_u_2706_ = leanh::lean_ctor_get(v_toRing_2678_, 2);
                v_ringInst_2707_ = leanh::lean_ctor_get(v_toRing_2678_, 3);
                v_semiringInst_2708_ = leanh::lean_ctor_get(v_toRing_2678_, 4);
                v_charInst_x3f_2709_ = leanh::lean_ctor_get(v_toRing_2678_, 5);
                v_addFn_x3f_2710_ = leanh::lean_ctor_get(v_toRing_2678_, 6);
                v_mulFn_x3f_2711_ = leanh::lean_ctor_get(v_toRing_2678_, 7);
                v_subFn_x3f_2712_ = leanh::lean_ctor_get(v_toRing_2678_, 8);
                v_powFn_x3f_2713_ = leanh::lean_ctor_get(v_toRing_2678_, 10);
                v_intCastFn_x3f_2714_ = leanh::lean_ctor_get(v_toRing_2678_, 11);
                v_natCastFn_x3f_2715_ = leanh::lean_ctor_get(v_toRing_2678_, 12);
                v_one_x3f_2716_ = leanh::lean_ctor_get(v_toRing_2678_, 13);
                v_vars_2717_ = leanh::lean_ctor_get(v_toRing_2678_, 14);
                v_varMap_2718_ = leanh::lean_ctor_get(v_toRing_2678_, 15);
                v_denote_2719_ = leanh::lean_ctor_get(v_toRing_2678_, 16);
                v_isSharedCheck_2736_ = (!leanh::lean_is_exclusive(v_toRing_2678_)) as u8;
                if v_isSharedCheck_2736_ == 0 {
                    v_unused_2737_ = leanh::lean_ctor_get(v_toRing_2678_, 9);
                    leanh::lean_dec(v_unused_2737_);
                    v___x_2721_ = v_toRing_2678_;
                    v_isShared_2722_ = v_isSharedCheck_2736_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_2719_);
                    leanh::lean_inc(v_varMap_2718_);
                    leanh::lean_inc(v_vars_2717_);
                    leanh::lean_inc(v_one_x3f_2716_);
                    leanh::lean_inc(v_natCastFn_x3f_2715_);
                    leanh::lean_inc(v_intCastFn_x3f_2714_);
                    leanh::lean_inc(v_powFn_x3f_2713_);
                    leanh::lean_inc(v_subFn_x3f_2712_);
                    leanh::lean_inc(v_mulFn_x3f_2711_);
                    leanh::lean_inc(v_addFn_x3f_2710_);
                    leanh::lean_inc(v_charInst_x3f_2709_);
                    leanh::lean_inc(v_semiringInst_2708_);
                    leanh::lean_inc(v_ringInst_2707_);
                    leanh::lean_inc(v_u_2706_);
                    leanh::lean_inc(v_type_2705_);
                    leanh::lean_inc(v_id_2704_);
                    leanh::lean_dec(v_toRing_2678_);
                    v___x_2721_ = leanh::lean_box(0);
                    v_isShared_2722_ = v_isSharedCheck_2736_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc(v_fst_2679_);
                v___x_2723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2723_, 0, v_fst_2679_);
                if v_isShared_2722_ == 0 {
                    leanh::lean_ctor_set(v___x_2721_, 9, v___x_2723_);
                    v___x_2725_ = v___x_2721_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_id_2704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_type_2705_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_u_2706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 3, v_ringInst_2707_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 4, v_semiringInst_2708_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 5, v_charInst_x3f_2709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 6, v_addFn_x3f_2710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 7, v_mulFn_x3f_2711_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 8, v_subFn_x3f_2712_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 9, v___x_2723_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 10, v_powFn_x3f_2713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 11, v_intCastFn_x3f_2714_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 12, v_natCastFn_x3f_2715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 13, v_one_x3f_2716_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 14, v_vars_2717_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 15, v_varMap_2718_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 16, v_denote_2719_);
                    v___x_2725_ = v_reuseFailAlloc_2735_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2703_ == 0 {
                    leanh::lean_ctor_set(v___x_2702_, 0, v___x_2725_);
                    v___x_2727_ = v___x_2702_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2734_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2725_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_invFn_x3f_2683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 2, v_semiringId_x3f_2684_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2734_,
                        3,
                        v_commSemiringInst_2685_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 4, v_commRingInst_2686_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2734_,
                        5,
                        v_noZeroDivInst_x3f_2687_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 6, v_fieldInst_x3f_2688_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2734_,
                        7,
                        v_powIdentityInst_x3f_2689_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 8, v_denoteEntries_2690_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 9, v_nextId_2691_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 10, v_steps_2692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 11, v_queue_2693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 12, v_basis_2694_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 13, v_diseqs_2695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 14, v_invSet_2697_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2734_,
                        15,
                        v_powIdentityVarCount_2698_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 16, v_numEq0_x3f_2699_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2734_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_2696_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2734_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_2700_,
                    );
                    v___x_2727_ = v_reuseFailAlloc_2734_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2682_ == 0 {
                    leanh::lean_ctor_set(v___x_2681_, 1, v___x_2727_);
                    v___x_2729_ = v___x_2681_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_fst_2679_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 1, v___x_2727_);
                    v___x_2729_ = v_reuseFailAlloc_2733_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2676_ == 0 {
                    leanh::lean_ctor_set(v___x_2675_, 0, v___x_2729_);
                    v___x_2731_ = v___x_2675_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
                    v___x_2731_ = v_reuseFailAlloc_2732_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5___boxed(
    mut v___y_2743_: *mut leanh::LeanObject,
    mut v___y_2744_: *mut leanh::LeanObject,
    mut v___y_2745_: *mut leanh::LeanObject,
    mut v___y_2746_: *mut leanh::LeanObject,
    mut v___y_2747_: *mut leanh::LeanObject,
    mut v___y_2748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2749_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5(v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
    leanh::lean_dec(v___y_2747_);
    leanh::lean_dec_ref(v___y_2746_);
    leanh::lean_dec(v___y_2745_);
    leanh::lean_dec_ref(v___y_2744_);
    return v_res_2749_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2757_ = leanh::lean_unsigned_to_nat(0);
    v___x_2758_ = lean_nat_to_int(v___x_2757_);
    return v___x_2758_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1(
    mut v_k_2765_: *mut leanh::LeanObject,
    mut v___y_2766_: *mut leanh::LeanObject,
    mut v___y_2767_: *mut leanh::LeanObject,
    mut v___y_2768_: *mut leanh::LeanObject,
    mut v___y_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v_ofNatInst_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2809_: u8 = 0;
    let mut v_fst_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2822_: u8 = 0;
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_val_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_a_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2772_ = leanh::lean_ctor_get(v___y_2766_, 0);
                v_type_2773_ = leanh::lean_ctor_get(v_toRing_2772_, 1);
                leanh::lean_inc_ref_n(v_type_2773_, 2);
                v_u_2774_ = leanh::lean_ctor_get(v_toRing_2772_, 2);
                v_semiringInst_2775_ = leanh::lean_ctor_get(v_toRing_2772_, 4);
                v___x_2776_ = lean_nat_abs(v_k_2765_);
                v_n_2777_ = l_Lean_mkRawNatLit(v___x_2776_);
                v___x_2778_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__1;
                v___x_2779_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2774_);
                v___x_2780_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2780_, 0, v_u_2774_);
                leanh::lean_ctor_set(v___x_2780_, 1, v___x_2779_);
                leanh::lean_inc_ref(v___x_2780_);
                v___x_2781_ = l_Lean_mkConst(v___x_2778_, v___x_2780_);
                leanh::lean_inc_ref(v_n_2777_);
                v___x_2782_ = l_Lean_mkAppB(v___x_2781_, v_type_2773_, v_n_2777_);
                v___x_2783_ = leanh::lean_box(0);
                v___x_2784_ = l_Lean_Meta_synthInstance_x3f(
                    v___x_2782_,
                    v___x_2783_,
                    v___y_2767_,
                    v___y_2768_,
                    v___y_2769_,
                    v___y_2770_,
                );
                if leanh::lean_obj_tag(v___x_2784_) == 0 {
                    v_a_2785_ = leanh::lean_ctor_get(v___x_2784_, 0);
                    v_isSharedCheck_2828_ = (!leanh::lean_is_exclusive(v___x_2784_)) as u8;
                    if v_isSharedCheck_2828_ == 0 {
                        v___x_2787_ = v___x_2784_;
                        v_isShared_2788_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2785_);
                        leanh::lean_dec(v___x_2784_);
                        v___x_2787_ = leanh::lean_box(0);
                        v_isShared_2788_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2780_, 2);
                    leanh::lean_dec_ref(v_n_2777_);
                    leanh::lean_dec_ref(v_type_2773_);
                    leanh::lean_dec_ref(v___y_2766_);
                    v_a_2829_ = leanh::lean_ctor_get(v___x_2784_, 0);
                    v_isSharedCheck_2836_ = (!leanh::lean_is_exclusive(v___x_2784_)) as u8;
                    if v_isSharedCheck_2836_ == 0 {
                        v___x_2831_ = v___x_2784_;
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2829_);
                        leanh::lean_dec(v___x_2784_);
                        v___x_2831_ = leanh::lean_box(0);
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2785_) == 1 {
                    v_val_2824_ = leanh::lean_ctor_get(v_a_2785_, 0);
                    leanh::lean_inc(v_val_2824_);
                    leanh::lean_dec_ref_known(v_a_2785_, 1);
                    v_ofNatInst_2790_ = v_val_2824_;
                    v___y_2791_ = v___y_2766_;
                    v___y_2792_ = v___y_2767_;
                    v___y_2793_ = v___y_2768_;
                    v___y_2794_ = v___y_2769_;
                    v___y_2795_ = v___y_2770_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_a_2785_);
                    v___x_2825_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__6;
                    leanh::lean_inc_ref(v___x_2780_);
                    v___x_2826_ = l_Lean_mkConst(v___x_2825_, v___x_2780_);
                    leanh::lean_inc_ref(v_n_2777_);
                    leanh::lean_inc_ref(v_semiringInst_2775_);
                    leanh::lean_inc_ref(v_type_2773_);
                    v___x_2827_ =
                        l_Lean_mkApp3(v___x_2826_, v_type_2773_, v_semiringInst_2775_, v_n_2777_);
                    v_ofNatInst_2790_ = v___x_2827_;
                    v___y_2791_ = v___y_2766_;
                    v___y_2792_ = v___y_2767_;
                    v___y_2793_ = v___y_2768_;
                    v___y_2794_ = v___y_2769_;
                    v___y_2795_ = v___y_2770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2796_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__3;
                v___x_2797_ = l_Lean_mkConst(v___x_2796_, v___x_2780_);
                v_n_2798_ = l_Lean_mkApp3(v___x_2797_, v_type_2773_, v_n_2777_, v_ofNatInst_2790_);
                v___x_2799_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4);
                v___x_2800_ = lean_int_dec_lt(v_k_2765_, v___x_2799_);
                if v___x_2800_ == 0 {
                    v___x_2801_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2801_, 0, v_n_2798_);
                    leanh::lean_ctor_set(v___x_2801_, 1, v___y_2791_);
                    if v_isShared_2788_ == 0 {
                        leanh::lean_ctor_set(v___x_2787_, 0, v___x_2801_);
                        v___x_2803_ = v___x_2787_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2804_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
                        v___x_2803_ = v_reuseFailAlloc_2804_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2787_);
                    v___x_2805_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5(v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
                    if leanh::lean_obj_tag(v___x_2805_) == 0 {
                        v_a_2806_ = leanh::lean_ctor_get(v___x_2805_, 0);
                        v_isSharedCheck_2823_ =
                            (!leanh::lean_is_exclusive(v___x_2805_)) as u8;
                        if v_isSharedCheck_2823_ == 0 {
                            v___x_2808_ = v___x_2805_;
                            v_isShared_2809_ = v_isSharedCheck_2823_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2806_);
                            leanh::lean_dec(v___x_2805_);
                            v___x_2808_ = leanh::lean_box(0);
                            v_isShared_2809_ = v_isSharedCheck_2823_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_n_2798_);
                        return v___x_2805_;
                    }
                }
            }
            3 => {
                return v___x_2803_;
            }
            4 => {
                v_fst_2810_ = leanh::lean_ctor_get(v_a_2806_, 0);
                v_snd_2811_ = leanh::lean_ctor_get(v_a_2806_, 1);
                v_isSharedCheck_2822_ = (!leanh::lean_is_exclusive(v_a_2806_)) as u8;
                if v_isSharedCheck_2822_ == 0 {
                    v___x_2813_ = v_a_2806_;
                    v_isShared_2814_ = v_isSharedCheck_2822_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2811_);
                    leanh::lean_inc(v_fst_2810_);
                    leanh::lean_dec(v_a_2806_);
                    v___x_2813_ = leanh::lean_box(0);
                    v_isShared_2814_ = v_isSharedCheck_2822_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2815_ = l_Lean_Expr_app___override(v_fst_2810_, v_n_2798_);
                if v_isShared_2814_ == 0 {
                    leanh::lean_ctor_set(v___x_2813_, 0, v___x_2815_);
                    v___x_2817_ = v___x_2813_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2821_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_snd_2811_);
                    v___x_2817_ = v_reuseFailAlloc_2821_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2809_ == 0 {
                    leanh::lean_ctor_set(v___x_2808_, 0, v___x_2817_);
                    v___x_2819_ = v___x_2808_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2820_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
                    v___x_2819_ = v_reuseFailAlloc_2820_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2819_;
            }
            8 => {
                if v_isShared_2832_ == 0 {
                    v___x_2834_ = v___x_2831_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
                    v___x_2834_ = v_reuseFailAlloc_2835_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___boxed(
    mut v_k_2837_: *mut leanh::LeanObject,
    mut v___y_2838_: *mut leanh::LeanObject,
    mut v___y_2839_: *mut leanh::LeanObject,
    mut v___y_2840_: *mut leanh::LeanObject,
    mut v___y_2841_: *mut leanh::LeanObject,
    mut v___y_2842_: *mut leanh::LeanObject,
    mut v___y_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2844_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1(v_k_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
    leanh::lean_dec(v___y_2842_);
    leanh::lean_dec_ref(v___y_2841_);
    leanh::lean_dec(v___y_2840_);
    leanh::lean_dec_ref(v___y_2839_);
    leanh::lean_dec(v_k_2837_);
    return v_res_2844_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5_spec__7(
    mut v_type_2845_: *mut leanh::LeanObject,
    mut v_u_2846_: *mut leanh::LeanObject,
    mut v_instDeclName_2847_: *mut leanh::LeanObject,
    mut v_declName_2848_: *mut leanh::LeanObject,
    mut v_expectedInst_2849_: *mut leanh::LeanObject,
    mut v___y_2850_: *mut leanh::LeanObject,
    mut v___y_2851_: *mut leanh::LeanObject,
    mut v___y_2852_: *mut leanh::LeanObject,
    mut v___y_2853_: *mut leanh::LeanObject,
    mut v___y_2854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2868_: u8 = 0;
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2881_: u8 = 0;
    let mut v_unused_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2890_: u8 = 0;
    let mut v_isSharedCheck_2891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2856_ = leanh::lean_box(0);
                leanh::lean_inc_n(v_u_2846_, 2);
                v___x_2857_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2857_, 0, v_u_2846_);
                leanh::lean_ctor_set(v___x_2857_, 1, v___x_2856_);
                v___x_2858_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2858_, 0, v_u_2846_);
                leanh::lean_ctor_set(v___x_2858_, 1, v___x_2857_);
                v___x_2859_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2859_, 0, v_u_2846_);
                leanh::lean_ctor_set(v___x_2859_, 1, v___x_2858_);
                leanh::lean_inc_ref(v___x_2859_);
                v___x_2860_ = l_Lean_mkConst(v_instDeclName_2847_, v___x_2859_);
                leanh::lean_inc_ref_n(v_type_2845_, 3);
                v___x_2861_ = l_Lean_mkApp3(v___x_2860_, v_type_2845_, v_type_2845_, v_type_2845_);
                v___x_2862_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15(v___x_2861_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
                if leanh::lean_obj_tag(v___x_2862_) == 0 {
                    v_a_2863_ = leanh::lean_ctor_get(v___x_2862_, 0);
                    leanh::lean_inc(v_a_2863_);
                    leanh::lean_dec_ref_known(v___x_2862_, 1);
                    v_fst_2864_ = leanh::lean_ctor_get(v_a_2863_, 0);
                    v_snd_2865_ = leanh::lean_ctor_get(v_a_2863_, 1);
                    v_isSharedCheck_2891_ = (!leanh::lean_is_exclusive(v_a_2863_)) as u8;
                    if v_isSharedCheck_2891_ == 0 {
                        v___x_2867_ = v_a_2863_;
                        v_isShared_2868_ = v_isSharedCheck_2891_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2865_);
                        leanh::lean_inc(v_fst_2864_);
                        leanh::lean_dec(v_a_2863_);
                        v___x_2867_ = leanh::lean_box(0);
                        v_isShared_2868_ = v_isSharedCheck_2891_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2859_, 2);
                    leanh::lean_dec_ref(v_expectedInst_2849_);
                    leanh::lean_dec(v_declName_2848_);
                    leanh::lean_dec_ref(v_type_2845_);
                    return v___x_2862_;
                }
            }
            1 => {
                leanh::lean_inc(v_fst_2864_);
                leanh::lean_inc(v_declName_2848_);
                v___x_2869_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                    v_declName_2848_,
                    v_fst_2864_,
                    v_expectedInst_2849_,
                    v___y_2851_,
                    v___y_2852_,
                    v___y_2853_,
                    v___y_2854_,
                );
                if leanh::lean_obj_tag(v___x_2869_) == 0 {
                    v_isSharedCheck_2881_ = (!leanh::lean_is_exclusive(v___x_2869_)) as u8;
                    if v_isSharedCheck_2881_ == 0 {
                        v_unused_2882_ = leanh::lean_ctor_get(v___x_2869_, 0);
                        leanh::lean_dec(v_unused_2882_);
                        v___x_2871_ = v___x_2869_;
                        v_isShared_2872_ = v_isSharedCheck_2881_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2869_);
                        v___x_2871_ = leanh::lean_box(0);
                        v_isShared_2872_ = v_isSharedCheck_2881_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2867_);
                    leanh::lean_dec(v_snd_2865_);
                    leanh::lean_dec(v_fst_2864_);
                    leanh::lean_dec_ref_known(v___x_2859_, 2);
                    leanh::lean_dec(v_declName_2848_);
                    leanh::lean_dec_ref(v_type_2845_);
                    v_a_2883_ = leanh::lean_ctor_get(v___x_2869_, 0);
                    v_isSharedCheck_2890_ = (!leanh::lean_is_exclusive(v___x_2869_)) as u8;
                    if v_isSharedCheck_2890_ == 0 {
                        v___x_2885_ = v___x_2869_;
                        v_isShared_2886_ = v_isSharedCheck_2890_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2883_);
                        leanh::lean_dec(v___x_2869_);
                        v___x_2885_ = leanh::lean_box(0);
                        v_isShared_2886_ = v_isSharedCheck_2890_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2873_ = l_Lean_mkConst(v_declName_2848_, v___x_2859_);
                leanh::lean_inc_ref_n(v_type_2845_, 2);
                v___x_2874_ = l_Lean_mkApp4(
                    v___x_2873_,
                    v_type_2845_,
                    v_type_2845_,
                    v_type_2845_,
                    v_fst_2864_,
                );
                if v_isShared_2868_ == 0 {
                    leanh::lean_ctor_set(v___x_2867_, 0, v___x_2874_);
                    v___x_2876_ = v___x_2867_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2880_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_snd_2865_);
                    v___x_2876_ = v_reuseFailAlloc_2880_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2872_ == 0 {
                    leanh::lean_ctor_set(v___x_2871_, 0, v___x_2876_);
                    v___x_2878_ = v___x_2871_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2879_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
                    v___x_2878_ = v_reuseFailAlloc_2879_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2878_;
            }
            5 => {
                if v_isShared_2886_ == 0 {
                    v___x_2888_ = v___x_2885_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2889_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
                    v___x_2888_ = v_reuseFailAlloc_2889_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5_spec__7___boxed(
    mut v_type_2892_: *mut leanh::LeanObject,
    mut v_u_2893_: *mut leanh::LeanObject,
    mut v_instDeclName_2894_: *mut leanh::LeanObject,
    mut v_declName_2895_: *mut leanh::LeanObject,
    mut v_expectedInst_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___y_2898_: *mut leanh::LeanObject,
    mut v___y_2899_: *mut leanh::LeanObject,
    mut v___y_2900_: *mut leanh::LeanObject,
    mut v___y_2901_: *mut leanh::LeanObject,
    mut v___y_2902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2903_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5_spec__7(v_type_2892_, v_u_2893_, v_instDeclName_2894_, v_declName_2895_, v_expectedInst_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
    leanh::lean_dec(v___y_2901_);
    leanh::lean_dec_ref(v___y_2900_);
    leanh::lean_dec(v___y_2899_);
    leanh::lean_dec_ref(v___y_2898_);
    return v_res_2903_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5(
    mut v___y_2920_: *mut leanh::LeanObject,
    mut v___y_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
    mut v___y_2923_: *mut leanh::LeanObject,
    mut v___y_2924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2936_: u8 = 0;
    let mut v_type_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2954_: u8 = 0;
    let mut v_snd_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRing_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2960_: u8 = 0;
    let mut v_invFn_x3f_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2974_: u8 = 0;
    let mut v_invSet_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2978_: u8 = 0;
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2981_: u8 = 0;
    let mut v_id_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3000_: u8 = 0;
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_unused_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3016_: u8 = 0;
    let mut v_unused_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut v_unused_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2926_ = leanh::lean_ctor_get(v___y_2920_, 0);
                v_mulFn_x3f_2927_ = leanh::lean_ctor_get(v_toRing_2926_, 7);
                leanh::lean_inc(v_mulFn_x3f_2927_);
                if leanh::lean_obj_tag(v_mulFn_x3f_2927_) == 1 {
                    v_val_2928_ = leanh::lean_ctor_get(v_mulFn_x3f_2927_, 0);
                    v_isSharedCheck_2936_ =
                        (!leanh::lean_is_exclusive(v_mulFn_x3f_2927_)) as u8;
                    if v_isSharedCheck_2936_ == 0 {
                        v___x_2930_ = v_mulFn_x3f_2927_;
                        v_isShared_2931_ = v_isSharedCheck_2936_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2928_);
                        leanh::lean_dec(v_mulFn_x3f_2927_);
                        v___x_2930_ = leanh::lean_box(0);
                        v_isShared_2931_ = v_isSharedCheck_2936_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_mulFn_x3f_2927_);
                    v_type_2937_ = leanh::lean_ctor_get(v_toRing_2926_, 1);
                    leanh::lean_inc_ref_n(v_type_2937_, 3);
                    v_u_2938_ = leanh::lean_ctor_get(v_toRing_2926_, 2);
                    leanh::lean_inc_n(v_u_2938_, 2);
                    v_semiringInst_2939_ = leanh::lean_ctor_get(v_toRing_2926_, 4);
                    v___x_2940_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__1;
                    v___x_2941_ = leanh::lean_box(0);
                    v___x_2942_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2942_, 0, v_u_2938_);
                    leanh::lean_ctor_set(v___x_2942_, 1, v___x_2941_);
                    leanh::lean_inc_ref(v___x_2942_);
                    v___x_2943_ = l_Lean_mkConst(v___x_2940_, v___x_2942_);
                    v___x_2944_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__3;
                    v___x_2945_ = l_Lean_mkConst(v___x_2944_, v___x_2942_);
                    leanh::lean_inc_ref(v_semiringInst_2939_);
                    v___x_2946_ = l_Lean_mkAppB(v___x_2945_, v_type_2937_, v_semiringInst_2939_);
                    v_expectedInst_2947_ = l_Lean_mkAppB(v___x_2943_, v_type_2937_, v___x_2946_);
                    v___x_2948_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__5;
                    v___x_2949_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___closed__7;
                    v___x_2950_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5_spec__7(v_type_2937_, v_u_2938_, v___x_2948_, v___x_2949_, v_expectedInst_2947_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
                    if leanh::lean_obj_tag(v___x_2950_) == 0 {
                        v_a_2951_ = leanh::lean_ctor_get(v___x_2950_, 0);
                        v_isSharedCheck_3020_ =
                            (!leanh::lean_is_exclusive(v___x_2950_)) as u8;
                        if v_isSharedCheck_3020_ == 0 {
                            v___x_2953_ = v___x_2950_;
                            v_isShared_2954_ = v_isSharedCheck_3020_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2951_);
                            leanh::lean_dec(v___x_2950_);
                            v___x_2953_ = leanh::lean_box(0);
                            v_isShared_2954_ = v_isSharedCheck_3020_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_2950_;
                    }
                }
            }
            1 => {
                v___x_2932_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2932_, 0, v_val_2928_);
                leanh::lean_ctor_set(v___x_2932_, 1, v___y_2920_);
                if v_isShared_2931_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2930_, 0);
                    leanh::lean_ctor_set(v___x_2930_, 0, v___x_2932_);
                    v___x_2934_ = v___x_2930_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2935_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
                    v___x_2934_ = v_reuseFailAlloc_2935_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2934_;
            }
            3 => {
                v_snd_2955_ = leanh::lean_ctor_get(v_a_2951_, 1);
                leanh::lean_inc(v_snd_2955_);
                v_toRing_2956_ = leanh::lean_ctor_get(v_snd_2955_, 0);
                leanh::lean_inc_ref(v_toRing_2956_);
                v_fst_2957_ = leanh::lean_ctor_get(v_a_2951_, 0);
                v_isSharedCheck_3018_ = (!leanh::lean_is_exclusive(v_a_2951_)) as u8;
                if v_isSharedCheck_3018_ == 0 {
                    v_unused_3019_ = leanh::lean_ctor_get(v_a_2951_, 1);
                    leanh::lean_dec(v_unused_3019_);
                    v___x_2959_ = v_a_2951_;
                    v_isShared_2960_ = v_isSharedCheck_3018_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_2957_);
                    leanh::lean_dec(v_a_2951_);
                    v___x_2959_ = leanh::lean_box(0);
                    v_isShared_2960_ = v_isSharedCheck_3018_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_invFn_x3f_2961_ = leanh::lean_ctor_get(v_snd_2955_, 1);
                v_semiringId_x3f_2962_ = leanh::lean_ctor_get(v_snd_2955_, 2);
                v_commSemiringInst_2963_ = leanh::lean_ctor_get(v_snd_2955_, 3);
                v_commRingInst_2964_ = leanh::lean_ctor_get(v_snd_2955_, 4);
                v_noZeroDivInst_x3f_2965_ = leanh::lean_ctor_get(v_snd_2955_, 5);
                v_fieldInst_x3f_2966_ = leanh::lean_ctor_get(v_snd_2955_, 6);
                v_powIdentityInst_x3f_2967_ = leanh::lean_ctor_get(v_snd_2955_, 7);
                v_denoteEntries_2968_ = leanh::lean_ctor_get(v_snd_2955_, 8);
                v_nextId_2969_ = leanh::lean_ctor_get(v_snd_2955_, 9);
                v_steps_2970_ = leanh::lean_ctor_get(v_snd_2955_, 10);
                v_queue_2971_ = leanh::lean_ctor_get(v_snd_2955_, 11);
                v_basis_2972_ = leanh::lean_ctor_get(v_snd_2955_, 12);
                v_diseqs_2973_ = leanh::lean_ctor_get(v_snd_2955_, 13);
                v_recheck_2974_ = leanh::lean_ctor_get_uint8(
                    v_snd_2955_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2975_ = leanh::lean_ctor_get(v_snd_2955_, 14);
                v_powIdentityVarCount_2976_ = leanh::lean_ctor_get(v_snd_2955_, 15);
                v_numEq0_x3f_2977_ = leanh::lean_ctor_get(v_snd_2955_, 16);
                v_numEq0Updated_2978_ = leanh::lean_ctor_get_uint8(
                    v_snd_2955_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_3016_ = (!leanh::lean_is_exclusive(v_snd_2955_)) as u8;
                if v_isSharedCheck_3016_ == 0 {
                    v_unused_3017_ = leanh::lean_ctor_get(v_snd_2955_, 0);
                    leanh::lean_dec(v_unused_3017_);
                    v___x_2980_ = v_snd_2955_;
                    v_isShared_2981_ = v_isSharedCheck_3016_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_2977_);
                    leanh::lean_inc(v_powIdentityVarCount_2976_);
                    leanh::lean_inc(v_invSet_2975_);
                    leanh::lean_inc(v_diseqs_2973_);
                    leanh::lean_inc(v_basis_2972_);
                    leanh::lean_inc(v_queue_2971_);
                    leanh::lean_inc(v_steps_2970_);
                    leanh::lean_inc(v_nextId_2969_);
                    leanh::lean_inc(v_denoteEntries_2968_);
                    leanh::lean_inc(v_powIdentityInst_x3f_2967_);
                    leanh::lean_inc(v_fieldInst_x3f_2966_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_2965_);
                    leanh::lean_inc(v_commRingInst_2964_);
                    leanh::lean_inc(v_commSemiringInst_2963_);
                    leanh::lean_inc(v_semiringId_x3f_2962_);
                    leanh::lean_inc(v_invFn_x3f_2961_);
                    leanh::lean_dec(v_snd_2955_);
                    v___x_2980_ = leanh::lean_box(0);
                    v_isShared_2981_ = v_isSharedCheck_3016_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_id_2982_ = leanh::lean_ctor_get(v_toRing_2956_, 0);
                v_type_2983_ = leanh::lean_ctor_get(v_toRing_2956_, 1);
                v_u_2984_ = leanh::lean_ctor_get(v_toRing_2956_, 2);
                v_ringInst_2985_ = leanh::lean_ctor_get(v_toRing_2956_, 3);
                v_semiringInst_2986_ = leanh::lean_ctor_get(v_toRing_2956_, 4);
                v_charInst_x3f_2987_ = leanh::lean_ctor_get(v_toRing_2956_, 5);
                v_addFn_x3f_2988_ = leanh::lean_ctor_get(v_toRing_2956_, 6);
                v_subFn_x3f_2989_ = leanh::lean_ctor_get(v_toRing_2956_, 8);
                v_negFn_x3f_2990_ = leanh::lean_ctor_get(v_toRing_2956_, 9);
                v_powFn_x3f_2991_ = leanh::lean_ctor_get(v_toRing_2956_, 10);
                v_intCastFn_x3f_2992_ = leanh::lean_ctor_get(v_toRing_2956_, 11);
                v_natCastFn_x3f_2993_ = leanh::lean_ctor_get(v_toRing_2956_, 12);
                v_one_x3f_2994_ = leanh::lean_ctor_get(v_toRing_2956_, 13);
                v_vars_2995_ = leanh::lean_ctor_get(v_toRing_2956_, 14);
                v_varMap_2996_ = leanh::lean_ctor_get(v_toRing_2956_, 15);
                v_denote_2997_ = leanh::lean_ctor_get(v_toRing_2956_, 16);
                v_isSharedCheck_3014_ = (!leanh::lean_is_exclusive(v_toRing_2956_)) as u8;
                if v_isSharedCheck_3014_ == 0 {
                    v_unused_3015_ = leanh::lean_ctor_get(v_toRing_2956_, 7);
                    leanh::lean_dec(v_unused_3015_);
                    v___x_2999_ = v_toRing_2956_;
                    v_isShared_3000_ = v_isSharedCheck_3014_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_2997_);
                    leanh::lean_inc(v_varMap_2996_);
                    leanh::lean_inc(v_vars_2995_);
                    leanh::lean_inc(v_one_x3f_2994_);
                    leanh::lean_inc(v_natCastFn_x3f_2993_);
                    leanh::lean_inc(v_intCastFn_x3f_2992_);
                    leanh::lean_inc(v_powFn_x3f_2991_);
                    leanh::lean_inc(v_negFn_x3f_2990_);
                    leanh::lean_inc(v_subFn_x3f_2989_);
                    leanh::lean_inc(v_addFn_x3f_2988_);
                    leanh::lean_inc(v_charInst_x3f_2987_);
                    leanh::lean_inc(v_semiringInst_2986_);
                    leanh::lean_inc(v_ringInst_2985_);
                    leanh::lean_inc(v_u_2984_);
                    leanh::lean_inc(v_type_2983_);
                    leanh::lean_inc(v_id_2982_);
                    leanh::lean_dec(v_toRing_2956_);
                    v___x_2999_ = leanh::lean_box(0);
                    v_isShared_3000_ = v_isSharedCheck_3014_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc(v_fst_2957_);
                v___x_3001_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3001_, 0, v_fst_2957_);
                if v_isShared_3000_ == 0 {
                    leanh::lean_ctor_set(v___x_2999_, 7, v___x_3001_);
                    v___x_3003_ = v___x_2999_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3013_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_id_2982_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_type_2983_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_u_2984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_ringInst_2985_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_semiringInst_2986_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 5, v_charInst_x3f_2987_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 6, v_addFn_x3f_2988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 7, v___x_3001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 8, v_subFn_x3f_2989_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 9, v_negFn_x3f_2990_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 10, v_powFn_x3f_2991_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 11, v_intCastFn_x3f_2992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 12, v_natCastFn_x3f_2993_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 13, v_one_x3f_2994_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 14, v_vars_2995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 15, v_varMap_2996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 16, v_denote_2997_);
                    v___x_3003_ = v_reuseFailAlloc_3013_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2981_ == 0 {
                    leanh::lean_ctor_set(v___x_2980_, 0, v___x_3003_);
                    v___x_3005_ = v___x_2980_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_invFn_x3f_2961_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_semiringId_x3f_2962_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3012_,
                        3,
                        v_commSemiringInst_2963_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 4, v_commRingInst_2964_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3012_,
                        5,
                        v_noZeroDivInst_x3f_2965_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 6, v_fieldInst_x3f_2966_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3012_,
                        7,
                        v_powIdentityInst_x3f_2967_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 8, v_denoteEntries_2968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 9, v_nextId_2969_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 10, v_steps_2970_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 11, v_queue_2971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 12, v_basis_2972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 13, v_diseqs_2973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 14, v_invSet_2975_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3012_,
                        15,
                        v_powIdentityVarCount_2976_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 16, v_numEq0_x3f_2977_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3012_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_2974_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3012_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_2978_,
                    );
                    v___x_3005_ = v_reuseFailAlloc_3012_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2960_ == 0 {
                    leanh::lean_ctor_set(v___x_2959_, 1, v___x_3005_);
                    v___x_3007_ = v___x_2959_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3011_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_fst_2957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_3005_);
                    v___x_3007_ = v_reuseFailAlloc_3011_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2954_ == 0 {
                    leanh::lean_ctor_set(v___x_2953_, 0, v___x_3007_);
                    v___x_3009_ = v___x_2953_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3010_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
                    v___x_3009_ = v_reuseFailAlloc_3010_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5___boxed(
    mut v___y_3021_: *mut leanh::LeanObject,
    mut v___y_3022_: *mut leanh::LeanObject,
    mut v___y_3023_: *mut leanh::LeanObject,
    mut v___y_3024_: *mut leanh::LeanObject,
    mut v___y_3025_: *mut leanh::LeanObject,
    mut v___y_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3027_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5(v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
    leanh::lean_dec(v___y_3025_);
    leanh::lean_dec_ref(v___y_3024_);
    leanh::lean_dec(v___y_3023_);
    leanh::lean_dec_ref(v___y_3022_);
    return v_res_3027_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3031_ = leanh::lean_unsigned_to_nat(0);
    v___x_3032_ = l_Lean_Level_ofNat(v___x_3031_);
    return v___x_3032_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15(
    mut v_u_3043_: *mut leanh::LeanObject,
    mut v_type_3044_: *mut leanh::LeanObject,
    mut v_semiringInst_3045_: *mut leanh::LeanObject,
    mut v___y_3046_: *mut leanh::LeanObject,
    mut v___y_3047_: *mut leanh::LeanObject,
    mut v___y_3048_: *mut leanh::LeanObject,
    mut v___y_3049_: *mut leanh::LeanObject,
    mut v___y_3050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3067_: u8 = 0;
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3075_: u8 = 0;
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3084_: u8 = 0;
    let mut v_unused_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3089_: u8 = 0;
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3093_: u8 = 0;
    let mut v_isSharedCheck_3094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3052_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__1;
                v___x_3053_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__2_once), _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__2);
                v___x_3054_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_3043_);
                v___x_3055_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3055_, 0, v_u_3043_);
                leanh::lean_ctor_set(v___x_3055_, 1, v___x_3054_);
                leanh::lean_inc_ref(v___x_3055_);
                v___x_3056_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3056_, 0, v___x_3053_);
                leanh::lean_ctor_set(v___x_3056_, 1, v___x_3055_);
                v___x_3057_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3057_, 0, v_u_3043_);
                leanh::lean_ctor_set(v___x_3057_, 1, v___x_3056_);
                leanh::lean_inc_ref(v___x_3057_);
                v___x_3058_ = l_Lean_mkConst(v___x_3052_, v___x_3057_);
                v___x_3059_ = l_Lean_Nat_mkType;
                leanh::lean_inc_ref_n(v_type_3044_, 2);
                v___x_3060_ = l_Lean_mkApp3(v___x_3058_, v_type_3044_, v___x_3059_, v_type_3044_);
                v___x_3061_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15(v___x_3060_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
                if leanh::lean_obj_tag(v___x_3061_) == 0 {
                    v_a_3062_ = leanh::lean_ctor_get(v___x_3061_, 0);
                    leanh::lean_inc(v_a_3062_);
                    leanh::lean_dec_ref_known(v___x_3061_, 1);
                    v_fst_3063_ = leanh::lean_ctor_get(v_a_3062_, 0);
                    v_snd_3064_ = leanh::lean_ctor_get(v_a_3062_, 1);
                    v_isSharedCheck_3094_ = (!leanh::lean_is_exclusive(v_a_3062_)) as u8;
                    if v_isSharedCheck_3094_ == 0 {
                        v___x_3066_ = v_a_3062_;
                        v_isShared_3067_ = v_isSharedCheck_3094_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3064_);
                        leanh::lean_inc(v_fst_3063_);
                        leanh::lean_dec(v_a_3062_);
                        v___x_3066_ = leanh::lean_box(0);
                        v_isShared_3067_ = v_isSharedCheck_3094_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_3057_, 2);
                    leanh::lean_dec_ref_known(v___x_3055_, 2);
                    leanh::lean_dec_ref(v_semiringInst_3045_);
                    leanh::lean_dec_ref(v_type_3044_);
                    return v___x_3061_;
                }
            }
            1 => {
                v___x_3068_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__4;
                v___x_3069_ = l_Lean_mkConst(v___x_3068_, v___x_3055_);
                leanh::lean_inc_ref(v_type_3044_);
                v_inst_x27_3070_ = l_Lean_mkAppB(v___x_3069_, v_type_3044_, v_semiringInst_3045_);
                v___x_3071_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___closed__6;
                leanh::lean_inc(v_fst_3063_);
                v___x_3072_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                    v___x_3071_,
                    v_fst_3063_,
                    v_inst_x27_3070_,
                    v___y_3047_,
                    v___y_3048_,
                    v___y_3049_,
                    v___y_3050_,
                );
                if leanh::lean_obj_tag(v___x_3072_) == 0 {
                    v_isSharedCheck_3084_ = (!leanh::lean_is_exclusive(v___x_3072_)) as u8;
                    if v_isSharedCheck_3084_ == 0 {
                        v_unused_3085_ = leanh::lean_ctor_get(v___x_3072_, 0);
                        leanh::lean_dec(v_unused_3085_);
                        v___x_3074_ = v___x_3072_;
                        v_isShared_3075_ = v_isSharedCheck_3084_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3072_);
                        v___x_3074_ = leanh::lean_box(0);
                        v_isShared_3075_ = v_isSharedCheck_3084_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3066_);
                    leanh::lean_dec(v_snd_3064_);
                    leanh::lean_dec(v_fst_3063_);
                    leanh::lean_dec_ref_known(v___x_3057_, 2);
                    leanh::lean_dec_ref(v_type_3044_);
                    v_a_3086_ = leanh::lean_ctor_get(v___x_3072_, 0);
                    v_isSharedCheck_3093_ = (!leanh::lean_is_exclusive(v___x_3072_)) as u8;
                    if v_isSharedCheck_3093_ == 0 {
                        v___x_3088_ = v___x_3072_;
                        v_isShared_3089_ = v_isSharedCheck_3093_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3086_);
                        leanh::lean_dec(v___x_3072_);
                        v___x_3088_ = leanh::lean_box(0);
                        v_isShared_3089_ = v_isSharedCheck_3093_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3076_ = l_Lean_mkConst(v___x_3071_, v___x_3057_);
                leanh::lean_inc_ref(v_type_3044_);
                v___x_3077_ = l_Lean_mkApp4(
                    v___x_3076_,
                    v_type_3044_,
                    v___x_3059_,
                    v_type_3044_,
                    v_fst_3063_,
                );
                if v_isShared_3067_ == 0 {
                    leanh::lean_ctor_set(v___x_3066_, 0, v___x_3077_);
                    v___x_3079_ = v___x_3066_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3083_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_snd_3064_);
                    v___x_3079_ = v_reuseFailAlloc_3083_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3075_ == 0 {
                    leanh::lean_ctor_set(v___x_3074_, 0, v___x_3079_);
                    v___x_3081_ = v___x_3074_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3079_);
                    v___x_3081_ = v_reuseFailAlloc_3082_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3081_;
            }
            5 => {
                if v_isShared_3089_ == 0 {
                    v___x_3091_ = v___x_3088_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3092_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
                    v___x_3091_ = v_reuseFailAlloc_3092_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3091_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15___boxed(
    mut v_u_3095_: *mut leanh::LeanObject,
    mut v_type_3096_: *mut leanh::LeanObject,
    mut v_semiringInst_3097_: *mut leanh::LeanObject,
    mut v___y_3098_: *mut leanh::LeanObject,
    mut v___y_3099_: *mut leanh::LeanObject,
    mut v___y_3100_: *mut leanh::LeanObject,
    mut v___y_3101_: *mut leanh::LeanObject,
    mut v___y_3102_: *mut leanh::LeanObject,
    mut v___y_3103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3104_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15(v_u_3095_, v_type_3096_, v_semiringInst_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
    leanh::lean_dec(v___y_3102_);
    leanh::lean_dec_ref(v___y_3101_);
    leanh::lean_dec(v___y_3100_);
    leanh::lean_dec_ref(v___y_3099_);
    return v_res_3104_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12(
    mut v___y_3105_: *mut leanh::LeanObject,
    mut v___y_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
    mut v___y_3108_: *mut leanh::LeanObject,
    mut v___y_3109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3121_: u8 = 0;
    let mut v_type_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v_snd_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRing_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3135_: u8 = 0;
    let mut v_invFn_x3f_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_3149_: u8 = 0;
    let mut v_invSet_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_3153_: u8 = 0;
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v_id_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3175_: u8 = 0;
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3189_: u8 = 0;
    let mut v_unused_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut v_unused_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v_unused_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_3111_ = leanh::lean_ctor_get(v___y_3105_, 0);
                v_powFn_x3f_3112_ = leanh::lean_ctor_get(v_toRing_3111_, 10);
                leanh::lean_inc(v_powFn_x3f_3112_);
                if leanh::lean_obj_tag(v_powFn_x3f_3112_) == 1 {
                    v_val_3113_ = leanh::lean_ctor_get(v_powFn_x3f_3112_, 0);
                    v_isSharedCheck_3121_ =
                        (!leanh::lean_is_exclusive(v_powFn_x3f_3112_)) as u8;
                    if v_isSharedCheck_3121_ == 0 {
                        v___x_3115_ = v_powFn_x3f_3112_;
                        v_isShared_3116_ = v_isSharedCheck_3121_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3113_);
                        leanh::lean_dec(v_powFn_x3f_3112_);
                        v___x_3115_ = leanh::lean_box(0);
                        v_isShared_3116_ = v_isSharedCheck_3121_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_powFn_x3f_3112_);
                    v_type_3122_ = leanh::lean_ctor_get(v_toRing_3111_, 1);
                    leanh::lean_inc_ref(v_type_3122_);
                    v_u_3123_ = leanh::lean_ctor_get(v_toRing_3111_, 2);
                    leanh::lean_inc(v_u_3123_);
                    v_semiringInst_3124_ = leanh::lean_ctor_get(v_toRing_3111_, 4);
                    leanh::lean_inc_ref(v_semiringInst_3124_);
                    v___x_3125_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12_spec__15(v_u_3123_, v_type_3122_, v_semiringInst_3124_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
                    if leanh::lean_obj_tag(v___x_3125_) == 0 {
                        v_a_3126_ = leanh::lean_ctor_get(v___x_3125_, 0);
                        v_isSharedCheck_3195_ =
                            (!leanh::lean_is_exclusive(v___x_3125_)) as u8;
                        if v_isSharedCheck_3195_ == 0 {
                            v___x_3128_ = v___x_3125_;
                            v_isShared_3129_ = v_isSharedCheck_3195_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3126_);
                            leanh::lean_dec(v___x_3125_);
                            v___x_3128_ = leanh::lean_box(0);
                            v_isShared_3129_ = v_isSharedCheck_3195_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_3125_;
                    }
                }
            }
            1 => {
                v___x_3117_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3117_, 0, v_val_3113_);
                leanh::lean_ctor_set(v___x_3117_, 1, v___y_3105_);
                if v_isShared_3116_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3115_, 0);
                    leanh::lean_ctor_set(v___x_3115_, 0, v___x_3117_);
                    v___x_3119_ = v___x_3115_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3120_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3117_);
                    v___x_3119_ = v_reuseFailAlloc_3120_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3119_;
            }
            3 => {
                v_snd_3130_ = leanh::lean_ctor_get(v_a_3126_, 1);
                leanh::lean_inc(v_snd_3130_);
                v_toRing_3131_ = leanh::lean_ctor_get(v_snd_3130_, 0);
                leanh::lean_inc_ref(v_toRing_3131_);
                v_fst_3132_ = leanh::lean_ctor_get(v_a_3126_, 0);
                v_isSharedCheck_3193_ = (!leanh::lean_is_exclusive(v_a_3126_)) as u8;
                if v_isSharedCheck_3193_ == 0 {
                    v_unused_3194_ = leanh::lean_ctor_get(v_a_3126_, 1);
                    leanh::lean_dec(v_unused_3194_);
                    v___x_3134_ = v_a_3126_;
                    v_isShared_3135_ = v_isSharedCheck_3193_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_3132_);
                    leanh::lean_dec(v_a_3126_);
                    v___x_3134_ = leanh::lean_box(0);
                    v_isShared_3135_ = v_isSharedCheck_3193_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_invFn_x3f_3136_ = leanh::lean_ctor_get(v_snd_3130_, 1);
                v_semiringId_x3f_3137_ = leanh::lean_ctor_get(v_snd_3130_, 2);
                v_commSemiringInst_3138_ = leanh::lean_ctor_get(v_snd_3130_, 3);
                v_commRingInst_3139_ = leanh::lean_ctor_get(v_snd_3130_, 4);
                v_noZeroDivInst_x3f_3140_ = leanh::lean_ctor_get(v_snd_3130_, 5);
                v_fieldInst_x3f_3141_ = leanh::lean_ctor_get(v_snd_3130_, 6);
                v_powIdentityInst_x3f_3142_ = leanh::lean_ctor_get(v_snd_3130_, 7);
                v_denoteEntries_3143_ = leanh::lean_ctor_get(v_snd_3130_, 8);
                v_nextId_3144_ = leanh::lean_ctor_get(v_snd_3130_, 9);
                v_steps_3145_ = leanh::lean_ctor_get(v_snd_3130_, 10);
                v_queue_3146_ = leanh::lean_ctor_get(v_snd_3130_, 11);
                v_basis_3147_ = leanh::lean_ctor_get(v_snd_3130_, 12);
                v_diseqs_3148_ = leanh::lean_ctor_get(v_snd_3130_, 13);
                v_recheck_3149_ = leanh::lean_ctor_get_uint8(
                    v_snd_3130_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_3150_ = leanh::lean_ctor_get(v_snd_3130_, 14);
                v_powIdentityVarCount_3151_ = leanh::lean_ctor_get(v_snd_3130_, 15);
                v_numEq0_x3f_3152_ = leanh::lean_ctor_get(v_snd_3130_, 16);
                v_numEq0Updated_3153_ = leanh::lean_ctor_get_uint8(
                    v_snd_3130_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_3191_ = (!leanh::lean_is_exclusive(v_snd_3130_)) as u8;
                if v_isSharedCheck_3191_ == 0 {
                    v_unused_3192_ = leanh::lean_ctor_get(v_snd_3130_, 0);
                    leanh::lean_dec(v_unused_3192_);
                    v___x_3155_ = v_snd_3130_;
                    v_isShared_3156_ = v_isSharedCheck_3191_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_3152_);
                    leanh::lean_inc(v_powIdentityVarCount_3151_);
                    leanh::lean_inc(v_invSet_3150_);
                    leanh::lean_inc(v_diseqs_3148_);
                    leanh::lean_inc(v_basis_3147_);
                    leanh::lean_inc(v_queue_3146_);
                    leanh::lean_inc(v_steps_3145_);
                    leanh::lean_inc(v_nextId_3144_);
                    leanh::lean_inc(v_denoteEntries_3143_);
                    leanh::lean_inc(v_powIdentityInst_x3f_3142_);
                    leanh::lean_inc(v_fieldInst_x3f_3141_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_3140_);
                    leanh::lean_inc(v_commRingInst_3139_);
                    leanh::lean_inc(v_commSemiringInst_3138_);
                    leanh::lean_inc(v_semiringId_x3f_3137_);
                    leanh::lean_inc(v_invFn_x3f_3136_);
                    leanh::lean_dec(v_snd_3130_);
                    v___x_3155_ = leanh::lean_box(0);
                    v_isShared_3156_ = v_isSharedCheck_3191_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_id_3157_ = leanh::lean_ctor_get(v_toRing_3131_, 0);
                v_type_3158_ = leanh::lean_ctor_get(v_toRing_3131_, 1);
                v_u_3159_ = leanh::lean_ctor_get(v_toRing_3131_, 2);
                v_ringInst_3160_ = leanh::lean_ctor_get(v_toRing_3131_, 3);
                v_semiringInst_3161_ = leanh::lean_ctor_get(v_toRing_3131_, 4);
                v_charInst_x3f_3162_ = leanh::lean_ctor_get(v_toRing_3131_, 5);
                v_addFn_x3f_3163_ = leanh::lean_ctor_get(v_toRing_3131_, 6);
                v_mulFn_x3f_3164_ = leanh::lean_ctor_get(v_toRing_3131_, 7);
                v_subFn_x3f_3165_ = leanh::lean_ctor_get(v_toRing_3131_, 8);
                v_negFn_x3f_3166_ = leanh::lean_ctor_get(v_toRing_3131_, 9);
                v_intCastFn_x3f_3167_ = leanh::lean_ctor_get(v_toRing_3131_, 11);
                v_natCastFn_x3f_3168_ = leanh::lean_ctor_get(v_toRing_3131_, 12);
                v_one_x3f_3169_ = leanh::lean_ctor_get(v_toRing_3131_, 13);
                v_vars_3170_ = leanh::lean_ctor_get(v_toRing_3131_, 14);
                v_varMap_3171_ = leanh::lean_ctor_get(v_toRing_3131_, 15);
                v_denote_3172_ = leanh::lean_ctor_get(v_toRing_3131_, 16);
                v_isSharedCheck_3189_ = (!leanh::lean_is_exclusive(v_toRing_3131_)) as u8;
                if v_isSharedCheck_3189_ == 0 {
                    v_unused_3190_ = leanh::lean_ctor_get(v_toRing_3131_, 10);
                    leanh::lean_dec(v_unused_3190_);
                    v___x_3174_ = v_toRing_3131_;
                    v_isShared_3175_ = v_isSharedCheck_3189_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_3172_);
                    leanh::lean_inc(v_varMap_3171_);
                    leanh::lean_inc(v_vars_3170_);
                    leanh::lean_inc(v_one_x3f_3169_);
                    leanh::lean_inc(v_natCastFn_x3f_3168_);
                    leanh::lean_inc(v_intCastFn_x3f_3167_);
                    leanh::lean_inc(v_negFn_x3f_3166_);
                    leanh::lean_inc(v_subFn_x3f_3165_);
                    leanh::lean_inc(v_mulFn_x3f_3164_);
                    leanh::lean_inc(v_addFn_x3f_3163_);
                    leanh::lean_inc(v_charInst_x3f_3162_);
                    leanh::lean_inc(v_semiringInst_3161_);
                    leanh::lean_inc(v_ringInst_3160_);
                    leanh::lean_inc(v_u_3159_);
                    leanh::lean_inc(v_type_3158_);
                    leanh::lean_inc(v_id_3157_);
                    leanh::lean_dec(v_toRing_3131_);
                    v___x_3174_ = leanh::lean_box(0);
                    v_isShared_3175_ = v_isSharedCheck_3189_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc(v_fst_3132_);
                v___x_3176_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3176_, 0, v_fst_3132_);
                if v_isShared_3175_ == 0 {
                    leanh::lean_ctor_set(v___x_3174_, 10, v___x_3176_);
                    v___x_3178_ = v___x_3174_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3188_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_id_3157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_type_3158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_u_3159_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_ringInst_3160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 4, v_semiringInst_3161_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 5, v_charInst_x3f_3162_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 6, v_addFn_x3f_3163_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 7, v_mulFn_x3f_3164_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 8, v_subFn_x3f_3165_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 9, v_negFn_x3f_3166_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 10, v___x_3176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 11, v_intCastFn_x3f_3167_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 12, v_natCastFn_x3f_3168_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 13, v_one_x3f_3169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 14, v_vars_3170_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 15, v_varMap_3171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 16, v_denote_3172_);
                    v___x_3178_ = v_reuseFailAlloc_3188_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3156_ == 0 {
                    leanh::lean_ctor_set(v___x_3155_, 0, v___x_3178_);
                    v___x_3180_ = v___x_3155_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3187_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3178_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_invFn_x3f_3136_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 2, v_semiringId_x3f_3137_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3187_,
                        3,
                        v_commSemiringInst_3138_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 4, v_commRingInst_3139_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3187_,
                        5,
                        v_noZeroDivInst_x3f_3140_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 6, v_fieldInst_x3f_3141_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3187_,
                        7,
                        v_powIdentityInst_x3f_3142_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 8, v_denoteEntries_3143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 9, v_nextId_3144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 10, v_steps_3145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 11, v_queue_3146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 12, v_basis_3147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 13, v_diseqs_3148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 14, v_invSet_3150_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3187_,
                        15,
                        v_powIdentityVarCount_3151_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3187_, 16, v_numEq0_x3f_3152_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3187_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_3149_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3187_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_3153_,
                    );
                    v___x_3180_ = v_reuseFailAlloc_3187_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3135_ == 0 {
                    leanh::lean_ctor_set(v___x_3134_, 1, v___x_3180_);
                    v___x_3182_ = v___x_3134_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3186_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_fst_3132_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___x_3180_);
                    v___x_3182_ = v_reuseFailAlloc_3186_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3129_ == 0 {
                    leanh::lean_ctor_set(v___x_3128_, 0, v___x_3182_);
                    v___x_3184_ = v___x_3128_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3185_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3182_);
                    v___x_3184_ = v_reuseFailAlloc_3185_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12___boxed(
    mut v___y_3196_: *mut leanh::LeanObject,
    mut v___y_3197_: *mut leanh::LeanObject,
    mut v___y_3198_: *mut leanh::LeanObject,
    mut v___y_3199_: *mut leanh::LeanObject,
    mut v___y_3200_: *mut leanh::LeanObject,
    mut v___y_3201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3202_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12(v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
    leanh::lean_dec(v___y_3200_);
    leanh::lean_dec_ref(v___y_3199_);
    leanh::lean_dec(v___y_3198_);
    leanh::lean_dec_ref(v___y_3197_);
    return v_res_3202_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9(
    mut v_pw_3203_: *mut leanh::LeanObject,
    mut v___y_3204_: *mut leanh::LeanObject,
    mut v___y_3205_: *mut leanh::LeanObject,
    mut v___y_3206_: *mut leanh::LeanObject,
    mut v___y_3207_: *mut leanh::LeanObject,
    mut v___y_3208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___y_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v_fst_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_3210_ = leanh::lean_ctor_get(v___y_3204_, 0);
                v_vars_3211_ = leanh::lean_ctor_get(v_toRing_3210_, 14);
                v_x_3212_ = leanh::lean_ctor_get(v_pw_3203_, 0);
                v_k_3213_ = leanh::lean_ctor_get(v_pw_3203_, 1);
                v_isSharedCheck_3250_ = (!leanh::lean_is_exclusive(v_pw_3203_)) as u8;
                if v_isSharedCheck_3250_ == 0 {
                    v___x_3215_ = v_pw_3203_;
                    v_isShared_3216_ = v_isSharedCheck_3250_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_k_3213_);
                    leanh::lean_inc(v_x_3212_);
                    leanh::lean_dec(v_pw_3203_);
                    v___x_3215_ = leanh::lean_box(0);
                    v_isShared_3216_ = v_isSharedCheck_3250_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_size_3245_ = leanh::lean_ctor_get(v_vars_3211_, 2);
                v___x_3246_ = l_Lean_instInhabitedExpr;
                v___x_3247_ = lean_nat_dec_lt(v_x_3212_, v_size_3245_);
                if v___x_3247_ == 0 {
                    leanh::lean_dec(v_x_3212_);
                    v___x_3248_ = l_outOfBounds___redArg(v___x_3246_);
                    v___y_3218_ = v___x_3248_;
                    state = 2;
                    continue;
                } else {
                    v___x_3249_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_3246_,
                        v_vars_3211_,
                        v_x_3212_,
                    );
                    leanh::lean_dec(v_x_3212_);
                    v___y_3218_ = v___x_3249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3219_ = leanh::lean_unsigned_to_nat(1);
                v___x_3220_ = lean_nat_dec_eq(v_k_3213_, v___x_3219_);
                if v___x_3220_ == 0 {
                    leanh::lean_del_object(v___x_3215_);
                    v___x_3221_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9_spec__12(v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
                    if leanh::lean_obj_tag(v___x_3221_) == 0 {
                        v_a_3222_ = leanh::lean_ctor_get(v___x_3221_, 0);
                        v_isSharedCheck_3240_ =
                            (!leanh::lean_is_exclusive(v___x_3221_)) as u8;
                        if v_isSharedCheck_3240_ == 0 {
                            v___x_3224_ = v___x_3221_;
                            v_isShared_3225_ = v_isSharedCheck_3240_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3222_);
                            leanh::lean_dec(v___x_3221_);
                            v___x_3224_ = leanh::lean_box(0);
                            v_isShared_3225_ = v_isSharedCheck_3240_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_3218_);
                        leanh::lean_dec(v_k_3213_);
                        return v___x_3221_;
                    }
                } else {
                    leanh::lean_dec(v_k_3213_);
                    if v_isShared_3216_ == 0 {
                        leanh::lean_ctor_set(v___x_3215_, 1, v___y_3204_);
                        leanh::lean_ctor_set(v___x_3215_, 0, v___y_3218_);
                        v___x_3242_ = v___x_3215_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3244_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___y_3218_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3244_, 1, v___y_3204_);
                        v___x_3242_ = v_reuseFailAlloc_3244_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_3226_ = leanh::lean_ctor_get(v_a_3222_, 0);
                v_snd_3227_ = leanh::lean_ctor_get(v_a_3222_, 1);
                v_isSharedCheck_3239_ = (!leanh::lean_is_exclusive(v_a_3222_)) as u8;
                if v_isSharedCheck_3239_ == 0 {
                    v___x_3229_ = v_a_3222_;
                    v_isShared_3230_ = v_isSharedCheck_3239_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3227_);
                    leanh::lean_inc(v_fst_3226_);
                    leanh::lean_dec(v_a_3222_);
                    v___x_3229_ = leanh::lean_box(0);
                    v_isShared_3230_ = v_isSharedCheck_3239_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3231_ = l_Lean_mkNatLit(v_k_3213_);
                v___x_3232_ = l_Lean_mkAppB(v_fst_3226_, v___y_3218_, v___x_3231_);
                if v_isShared_3230_ == 0 {
                    leanh::lean_ctor_set(v___x_3229_, 0, v___x_3232_);
                    v___x_3234_ = v___x_3229_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3238_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3232_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_snd_3227_);
                    v___x_3234_ = v_reuseFailAlloc_3238_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3225_ == 0 {
                    leanh::lean_ctor_set(v___x_3224_, 0, v___x_3234_);
                    v___x_3236_ = v___x_3224_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3237_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
                    v___x_3236_ = v_reuseFailAlloc_3237_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3236_;
            }
            7 => {
                v___x_3243_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3243_, 0, v___x_3242_);
                return v___x_3243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9___boxed(
    mut v_pw_3251_: *mut leanh::LeanObject,
    mut v___y_3252_: *mut leanh::LeanObject,
    mut v___y_3253_: *mut leanh::LeanObject,
    mut v___y_3254_: *mut leanh::LeanObject,
    mut v___y_3255_: *mut leanh::LeanObject,
    mut v___y_3256_: *mut leanh::LeanObject,
    mut v___y_3257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3258_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9(v_pw_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
    leanh::lean_dec(v___y_3256_);
    leanh::lean_dec_ref(v___y_3255_);
    leanh::lean_dec(v___y_3254_);
    leanh::lean_dec_ref(v___y_3253_);
    return v_res_3258_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__10(
    mut v_m_3259_: *mut leanh::LeanObject,
    mut v_acc_3260_: *mut leanh::LeanObject,
    mut v___y_3261_: *mut leanh::LeanObject,
    mut v___y_3262_: *mut leanh::LeanObject,
    mut v___y_3263_: *mut leanh::LeanObject,
    mut v___y_3264_: *mut leanh::LeanObject,
    mut v___y_3265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_m_3259_) == 0 {
                    v___x_3267_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3267_, 0, v_acc_3260_);
                    leanh::lean_ctor_set(v___x_3267_, 1, v___y_3261_);
                    v___x_3268_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3268_, 0, v___x_3267_);
                    return v___x_3268_;
                } else {
                    v_p_3269_ = leanh::lean_ctor_get(v_m_3259_, 0);
                    leanh::lean_inc_ref(v_p_3269_);
                    v_m_3270_ = leanh::lean_ctor_get(v_m_3259_, 1);
                    leanh::lean_inc(v_m_3270_);
                    leanh::lean_dec_ref_known(v_m_3259_, 2);
                    v___x_3271_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5(v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
                    if leanh::lean_obj_tag(v___x_3271_) == 0 {
                        v_a_3272_ = leanh::lean_ctor_get(v___x_3271_, 0);
                        leanh::lean_inc(v_a_3272_);
                        leanh::lean_dec_ref_known(v___x_3271_, 1);
                        v_fst_3273_ = leanh::lean_ctor_get(v_a_3272_, 0);
                        leanh::lean_inc(v_fst_3273_);
                        v_snd_3274_ = leanh::lean_ctor_get(v_a_3272_, 1);
                        leanh::lean_inc(v_snd_3274_);
                        leanh::lean_dec(v_a_3272_);
                        v___x_3275_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9(v_p_3269_, v_snd_3274_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
                        if leanh::lean_obj_tag(v___x_3275_) == 0 {
                            v_a_3276_ = leanh::lean_ctor_get(v___x_3275_, 0);
                            leanh::lean_inc(v_a_3276_);
                            leanh::lean_dec_ref_known(v___x_3275_, 1);
                            v_fst_3277_ = leanh::lean_ctor_get(v_a_3276_, 0);
                            leanh::lean_inc(v_fst_3277_);
                            v_snd_3278_ = leanh::lean_ctor_get(v_a_3276_, 1);
                            leanh::lean_inc(v_snd_3278_);
                            leanh::lean_dec(v_a_3276_);
                            v___x_3279_ = l_Lean_mkAppB(v_fst_3273_, v_acc_3260_, v_fst_3277_);
                            v_m_3259_ = v_m_3270_;
                            v_acc_3260_ = v___x_3279_;
                            v___y_3261_ = v_snd_3278_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_fst_3273_);
                            leanh::lean_dec(v_m_3270_);
                            leanh::lean_dec_ref(v_acc_3260_);
                            return v___x_3275_;
                        }
                    } else {
                        leanh::lean_dec(v_m_3270_);
                        leanh::lean_dec_ref(v_p_3269_);
                        leanh::lean_dec_ref(v_acc_3260_);
                        return v___x_3271_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__10___boxed(
    mut v_m_3281_: *mut leanh::LeanObject,
    mut v_acc_3282_: *mut leanh::LeanObject,
    mut v___y_3283_: *mut leanh::LeanObject,
    mut v___y_3284_: *mut leanh::LeanObject,
    mut v___y_3285_: *mut leanh::LeanObject,
    mut v___y_3286_: *mut leanh::LeanObject,
    mut v___y_3287_: *mut leanh::LeanObject,
    mut v___y_3288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3289_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__10(v_m_3281_, v_acc_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
    leanh::lean_dec(v___y_3287_);
    leanh::lean_dec_ref(v___y_3286_);
    leanh::lean_dec(v___y_3285_);
    leanh::lean_dec_ref(v___y_3284_);
    return v_res_3289_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3290_ = leanh::lean_unsigned_to_nat(1);
    v___x_3291_ = lean_nat_to_int(v___x_3290_);
    return v___x_3291_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6(
    mut v_m_3292_: *mut leanh::LeanObject,
    mut v___y_3293_: *mut leanh::LeanObject,
    mut v___y_3294_: *mut leanh::LeanObject,
    mut v___y_3295_: *mut leanh::LeanObject,
    mut v___y_3296_: *mut leanh::LeanObject,
    mut v___y_3297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_m_3292_) == 0 {
        let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3299_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6___closed__0), core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6___closed__0_once), _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6___closed__0);
        v___x_3300_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1(v___x_3299_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
        return v___x_3300_;
    } else {
        let mut v_p_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_p_3301_ = leanh::lean_ctor_get(v_m_3292_, 0);
        leanh::lean_inc_ref(v_p_3301_);
        v_m_3302_ = leanh::lean_ctor_get(v_m_3292_, 1);
        leanh::lean_inc(v_m_3302_);
        leanh::lean_dec_ref_known(v_m_3292_, 2);
        v___x_3303_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__9(v_p_3301_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
        if leanh::lean_obj_tag(v___x_3303_) == 0 {
            let mut v_a_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_3304_ = leanh::lean_ctor_get(v___x_3303_, 0);
            leanh::lean_inc(v_a_3304_);
            leanh::lean_dec_ref_known(v___x_3303_, 1);
            v_fst_3305_ = leanh::lean_ctor_get(v_a_3304_, 0);
            leanh::lean_inc(v_fst_3305_);
            v_snd_3306_ = leanh::lean_ctor_get(v_a_3304_, 1);
            leanh::lean_inc(v_snd_3306_);
            leanh::lean_dec(v_a_3304_);
            v___x_3307_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6_spec__10(v_m_3302_, v_fst_3305_, v_snd_3306_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
            return v___x_3307_;
        } else {
            leanh::lean_dec(v_m_3302_);
            return v___x_3303_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_m_3308_: *mut leanh::LeanObject,
    mut v___y_3309_: *mut leanh::LeanObject,
    mut v___y_3310_: *mut leanh::LeanObject,
    mut v___y_3311_: *mut leanh::LeanObject,
    mut v___y_3312_: *mut leanh::LeanObject,
    mut v___y_3313_: *mut leanh::LeanObject,
    mut v___y_3314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3315_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6(v_m_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
    leanh::lean_dec(v___y_3313_);
    leanh::lean_dec_ref(v___y_3312_);
    leanh::lean_dec(v___y_3311_);
    leanh::lean_dec_ref(v___y_3310_);
    return v_res_3315_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2(
    mut v_k_3316_: *mut leanh::LeanObject,
    mut v_m_3317_: *mut leanh::LeanObject,
    mut v___y_3318_: *mut leanh::LeanObject,
    mut v___y_3319_: *mut leanh::LeanObject,
    mut v___y_3320_: *mut leanh::LeanObject,
    mut v___y_3321_: *mut leanh::LeanObject,
    mut v___y_3322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: u8 = 0;
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3338_: u8 = 0;
    let mut v_fst_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3343_: u8 = 0;
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3351_: u8 = 0;
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3324_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6___closed__0), core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6___closed__0_once), _init_l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6___closed__0);
                v___x_3325_ = lean_int_dec_eq(v_k_3316_, v___x_3324_);
                if v___x_3325_ == 0 {
                    v___x_3326_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5(v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
                    if leanh::lean_obj_tag(v___x_3326_) == 0 {
                        v_a_3327_ = leanh::lean_ctor_get(v___x_3326_, 0);
                        leanh::lean_inc(v_a_3327_);
                        leanh::lean_dec_ref_known(v___x_3326_, 1);
                        v_fst_3328_ = leanh::lean_ctor_get(v_a_3327_, 0);
                        leanh::lean_inc(v_fst_3328_);
                        v_snd_3329_ = leanh::lean_ctor_get(v_a_3327_, 1);
                        leanh::lean_inc(v_snd_3329_);
                        leanh::lean_dec(v_a_3327_);
                        v___x_3330_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1(v_k_3316_, v_snd_3329_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
                        if leanh::lean_obj_tag(v___x_3330_) == 0 {
                            v_a_3331_ = leanh::lean_ctor_get(v___x_3330_, 0);
                            leanh::lean_inc(v_a_3331_);
                            leanh::lean_dec_ref_known(v___x_3330_, 1);
                            v_fst_3332_ = leanh::lean_ctor_get(v_a_3331_, 0);
                            leanh::lean_inc(v_fst_3332_);
                            v_snd_3333_ = leanh::lean_ctor_get(v_a_3331_, 1);
                            leanh::lean_inc(v_snd_3333_);
                            leanh::lean_dec(v_a_3331_);
                            v___x_3334_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6(v_m_3317_, v_snd_3333_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
                            if leanh::lean_obj_tag(v___x_3334_) == 0 {
                                v_a_3335_ = leanh::lean_ctor_get(v___x_3334_, 0);
                                v_isSharedCheck_3352_ =
                                    (!leanh::lean_is_exclusive(v___x_3334_)) as u8;
                                if v_isSharedCheck_3352_ == 0 {
                                    v___x_3337_ = v___x_3334_;
                                    v_isShared_3338_ = v_isSharedCheck_3352_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3335_);
                                    leanh::lean_dec(v___x_3334_);
                                    v___x_3337_ = leanh::lean_box(0);
                                    v_isShared_3338_ = v_isSharedCheck_3352_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_fst_3332_);
                                leanh::lean_dec(v_fst_3328_);
                                return v___x_3334_;
                            }
                        } else {
                            leanh::lean_dec(v_fst_3328_);
                            leanh::lean_dec(v_m_3317_);
                            return v___x_3330_;
                        }
                    } else {
                        leanh::lean_dec(v_m_3317_);
                        return v___x_3326_;
                    }
                } else {
                    v___x_3353_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__6(v_m_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
                    return v___x_3353_;
                }
            }
            1 => {
                v_fst_3339_ = leanh::lean_ctor_get(v_a_3335_, 0);
                v_snd_3340_ = leanh::lean_ctor_get(v_a_3335_, 1);
                v_isSharedCheck_3351_ = (!leanh::lean_is_exclusive(v_a_3335_)) as u8;
                if v_isSharedCheck_3351_ == 0 {
                    v___x_3342_ = v_a_3335_;
                    v_isShared_3343_ = v_isSharedCheck_3351_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3340_);
                    leanh::lean_inc(v_fst_3339_);
                    leanh::lean_dec(v_a_3335_);
                    v___x_3342_ = leanh::lean_box(0);
                    v_isShared_3343_ = v_isSharedCheck_3351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3344_ = l_Lean_mkAppB(v_fst_3328_, v_fst_3332_, v_fst_3339_);
                if v_isShared_3343_ == 0 {
                    leanh::lean_ctor_set(v___x_3342_, 0, v___x_3344_);
                    v___x_3346_ = v___x_3342_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3350_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3350_, 1, v_snd_3340_);
                    v___x_3346_ = v_reuseFailAlloc_3350_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3338_ == 0 {
                    leanh::lean_ctor_set(v___x_3337_, 0, v___x_3346_);
                    v___x_3348_ = v___x_3337_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3349_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
                    v___x_3348_ = v_reuseFailAlloc_3349_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_k_3354_: *mut leanh::LeanObject,
    mut v_m_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
    mut v___y_3357_: *mut leanh::LeanObject,
    mut v___y_3358_: *mut leanh::LeanObject,
    mut v___y_3359_: *mut leanh::LeanObject,
    mut v___y_3360_: *mut leanh::LeanObject,
    mut v___y_3361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3362_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2(v_k_3354_, v_m_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_);
    leanh::lean_dec(v___y_3360_);
    leanh::lean_dec_ref(v___y_3359_);
    leanh::lean_dec(v___y_3358_);
    leanh::lean_dec_ref(v___y_3357_);
    leanh::lean_dec(v_k_3354_);
    return v_res_3362_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8(
    mut v___y_3379_: *mut leanh::LeanObject,
    mut v___y_3380_: *mut leanh::LeanObject,
    mut v___y_3381_: *mut leanh::LeanObject,
    mut v___y_3382_: *mut leanh::LeanObject,
    mut v___y_3383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3390_: u8 = 0;
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3395_: u8 = 0;
    let mut v_type_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v_snd_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRing_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3419_: u8 = 0;
    let mut v_invFn_x3f_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_3433_: u8 = 0;
    let mut v_invSet_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_3437_: u8 = 0;
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v_id_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3459_: u8 = 0;
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3473_: u8 = 0;
    let mut v_unused_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut v_unused_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v_unused_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_3385_ = leanh::lean_ctor_get(v___y_3379_, 0);
                v_addFn_x3f_3386_ = leanh::lean_ctor_get(v_toRing_3385_, 6);
                leanh::lean_inc(v_addFn_x3f_3386_);
                if leanh::lean_obj_tag(v_addFn_x3f_3386_) == 1 {
                    v_val_3387_ = leanh::lean_ctor_get(v_addFn_x3f_3386_, 0);
                    v_isSharedCheck_3395_ =
                        (!leanh::lean_is_exclusive(v_addFn_x3f_3386_)) as u8;
                    if v_isSharedCheck_3395_ == 0 {
                        v___x_3389_ = v_addFn_x3f_3386_;
                        v_isShared_3390_ = v_isSharedCheck_3395_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3387_);
                        leanh::lean_dec(v_addFn_x3f_3386_);
                        v___x_3389_ = leanh::lean_box(0);
                        v_isShared_3390_ = v_isSharedCheck_3395_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_addFn_x3f_3386_);
                    v_type_3396_ = leanh::lean_ctor_get(v_toRing_3385_, 1);
                    leanh::lean_inc_ref_n(v_type_3396_, 3);
                    v_u_3397_ = leanh::lean_ctor_get(v_toRing_3385_, 2);
                    leanh::lean_inc_n(v_u_3397_, 2);
                    v_semiringInst_3398_ = leanh::lean_ctor_get(v_toRing_3385_, 4);
                    v___x_3399_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__1;
                    v___x_3400_ = leanh::lean_box(0);
                    v___x_3401_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3401_, 0, v_u_3397_);
                    leanh::lean_ctor_set(v___x_3401_, 1, v___x_3400_);
                    leanh::lean_inc_ref(v___x_3401_);
                    v___x_3402_ = l_Lean_mkConst(v___x_3399_, v___x_3401_);
                    v___x_3403_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__3;
                    v___x_3404_ = l_Lean_mkConst(v___x_3403_, v___x_3401_);
                    leanh::lean_inc_ref(v_semiringInst_3398_);
                    v___x_3405_ = l_Lean_mkAppB(v___x_3404_, v_type_3396_, v_semiringInst_3398_);
                    v_expectedInst_3406_ = l_Lean_mkAppB(v___x_3402_, v_type_3396_, v___x_3405_);
                    v___x_3407_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__5;
                    v___x_3408_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___closed__7;
                    v___x_3409_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2_spec__5_spec__7(v_type_3396_, v_u_3397_, v___x_3407_, v___x_3408_, v_expectedInst_3406_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
                    if leanh::lean_obj_tag(v___x_3409_) == 0 {
                        v_a_3410_ = leanh::lean_ctor_get(v___x_3409_, 0);
                        v_isSharedCheck_3479_ =
                            (!leanh::lean_is_exclusive(v___x_3409_)) as u8;
                        if v_isSharedCheck_3479_ == 0 {
                            v___x_3412_ = v___x_3409_;
                            v_isShared_3413_ = v_isSharedCheck_3479_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3410_);
                            leanh::lean_dec(v___x_3409_);
                            v___x_3412_ = leanh::lean_box(0);
                            v_isShared_3413_ = v_isSharedCheck_3479_;
                            state = 3;
                            continue;
                        }
                    } else {
                        return v___x_3409_;
                    }
                }
            }
            1 => {
                v___x_3391_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3391_, 0, v_val_3387_);
                leanh::lean_ctor_set(v___x_3391_, 1, v___y_3379_);
                if v_isShared_3390_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3389_, 0);
                    leanh::lean_ctor_set(v___x_3389_, 0, v___x_3391_);
                    v___x_3393_ = v___x_3389_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3394_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
                    v___x_3393_ = v_reuseFailAlloc_3394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3393_;
            }
            3 => {
                v_snd_3414_ = leanh::lean_ctor_get(v_a_3410_, 1);
                leanh::lean_inc(v_snd_3414_);
                v_toRing_3415_ = leanh::lean_ctor_get(v_snd_3414_, 0);
                leanh::lean_inc_ref(v_toRing_3415_);
                v_fst_3416_ = leanh::lean_ctor_get(v_a_3410_, 0);
                v_isSharedCheck_3477_ = (!leanh::lean_is_exclusive(v_a_3410_)) as u8;
                if v_isSharedCheck_3477_ == 0 {
                    v_unused_3478_ = leanh::lean_ctor_get(v_a_3410_, 1);
                    leanh::lean_dec(v_unused_3478_);
                    v___x_3418_ = v_a_3410_;
                    v_isShared_3419_ = v_isSharedCheck_3477_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_3416_);
                    leanh::lean_dec(v_a_3410_);
                    v___x_3418_ = leanh::lean_box(0);
                    v_isShared_3419_ = v_isSharedCheck_3477_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_invFn_x3f_3420_ = leanh::lean_ctor_get(v_snd_3414_, 1);
                v_semiringId_x3f_3421_ = leanh::lean_ctor_get(v_snd_3414_, 2);
                v_commSemiringInst_3422_ = leanh::lean_ctor_get(v_snd_3414_, 3);
                v_commRingInst_3423_ = leanh::lean_ctor_get(v_snd_3414_, 4);
                v_noZeroDivInst_x3f_3424_ = leanh::lean_ctor_get(v_snd_3414_, 5);
                v_fieldInst_x3f_3425_ = leanh::lean_ctor_get(v_snd_3414_, 6);
                v_powIdentityInst_x3f_3426_ = leanh::lean_ctor_get(v_snd_3414_, 7);
                v_denoteEntries_3427_ = leanh::lean_ctor_get(v_snd_3414_, 8);
                v_nextId_3428_ = leanh::lean_ctor_get(v_snd_3414_, 9);
                v_steps_3429_ = leanh::lean_ctor_get(v_snd_3414_, 10);
                v_queue_3430_ = leanh::lean_ctor_get(v_snd_3414_, 11);
                v_basis_3431_ = leanh::lean_ctor_get(v_snd_3414_, 12);
                v_diseqs_3432_ = leanh::lean_ctor_get(v_snd_3414_, 13);
                v_recheck_3433_ = leanh::lean_ctor_get_uint8(
                    v_snd_3414_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_3434_ = leanh::lean_ctor_get(v_snd_3414_, 14);
                v_powIdentityVarCount_3435_ = leanh::lean_ctor_get(v_snd_3414_, 15);
                v_numEq0_x3f_3436_ = leanh::lean_ctor_get(v_snd_3414_, 16);
                v_numEq0Updated_3437_ = leanh::lean_ctor_get_uint8(
                    v_snd_3414_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_3475_ = (!leanh::lean_is_exclusive(v_snd_3414_)) as u8;
                if v_isSharedCheck_3475_ == 0 {
                    v_unused_3476_ = leanh::lean_ctor_get(v_snd_3414_, 0);
                    leanh::lean_dec(v_unused_3476_);
                    v___x_3439_ = v_snd_3414_;
                    v_isShared_3440_ = v_isSharedCheck_3475_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_3436_);
                    leanh::lean_inc(v_powIdentityVarCount_3435_);
                    leanh::lean_inc(v_invSet_3434_);
                    leanh::lean_inc(v_diseqs_3432_);
                    leanh::lean_inc(v_basis_3431_);
                    leanh::lean_inc(v_queue_3430_);
                    leanh::lean_inc(v_steps_3429_);
                    leanh::lean_inc(v_nextId_3428_);
                    leanh::lean_inc(v_denoteEntries_3427_);
                    leanh::lean_inc(v_powIdentityInst_x3f_3426_);
                    leanh::lean_inc(v_fieldInst_x3f_3425_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_3424_);
                    leanh::lean_inc(v_commRingInst_3423_);
                    leanh::lean_inc(v_commSemiringInst_3422_);
                    leanh::lean_inc(v_semiringId_x3f_3421_);
                    leanh::lean_inc(v_invFn_x3f_3420_);
                    leanh::lean_dec(v_snd_3414_);
                    v___x_3439_ = leanh::lean_box(0);
                    v_isShared_3440_ = v_isSharedCheck_3475_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_id_3441_ = leanh::lean_ctor_get(v_toRing_3415_, 0);
                v_type_3442_ = leanh::lean_ctor_get(v_toRing_3415_, 1);
                v_u_3443_ = leanh::lean_ctor_get(v_toRing_3415_, 2);
                v_ringInst_3444_ = leanh::lean_ctor_get(v_toRing_3415_, 3);
                v_semiringInst_3445_ = leanh::lean_ctor_get(v_toRing_3415_, 4);
                v_charInst_x3f_3446_ = leanh::lean_ctor_get(v_toRing_3415_, 5);
                v_mulFn_x3f_3447_ = leanh::lean_ctor_get(v_toRing_3415_, 7);
                v_subFn_x3f_3448_ = leanh::lean_ctor_get(v_toRing_3415_, 8);
                v_negFn_x3f_3449_ = leanh::lean_ctor_get(v_toRing_3415_, 9);
                v_powFn_x3f_3450_ = leanh::lean_ctor_get(v_toRing_3415_, 10);
                v_intCastFn_x3f_3451_ = leanh::lean_ctor_get(v_toRing_3415_, 11);
                v_natCastFn_x3f_3452_ = leanh::lean_ctor_get(v_toRing_3415_, 12);
                v_one_x3f_3453_ = leanh::lean_ctor_get(v_toRing_3415_, 13);
                v_vars_3454_ = leanh::lean_ctor_get(v_toRing_3415_, 14);
                v_varMap_3455_ = leanh::lean_ctor_get(v_toRing_3415_, 15);
                v_denote_3456_ = leanh::lean_ctor_get(v_toRing_3415_, 16);
                v_isSharedCheck_3473_ = (!leanh::lean_is_exclusive(v_toRing_3415_)) as u8;
                if v_isSharedCheck_3473_ == 0 {
                    v_unused_3474_ = leanh::lean_ctor_get(v_toRing_3415_, 6);
                    leanh::lean_dec(v_unused_3474_);
                    v___x_3458_ = v_toRing_3415_;
                    v_isShared_3459_ = v_isSharedCheck_3473_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_3456_);
                    leanh::lean_inc(v_varMap_3455_);
                    leanh::lean_inc(v_vars_3454_);
                    leanh::lean_inc(v_one_x3f_3453_);
                    leanh::lean_inc(v_natCastFn_x3f_3452_);
                    leanh::lean_inc(v_intCastFn_x3f_3451_);
                    leanh::lean_inc(v_powFn_x3f_3450_);
                    leanh::lean_inc(v_negFn_x3f_3449_);
                    leanh::lean_inc(v_subFn_x3f_3448_);
                    leanh::lean_inc(v_mulFn_x3f_3447_);
                    leanh::lean_inc(v_charInst_x3f_3446_);
                    leanh::lean_inc(v_semiringInst_3445_);
                    leanh::lean_inc(v_ringInst_3444_);
                    leanh::lean_inc(v_u_3443_);
                    leanh::lean_inc(v_type_3442_);
                    leanh::lean_inc(v_id_3441_);
                    leanh::lean_dec(v_toRing_3415_);
                    v___x_3458_ = leanh::lean_box(0);
                    v_isShared_3459_ = v_isSharedCheck_3473_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc(v_fst_3416_);
                v___x_3460_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3460_, 0, v_fst_3416_);
                if v_isShared_3459_ == 0 {
                    leanh::lean_ctor_set(v___x_3458_, 6, v___x_3460_);
                    v___x_3462_ = v___x_3458_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3472_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_id_3441_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_type_3442_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 2, v_u_3443_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 3, v_ringInst_3444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 4, v_semiringInst_3445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 5, v_charInst_x3f_3446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 6, v___x_3460_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 7, v_mulFn_x3f_3447_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 8, v_subFn_x3f_3448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 9, v_negFn_x3f_3449_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 10, v_powFn_x3f_3450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 11, v_intCastFn_x3f_3451_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 12, v_natCastFn_x3f_3452_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 13, v_one_x3f_3453_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 14, v_vars_3454_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 15, v_varMap_3455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3472_, 16, v_denote_3456_);
                    v___x_3462_ = v_reuseFailAlloc_3472_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3440_ == 0 {
                    leanh::lean_ctor_set(v___x_3439_, 0, v___x_3462_);
                    v___x_3464_ = v___x_3439_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3471_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_invFn_x3f_3420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 2, v_semiringId_x3f_3421_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3471_,
                        3,
                        v_commSemiringInst_3422_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 4, v_commRingInst_3423_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3471_,
                        5,
                        v_noZeroDivInst_x3f_3424_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 6, v_fieldInst_x3f_3425_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3471_,
                        7,
                        v_powIdentityInst_x3f_3426_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 8, v_denoteEntries_3427_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 9, v_nextId_3428_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 10, v_steps_3429_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 11, v_queue_3430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 12, v_basis_3431_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 13, v_diseqs_3432_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 14, v_invSet_3434_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3471_,
                        15,
                        v_powIdentityVarCount_3435_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 16, v_numEq0_x3f_3436_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3471_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_3433_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3471_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_3437_,
                    );
                    v___x_3464_ = v_reuseFailAlloc_3471_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3419_ == 0 {
                    leanh::lean_ctor_set(v___x_3418_, 1, v___x_3464_);
                    v___x_3466_ = v___x_3418_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3470_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_fst_3416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 1, v___x_3464_);
                    v___x_3466_ = v_reuseFailAlloc_3470_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3413_ == 0 {
                    leanh::lean_ctor_set(v___x_3412_, 0, v___x_3466_);
                    v___x_3468_ = v___x_3412_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3466_);
                    v___x_3468_ = v_reuseFailAlloc_3469_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8___boxed(
    mut v___y_3480_: *mut leanh::LeanObject,
    mut v___y_3481_: *mut leanh::LeanObject,
    mut v___y_3482_: *mut leanh::LeanObject,
    mut v___y_3483_: *mut leanh::LeanObject,
    mut v___y_3484_: *mut leanh::LeanObject,
    mut v___y_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3486_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8(v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
    leanh::lean_dec(v___y_3484_);
    leanh::lean_dec_ref(v___y_3483_);
    leanh::lean_dec(v___y_3482_);
    leanh::lean_dec_ref(v___y_3481_);
    return v_res_3486_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3(
    mut v_p_3487_: *mut leanh::LeanObject,
    mut v_acc_3488_: *mut leanh::LeanObject,
    mut v___y_3489_: *mut leanh::LeanObject,
    mut v___y_3490_: *mut leanh::LeanObject,
    mut v___y_3491_: *mut leanh::LeanObject,
    mut v___y_3492_: *mut leanh::LeanObject,
    mut v___y_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: u8 = 0;
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v_fst_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3514_: u8 = 0;
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_isSharedCheck_3523_: u8 = 0;
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut v_k_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_3487_) == 0 {
                    v_k_3495_ = leanh::lean_ctor_get(v_p_3487_, 0);
                    v_isSharedCheck_3528_ = (!leanh::lean_is_exclusive(v_p_3487_)) as u8;
                    if v_isSharedCheck_3528_ == 0 {
                        v___x_3497_ = v_p_3487_;
                        v_isShared_3498_ = v_isSharedCheck_3528_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_3495_);
                        leanh::lean_dec(v_p_3487_);
                        v___x_3497_ = leanh::lean_box(0);
                        v_isShared_3498_ = v_isSharedCheck_3528_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_3529_ = leanh::lean_ctor_get(v_p_3487_, 0);
                    leanh::lean_inc(v_k_3529_);
                    v_v_3530_ = leanh::lean_ctor_get(v_p_3487_, 1);
                    leanh::lean_inc(v_v_3530_);
                    v_p_3531_ = leanh::lean_ctor_get(v_p_3487_, 2);
                    leanh::lean_inc_ref(v_p_3531_);
                    leanh::lean_dec_ref_known(v_p_3487_, 3);
                    v___x_3532_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8(v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
                    if leanh::lean_obj_tag(v___x_3532_) == 0 {
                        v_a_3533_ = leanh::lean_ctor_get(v___x_3532_, 0);
                        leanh::lean_inc(v_a_3533_);
                        leanh::lean_dec_ref_known(v___x_3532_, 1);
                        v_fst_3534_ = leanh::lean_ctor_get(v_a_3533_, 0);
                        leanh::lean_inc(v_fst_3534_);
                        v_snd_3535_ = leanh::lean_ctor_get(v_a_3533_, 1);
                        leanh::lean_inc(v_snd_3535_);
                        leanh::lean_dec(v_a_3533_);
                        v___x_3536_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2(v_k_3529_, v_v_3530_, v_snd_3535_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
                        leanh::lean_dec(v_k_3529_);
                        if leanh::lean_obj_tag(v___x_3536_) == 0 {
                            v_a_3537_ = leanh::lean_ctor_get(v___x_3536_, 0);
                            leanh::lean_inc(v_a_3537_);
                            leanh::lean_dec_ref_known(v___x_3536_, 1);
                            v_fst_3538_ = leanh::lean_ctor_get(v_a_3537_, 0);
                            leanh::lean_inc(v_fst_3538_);
                            v_snd_3539_ = leanh::lean_ctor_get(v_a_3537_, 1);
                            leanh::lean_inc(v_snd_3539_);
                            leanh::lean_dec(v_a_3537_);
                            v___x_3540_ = l_Lean_mkAppB(v_fst_3534_, v_acc_3488_, v_fst_3538_);
                            v_p_3487_ = v_p_3531_;
                            v_acc_3488_ = v___x_3540_;
                            v___y_3489_ = v_snd_3539_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_fst_3534_);
                            leanh::lean_dec_ref(v_p_3531_);
                            leanh::lean_dec_ref(v_acc_3488_);
                            return v___x_3536_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_p_3531_);
                        leanh::lean_dec(v_v_3530_);
                        leanh::lean_dec(v_k_3529_);
                        leanh::lean_dec_ref(v_acc_3488_);
                        return v___x_3532_;
                    }
                }
            }
            1 => {
                v___x_3499_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4);
                v___x_3500_ = lean_int_dec_eq(v_k_3495_, v___x_3499_);
                if v___x_3500_ == 0 {
                    leanh::lean_del_object(v___x_3497_);
                    v___x_3501_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3_spec__8(v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
                    if leanh::lean_obj_tag(v___x_3501_) == 0 {
                        v_a_3502_ = leanh::lean_ctor_get(v___x_3501_, 0);
                        leanh::lean_inc(v_a_3502_);
                        leanh::lean_dec_ref_known(v___x_3501_, 1);
                        v_fst_3503_ = leanh::lean_ctor_get(v_a_3502_, 0);
                        leanh::lean_inc(v_fst_3503_);
                        v_snd_3504_ = leanh::lean_ctor_get(v_a_3502_, 1);
                        leanh::lean_inc(v_snd_3504_);
                        leanh::lean_dec(v_a_3502_);
                        v___x_3505_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1(v_k_3495_, v_snd_3504_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
                        leanh::lean_dec(v_k_3495_);
                        if leanh::lean_obj_tag(v___x_3505_) == 0 {
                            v_a_3506_ = leanh::lean_ctor_get(v___x_3505_, 0);
                            v_isSharedCheck_3523_ =
                                (!leanh::lean_is_exclusive(v___x_3505_)) as u8;
                            if v_isSharedCheck_3523_ == 0 {
                                v___x_3508_ = v___x_3505_;
                                v_isShared_3509_ = v_isSharedCheck_3523_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3506_);
                                leanh::lean_dec(v___x_3505_);
                                v___x_3508_ = leanh::lean_box(0);
                                v_isShared_3509_ = v_isSharedCheck_3523_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_fst_3503_);
                            leanh::lean_dec_ref(v_acc_3488_);
                            return v___x_3505_;
                        }
                    } else {
                        leanh::lean_dec(v_k_3495_);
                        leanh::lean_dec_ref(v_acc_3488_);
                        return v___x_3501_;
                    }
                } else {
                    leanh::lean_dec(v_k_3495_);
                    v___x_3524_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3524_, 0, v_acc_3488_);
                    leanh::lean_ctor_set(v___x_3524_, 1, v___y_3489_);
                    if v_isShared_3498_ == 0 {
                        leanh::lean_ctor_set(v___x_3497_, 0, v___x_3524_);
                        v___x_3526_ = v___x_3497_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
                        v___x_3526_ = v_reuseFailAlloc_3527_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3510_ = leanh::lean_ctor_get(v_a_3506_, 0);
                v_snd_3511_ = leanh::lean_ctor_get(v_a_3506_, 1);
                v_isSharedCheck_3522_ = (!leanh::lean_is_exclusive(v_a_3506_)) as u8;
                if v_isSharedCheck_3522_ == 0 {
                    v___x_3513_ = v_a_3506_;
                    v_isShared_3514_ = v_isSharedCheck_3522_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3511_);
                    leanh::lean_inc(v_fst_3510_);
                    leanh::lean_dec(v_a_3506_);
                    v___x_3513_ = leanh::lean_box(0);
                    v_isShared_3514_ = v_isSharedCheck_3522_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3515_ = l_Lean_mkAppB(v_fst_3503_, v_acc_3488_, v_fst_3510_);
                if v_isShared_3514_ == 0 {
                    leanh::lean_ctor_set(v___x_3513_, 0, v___x_3515_);
                    v___x_3517_ = v___x_3513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3521_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3515_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_snd_3511_);
                    v___x_3517_ = v_reuseFailAlloc_3521_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3509_ == 0 {
                    leanh::lean_ctor_set(v___x_3508_, 0, v___x_3517_);
                    v___x_3519_ = v___x_3508_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3520_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
                    v___x_3519_ = v_reuseFailAlloc_3520_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3519_;
            }
            6 => {
                return v___x_3526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3___boxed(
    mut v_p_3542_: *mut leanh::LeanObject,
    mut v_acc_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
    mut v___y_3545_: *mut leanh::LeanObject,
    mut v___y_3546_: *mut leanh::LeanObject,
    mut v___y_3547_: *mut leanh::LeanObject,
    mut v___y_3548_: *mut leanh::LeanObject,
    mut v___y_3549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3550_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3(v_p_3542_, v_acc_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
    leanh::lean_dec(v___y_3548_);
    leanh::lean_dec_ref(v___y_3547_);
    leanh::lean_dec(v___y_3546_);
    leanh::lean_dec_ref(v___y_3545_);
    return v_res_3550_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0(
    mut v_p_3551_: *mut leanh::LeanObject,
    mut v___y_3552_: *mut leanh::LeanObject,
    mut v___y_3553_: *mut leanh::LeanObject,
    mut v___y_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_3551_) == 0 {
        let mut v_k_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_3558_ = leanh::lean_ctor_get(v_p_3551_, 0);
        leanh::lean_inc(v_k_3558_);
        leanh::lean_dec_ref_known(v_p_3551_, 1);
        v___x_3559_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1(v_k_3558_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
        leanh::lean_dec(v_k_3558_);
        return v___x_3559_;
    } else {
        let mut v_k_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_3560_ = leanh::lean_ctor_get(v_p_3551_, 0);
        leanh::lean_inc(v_k_3560_);
        v_v_3561_ = leanh::lean_ctor_get(v_p_3551_, 1);
        leanh::lean_inc(v_v_3561_);
        v_p_3562_ = leanh::lean_ctor_get(v_p_3551_, 2);
        leanh::lean_inc_ref(v_p_3562_);
        leanh::lean_dec_ref_known(v_p_3551_, 3);
        v___x_3563_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_denoteTerm___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__2(v_k_3560_, v_v_3561_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
        leanh::lean_dec(v_k_3560_);
        if leanh::lean_obj_tag(v___x_3563_) == 0 {
            let mut v_a_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_3564_ = leanh::lean_ctor_get(v___x_3563_, 0);
            leanh::lean_inc(v_a_3564_);
            leanh::lean_dec_ref_known(v___x_3563_, 1);
            v_fst_3565_ = leanh::lean_ctor_get(v_a_3564_, 0);
            leanh::lean_inc(v_fst_3565_);
            v_snd_3566_ = leanh::lean_ctor_get(v_a_3564_, 1);
            leanh::lean_inc(v_snd_3566_);
            leanh::lean_dec(v_a_3564_);
            v___x_3567_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Poly_denoteExpr_go___at___00Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0_spec__3(v_p_3562_, v_fst_3565_, v_snd_3566_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
            return v___x_3567_;
        } else {
            leanh::lean_dec_ref(v_p_3562_);
            return v___x_3563_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0___boxed(
    mut v_p_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
    mut v___y_3572_: *mut leanh::LeanObject,
    mut v___y_3573_: *mut leanh::LeanObject,
    mut v___y_3574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3575_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0(v_p_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
    leanh::lean_dec(v___y_3573_);
    leanh::lean_dec_ref(v___y_3572_);
    leanh::lean_dec(v___y_3571_);
    leanh::lean_dec_ref(v___y_3570_);
    return v_res_3575_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0(
    mut v_c_3576_: *mut leanh::LeanObject,
    mut v___y_3577_: *mut leanh::LeanObject,
    mut v___y_3578_: *mut leanh::LeanObject,
    mut v___y_3579_: *mut leanh::LeanObject,
    mut v___y_3580_: *mut leanh::LeanObject,
    mut v___y_3581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_3583_ = leanh::lean_ctor_get(v_c_3576_, 0);
    leanh::lean_inc_ref(v_p_3583_);
    leanh::lean_dec_ref(v_c_3576_);
    v___x_3584_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0(v_p_3583_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
    if leanh::lean_obj_tag(v___x_3584_) == 0 {
        let mut v_a_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3585_ = leanh::lean_ctor_get(v___x_3584_, 0);
        leanh::lean_inc(v_a_3585_);
        leanh::lean_dec_ref_known(v___x_3584_, 1);
        v_fst_3586_ = leanh::lean_ctor_get(v_a_3585_, 0);
        leanh::lean_inc(v_fst_3586_);
        v_snd_3587_ = leanh::lean_ctor_get(v_a_3585_, 1);
        leanh::lean_inc(v_snd_3587_);
        leanh::lean_dec(v_a_3585_);
        v___x_3588_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4);
        v___x_3589_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1(v___x_3588_, v_snd_3587_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
        if leanh::lean_obj_tag(v___x_3589_) == 0 {
            let mut v_a_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_3590_ = leanh::lean_ctor_get(v___x_3589_, 0);
            leanh::lean_inc(v_a_3590_);
            leanh::lean_dec_ref_known(v___x_3589_, 1);
            v_fst_3591_ = leanh::lean_ctor_get(v_a_3590_, 0);
            leanh::lean_inc(v_fst_3591_);
            v_snd_3592_ = leanh::lean_ctor_get(v_a_3590_, 1);
            leanh::lean_inc(v_snd_3592_);
            leanh::lean_dec(v_a_3590_);
            v___x_3593_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg(v_fst_3586_, v_fst_3591_, v_snd_3592_);
            return v___x_3593_;
        } else {
            leanh::lean_dec(v_fst_3586_);
            return v___x_3589_;
        }
    } else {
        return v___x_3584_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0___boxed(
    mut v_c_3594_: *mut leanh::LeanObject,
    mut v___y_3595_: *mut leanh::LeanObject,
    mut v___y_3596_: *mut leanh::LeanObject,
    mut v___y_3597_: *mut leanh::LeanObject,
    mut v___y_3598_: *mut leanh::LeanObject,
    mut v___y_3599_: *mut leanh::LeanObject,
    mut v___y_3600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3601_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0(v_c_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
    leanh::lean_dec(v___y_3599_);
    leanh::lean_dec_ref(v___y_3598_);
    leanh::lean_dec(v___y_3597_);
    leanh::lean_dec_ref(v___y_3596_);
    return v_res_3601_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg(
    mut v_as_x27_3606_: *mut leanh::LeanObject,
    mut v_b_3607_: *mut leanh::LeanObject,
    mut v___y_3608_: *mut leanh::LeanObject,
    mut v___y_3609_: *mut leanh::LeanObject,
    mut v___y_3610_: *mut leanh::LeanObject,
    mut v___y_3611_: *mut leanh::LeanObject,
    mut v___y_3612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3606_) == 0 {
                    v___x_3614_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3614_, 0, v_b_3607_);
                    leanh::lean_ctor_set(v___x_3614_, 1, v___y_3608_);
                    v___x_3615_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3615_, 0, v___x_3614_);
                    return v___x_3615_;
                } else {
                    v_head_3616_ = leanh::lean_ctor_get(v_as_x27_3606_, 0);
                    v_tail_3617_ = leanh::lean_ctor_get(v_as_x27_3606_, 1);
                    leanh::lean_inc(v_head_3616_);
                    v___x_3618_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0(v_head_3616_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
                    if leanh::lean_obj_tag(v___x_3618_) == 0 {
                        v_a_3619_ = leanh::lean_ctor_get(v___x_3618_, 0);
                        leanh::lean_inc(v_a_3619_);
                        leanh::lean_dec_ref_known(v___x_3618_, 1);
                        v_fst_3620_ = leanh::lean_ctor_get(v_a_3619_, 0);
                        leanh::lean_inc(v_fst_3620_);
                        v_snd_3621_ = leanh::lean_ctor_get(v_a_3619_, 1);
                        leanh::lean_inc(v_snd_3621_);
                        leanh::lean_dec(v_a_3619_);
                        v___x_3622_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__1;
                        v___x_3623_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1(v_fst_3620_, v___x_3622_);
                        v___x_3624_ = lean_array_push(v_b_3607_, v___x_3623_);
                        v_as_x27_3606_ = v_tail_3617_;
                        v_b_3607_ = v___x_3624_;
                        v___y_3608_ = v_snd_3621_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_b_3607_);
                        v_a_3626_ = leanh::lean_ctor_get(v___x_3618_, 0);
                        v_isSharedCheck_3633_ =
                            (!leanh::lean_is_exclusive(v___x_3618_)) as u8;
                        if v_isSharedCheck_3633_ == 0 {
                            v___x_3628_ = v___x_3618_;
                            v_isShared_3629_ = v_isSharedCheck_3633_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3626_);
                            leanh::lean_dec(v___x_3618_);
                            v___x_3628_ = leanh::lean_box(0);
                            v_isShared_3629_ = v_isSharedCheck_3633_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3629_ == 0 {
                    v___x_3631_ = v___x_3628_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
                    v___x_3631_ = v_reuseFailAlloc_3632_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___boxed(
    mut v_as_x27_3634_: *mut leanh::LeanObject,
    mut v_b_3635_: *mut leanh::LeanObject,
    mut v___y_3636_: *mut leanh::LeanObject,
    mut v___y_3637_: *mut leanh::LeanObject,
    mut v___y_3638_: *mut leanh::LeanObject,
    mut v___y_3639_: *mut leanh::LeanObject,
    mut v___y_3640_: *mut leanh::LeanObject,
    mut v___y_3641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3642_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg(v_as_x27_3634_, v_b_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
    leanh::lean_dec(v___y_3640_);
    leanh::lean_dec_ref(v___y_3639_);
    leanh::lean_dec(v___y_3638_);
    leanh::lean_dec_ref(v___y_3637_);
    leanh::lean_dec(v_as_x27_3634_);
    return v_res_3642_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__3()
-> *mut leanh::LeanObject {
    let mut v___f_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3647_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__0;
    v___x_3648_ = lean_mk_thunk(v___f_3647_);
    return v___x_3648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f(
    mut v_a_3649_: *mut leanh::LeanObject,
    mut v_a_3650_: *mut leanh::LeanObject,
    mut v_a_3651_: *mut leanh::LeanObject,
    mut v_a_3652_: *mut leanh::LeanObject,
    mut v_a_3653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_basis_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v_fst_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3676_: u8 = 0;
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_a_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3681_: u8 = 0;
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_basis_3655_ = leanh::lean_ctor_get(v_a_3649_, 12);
                leanh::lean_inc(v_basis_3655_);
                v_basis_3656_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1___closed__0;
                v___x_3657_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg(v_basis_3655_, v_basis_3656_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
                leanh::lean_dec(v_basis_3655_);
                if leanh::lean_obj_tag(v___x_3657_) == 0 {
                    v_a_3658_ = leanh::lean_ctor_get(v___x_3657_, 0);
                    v_isSharedCheck_3677_ = (!leanh::lean_is_exclusive(v___x_3657_)) as u8;
                    if v_isSharedCheck_3677_ == 0 {
                        v___x_3660_ = v___x_3657_;
                        v_isShared_3661_ = v_isSharedCheck_3677_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3658_);
                        leanh::lean_dec(v___x_3657_);
                        v___x_3660_ = leanh::lean_box(0);
                        v_isShared_3661_ = v_isSharedCheck_3677_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3678_ = leanh::lean_ctor_get(v___x_3657_, 0);
                    v_isSharedCheck_3685_ = (!leanh::lean_is_exclusive(v___x_3657_)) as u8;
                    if v_isSharedCheck_3685_ == 0 {
                        v___x_3680_ = v___x_3657_;
                        v_isShared_3681_ = v_isSharedCheck_3685_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3678_);
                        leanh::lean_dec(v___x_3657_);
                        v___x_3680_ = leanh::lean_box(0);
                        v_isShared_3681_ = v_isSharedCheck_3685_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3662_ = leanh::lean_ctor_get(v_a_3658_, 0);
                v_snd_3663_ = leanh::lean_ctor_get(v_a_3658_, 1);
                v_isSharedCheck_3676_ = (!leanh::lean_is_exclusive(v_a_3658_)) as u8;
                if v_isSharedCheck_3676_ == 0 {
                    v___x_3665_ = v_a_3658_;
                    v_isShared_3666_ = v_isSharedCheck_3676_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3663_);
                    leanh::lean_inc(v_fst_3662_);
                    leanh::lean_dec(v_a_3658_);
                    v___x_3665_ = leanh::lean_box(0);
                    v_isShared_3666_ = v_isSharedCheck_3676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3667_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__2;
                v___x_3668_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___closed__3);
                v___x_3669_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption(v___x_3667_, v___x_3668_, v_fst_3662_);
                if v_isShared_3666_ == 0 {
                    leanh::lean_ctor_set(v___x_3665_, 0, v___x_3669_);
                    v___x_3671_ = v___x_3665_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3675_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3669_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_snd_3663_);
                    v___x_3671_ = v_reuseFailAlloc_3675_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3661_ == 0 {
                    leanh::lean_ctor_set(v___x_3660_, 0, v___x_3671_);
                    v___x_3673_ = v___x_3660_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3674_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
                    v___x_3673_ = v_reuseFailAlloc_3674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3673_;
            }
            5 => {
                if v_isShared_3681_ == 0 {
                    v___x_3683_ = v___x_3680_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
                    v___x_3683_ = v_reuseFailAlloc_3684_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f___boxed(
    mut v_a_3686_: *mut leanh::LeanObject,
    mut v_a_3687_: *mut leanh::LeanObject,
    mut v_a_3688_: *mut leanh::LeanObject,
    mut v_a_3689_: *mut leanh::LeanObject,
    mut v_a_3690_: *mut leanh::LeanObject,
    mut v_a_3691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3692_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f(v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_);
    leanh::lean_dec(v_a_3690_);
    leanh::lean_dec_ref(v_a_3689_);
    leanh::lean_dec(v_a_3688_);
    leanh::lean_dec_ref(v_a_3687_);
    return v_res_3692_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2(
    mut v_a_3693_: *mut leanh::LeanObject,
    mut v_b_3694_: *mut leanh::LeanObject,
    mut v___y_3695_: *mut leanh::LeanObject,
    mut v___y_3696_: *mut leanh::LeanObject,
    mut v___y_3697_: *mut leanh::LeanObject,
    mut v___y_3698_: *mut leanh::LeanObject,
    mut v___y_3699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3701_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg(v_a_3693_, v_b_3694_, v___y_3695_);
    return v___x_3701_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___boxed(
    mut v_a_3702_: *mut leanh::LeanObject,
    mut v_b_3703_: *mut leanh::LeanObject,
    mut v___y_3704_: *mut leanh::LeanObject,
    mut v___y_3705_: *mut leanh::LeanObject,
    mut v___y_3706_: *mut leanh::LeanObject,
    mut v___y_3707_: *mut leanh::LeanObject,
    mut v___y_3708_: *mut leanh::LeanObject,
    mut v___y_3709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3710_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2(v_a_3702_, v_b_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
    leanh::lean_dec(v___y_3708_);
    leanh::lean_dec_ref(v___y_3707_);
    leanh::lean_dec(v___y_3706_);
    leanh::lean_dec_ref(v___y_3705_);
    return v_res_3710_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2(
    mut v_as_3711_: *mut leanh::LeanObject,
    mut v_as_x27_3712_: *mut leanh::LeanObject,
    mut v_b_3713_: *mut leanh::LeanObject,
    mut v_a_3714_: *mut leanh::LeanObject,
    mut v___y_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
    mut v___y_3717_: *mut leanh::LeanObject,
    mut v___y_3718_: *mut leanh::LeanObject,
    mut v___y_3719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg(v_as_x27_3712_, v_b_3713_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
    return v___x_3721_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___boxed(
    mut v_as_3722_: *mut leanh::LeanObject,
    mut v_as_x27_3723_: *mut leanh::LeanObject,
    mut v_b_3724_: *mut leanh::LeanObject,
    mut v_a_3725_: *mut leanh::LeanObject,
    mut v___y_3726_: *mut leanh::LeanObject,
    mut v___y_3727_: *mut leanh::LeanObject,
    mut v___y_3728_: *mut leanh::LeanObject,
    mut v___y_3729_: *mut leanh::LeanObject,
    mut v___y_3730_: *mut leanh::LeanObject,
    mut v___y_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3732_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2(v_as_3722_, v_as_x27_3723_, v_b_3724_, v_a_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
    leanh::lean_dec(v___y_3730_);
    leanh::lean_dec_ref(v___y_3729_);
    leanh::lean_dec(v___y_3728_);
    leanh::lean_dec_ref(v___y_3727_);
    leanh::lean_dec(v_as_x27_3723_);
    leanh::lean_dec(v_as_3722_);
    return v_res_3732_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17(
    mut v_00_u03b1_3733_: *mut leanh::LeanObject,
    mut v_msg_3734_: *mut leanh::LeanObject,
    mut v___y_3735_: *mut leanh::LeanObject,
    mut v___y_3736_: *mut leanh::LeanObject,
    mut v___y_3737_: *mut leanh::LeanObject,
    mut v___y_3738_: *mut leanh::LeanObject,
    mut v___y_3739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3741_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17___redArg(v_msg_3734_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
    return v___x_3741_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17___boxed(
    mut v_00_u03b1_3742_: *mut leanh::LeanObject,
    mut v_msg_3743_: *mut leanh::LeanObject,
    mut v___y_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
    mut v___y_3749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3750_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1_spec__5_spec__11_spec__15_spec__17(v_00_u03b1_3742_, v_msg_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
    leanh::lean_dec(v___y_3748_);
    leanh::lean_dec_ref(v___y_3747_);
    leanh::lean_dec(v___y_3746_);
    leanh::lean_dec_ref(v___y_3745_);
    leanh::lean_dec_ref(v___y_3744_);
    return v_res_3750_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__1;
    v___x_3755_ = l_Lean_MessageData_ofFormat(v___x_3754_);
    return v___x_3755_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0(
    mut v_x_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3757_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___lam__0___closed__2);
    return v___x_3757_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0_spec__0(
    mut v_d_3758_: *mut leanh::LeanObject,
    mut v___y_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
    mut v___y_3762_: *mut leanh::LeanObject,
    mut v___y_3763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3765_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_3758_);
    v___x_3766_ = l_Lean_Grind_CommRing_Poly_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__0(v___x_3765_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
    return v___x_3766_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0_spec__0___boxed(
    mut v_d_3767_: *mut leanh::LeanObject,
    mut v___y_3768_: *mut leanh::LeanObject,
    mut v___y_3769_: *mut leanh::LeanObject,
    mut v___y_3770_: *mut leanh::LeanObject,
    mut v___y_3771_: *mut leanh::LeanObject,
    mut v___y_3772_: *mut leanh::LeanObject,
    mut v___y_3773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3774_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0_spec__0(v_d_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
    leanh::lean_dec(v___y_3772_);
    leanh::lean_dec_ref(v___y_3771_);
    leanh::lean_dec(v___y_3770_);
    leanh::lean_dec_ref(v___y_3769_);
    leanh::lean_dec_ref(v_d_3767_);
    return v_res_3774_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0(
    mut v_c_3775_: *mut leanh::LeanObject,
    mut v___y_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
    mut v___y_3779_: *mut leanh::LeanObject,
    mut v___y_3780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_d_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3796_: u8 = 0;
    let mut v_fst_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3801_: u8 = 0;
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut v_isSharedCheck_3810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_d_3782_ = leanh::lean_ctor_get(v_c_3775_, 4);
                v___x_3783_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___at___00Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0_spec__0(v_d_3782_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
                if leanh::lean_obj_tag(v___x_3783_) == 0 {
                    v_a_3784_ = leanh::lean_ctor_get(v___x_3783_, 0);
                    leanh::lean_inc(v_a_3784_);
                    leanh::lean_dec_ref_known(v___x_3783_, 1);
                    v_fst_3785_ = leanh::lean_ctor_get(v_a_3784_, 0);
                    leanh::lean_inc(v_fst_3785_);
                    v_snd_3786_ = leanh::lean_ctor_get(v_a_3784_, 1);
                    leanh::lean_inc(v_snd_3786_);
                    leanh::lean_dec(v_a_3784_);
                    v___x_3787_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1___closed__4);
                    v___x_3788_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__1(v___x_3787_, v_snd_3786_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
                    if leanh::lean_obj_tag(v___x_3788_) == 0 {
                        v_a_3789_ = leanh::lean_ctor_get(v___x_3788_, 0);
                        leanh::lean_inc(v_a_3789_);
                        leanh::lean_dec_ref_known(v___x_3788_, 1);
                        v_fst_3790_ = leanh::lean_ctor_get(v_a_3789_, 0);
                        leanh::lean_inc(v_fst_3790_);
                        v_snd_3791_ = leanh::lean_ctor_get(v_a_3789_, 1);
                        leanh::lean_inc(v_snd_3791_);
                        leanh::lean_dec(v_a_3789_);
                        v___x_3792_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Meta_Grind_Arith_CommRing_mkEq___at___00Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__0_spec__2___redArg(v_fst_3785_, v_fst_3790_, v_snd_3791_);
                        v_a_3793_ = leanh::lean_ctor_get(v___x_3792_, 0);
                        v_isSharedCheck_3810_ =
                            (!leanh::lean_is_exclusive(v___x_3792_)) as u8;
                        if v_isSharedCheck_3810_ == 0 {
                            v___x_3795_ = v___x_3792_;
                            v_isShared_3796_ = v_isSharedCheck_3810_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3793_);
                            leanh::lean_dec(v___x_3792_);
                            v___x_3795_ = leanh::lean_box(0);
                            v_isShared_3796_ = v_isSharedCheck_3810_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fst_3785_);
                        return v___x_3788_;
                    }
                } else {
                    return v___x_3783_;
                }
            }
            1 => {
                v_fst_3797_ = leanh::lean_ctor_get(v_a_3793_, 0);
                v_snd_3798_ = leanh::lean_ctor_get(v_a_3793_, 1);
                v_isSharedCheck_3809_ = (!leanh::lean_is_exclusive(v_a_3793_)) as u8;
                if v_isSharedCheck_3809_ == 0 {
                    v___x_3800_ = v_a_3793_;
                    v_isShared_3801_ = v_isSharedCheck_3809_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3798_);
                    leanh::lean_inc(v_fst_3797_);
                    leanh::lean_dec(v_a_3793_);
                    v___x_3800_ = leanh::lean_box(0);
                    v_isShared_3801_ = v_isSharedCheck_3809_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3802_ = l_Lean_mkNot(v_fst_3797_);
                if v_isShared_3801_ == 0 {
                    leanh::lean_ctor_set(v___x_3800_, 0, v___x_3802_);
                    v___x_3804_ = v___x_3800_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3808_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_snd_3798_);
                    v___x_3804_ = v_reuseFailAlloc_3808_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3796_ == 0 {
                    leanh::lean_ctor_set(v___x_3795_, 0, v___x_3804_);
                    v___x_3806_ = v___x_3795_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
                    v___x_3806_ = v_reuseFailAlloc_3807_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0___boxed(
    mut v_c_3811_: *mut leanh::LeanObject,
    mut v___y_3812_: *mut leanh::LeanObject,
    mut v___y_3813_: *mut leanh::LeanObject,
    mut v___y_3814_: *mut leanh::LeanObject,
    mut v___y_3815_: *mut leanh::LeanObject,
    mut v___y_3816_: *mut leanh::LeanObject,
    mut v___y_3817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3818_ = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0(v_c_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
    leanh::lean_dec(v___y_3816_);
    leanh::lean_dec_ref(v___y_3815_);
    leanh::lean_dec(v___y_3814_);
    leanh::lean_dec_ref(v___y_3813_);
    leanh::lean_dec_ref(v_c_3811_);
    return v_res_3818_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__3_spec__6(
    mut v_as_3819_: *mut leanh::LeanObject,
    mut v_sz_3820_: usize,
    mut v_i_3821_: usize,
    mut v_b_3822_: *mut leanh::LeanObject,
    mut v___y_3823_: *mut leanh::LeanObject,
    mut v___y_3824_: *mut leanh::LeanObject,
    mut v___y_3825_: *mut leanh::LeanObject,
    mut v___y_3826_: *mut leanh::LeanObject,
    mut v___y_3827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: usize = 0;
    let mut v___x_3848_: usize = 0;
    let mut v_reuseFailAlloc_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v_a_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3855_: u8 = 0;
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3829_ = lean_usize_dec_lt(v_i_3821_, v_sz_3820_);
                if v___x_3829_ == 0 {
                    v___x_3830_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3830_, 0, v_b_3822_);
                    leanh::lean_ctor_set(v___x_3830_, 1, v___y_3823_);
                    v___x_3831_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3831_, 0, v___x_3830_);
                    return v___x_3831_;
                } else {
                    v_snd_3832_ = leanh::lean_ctor_get(v_b_3822_, 1);
                    leanh::lean_inc(v_snd_3832_);
                    leanh::lean_dec_ref(v_b_3822_);
                    v_a_3833_ = lean_array_uget_borrowed(v_as_3819_, v_i_3821_);
                    v___x_3834_ = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0(v_a_3833_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
                    if leanh::lean_obj_tag(v___x_3834_) == 0 {
                        v_a_3835_ = leanh::lean_ctor_get(v___x_3834_, 0);
                        leanh::lean_inc(v_a_3835_);
                        leanh::lean_dec_ref_known(v___x_3834_, 1);
                        v_fst_3836_ = leanh::lean_ctor_get(v_a_3835_, 0);
                        v_snd_3837_ = leanh::lean_ctor_get(v_a_3835_, 1);
                        v_isSharedCheck_3851_ = (!leanh::lean_is_exclusive(v_a_3835_)) as u8;
                        if v_isSharedCheck_3851_ == 0 {
                            v___x_3839_ = v_a_3835_;
                            v_isShared_3840_ = v_isSharedCheck_3851_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3837_);
                            leanh::lean_inc(v_fst_3836_);
                            leanh::lean_dec(v_a_3835_);
                            v___x_3839_ = leanh::lean_box(0);
                            v_isShared_3840_ = v_isSharedCheck_3851_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_3832_);
                        v_a_3852_ = leanh::lean_ctor_get(v___x_3834_, 0);
                        v_isSharedCheck_3859_ =
                            (!leanh::lean_is_exclusive(v___x_3834_)) as u8;
                        if v_isSharedCheck_3859_ == 0 {
                            v___x_3854_ = v___x_3834_;
                            v_isShared_3855_ = v_isSharedCheck_3859_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3852_);
                            leanh::lean_dec(v___x_3834_);
                            v___x_3854_ = leanh::lean_box(0);
                            v_isShared_3855_ = v_isSharedCheck_3859_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3841_ = leanh::lean_box(0);
                v___x_3842_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_3843_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1(v_fst_3836_, v___x_3842_);
                v___x_3844_ = lean_array_push(v_snd_3832_, v___x_3843_);
                if v_isShared_3840_ == 0 {
                    leanh::lean_ctor_set(v___x_3839_, 1, v___x_3844_);
                    leanh::lean_ctor_set(v___x_3839_, 0, v___x_3841_);
                    v___x_3846_ = v___x_3839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3850_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3850_, 1, v___x_3844_);
                    v___x_3846_ = v_reuseFailAlloc_3850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3847_ = 1usize;
                v___x_3848_ = lean_usize_add(v_i_3821_, v___x_3847_);
                v_i_3821_ = v___x_3848_;
                v_b_3822_ = v___x_3846_;
                v___y_3823_ = v_snd_3837_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3855_ == 0 {
                    v___x_3857_ = v___x_3854_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3858_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
                    v___x_3857_ = v_reuseFailAlloc_3858_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__3_spec__6___boxed(
    mut v_as_3860_: *mut leanh::LeanObject,
    mut v_sz_3861_: *mut leanh::LeanObject,
    mut v_i_3862_: *mut leanh::LeanObject,
    mut v_b_3863_: *mut leanh::LeanObject,
    mut v___y_3864_: *mut leanh::LeanObject,
    mut v___y_3865_: *mut leanh::LeanObject,
    mut v___y_3866_: *mut leanh::LeanObject,
    mut v___y_3867_: *mut leanh::LeanObject,
    mut v___y_3868_: *mut leanh::LeanObject,
    mut v___y_3869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3870_: usize = 0;
    let mut v_i_boxed_3871_: usize = 0;
    let mut v_res_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3870_ = leanh::lean_unbox_usize(v_sz_3861_);
    leanh::lean_dec(v_sz_3861_);
    v_i_boxed_3871_ = leanh::lean_unbox_usize(v_i_3862_);
    leanh::lean_dec(v_i_3862_);
    v_res_3872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__3_spec__6(v_as_3860_, v_sz_boxed_3870_, v_i_boxed_3871_, v_b_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
    leanh::lean_dec(v___y_3868_);
    leanh::lean_dec_ref(v___y_3867_);
    leanh::lean_dec(v___y_3866_);
    leanh::lean_dec_ref(v___y_3865_);
    leanh::lean_dec_ref(v_as_3860_);
    return v_res_3872_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__3(
    mut v_as_3873_: *mut leanh::LeanObject,
    mut v_sz_3874_: usize,
    mut v_i_3875_: usize,
    mut v_b_3876_: *mut leanh::LeanObject,
    mut v___y_3877_: *mut leanh::LeanObject,
    mut v___y_3878_: *mut leanh::LeanObject,
    mut v___y_3879_: *mut leanh::LeanObject,
    mut v___y_3880_: *mut leanh::LeanObject,
    mut v___y_3881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3883_: u8 = 0;
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: usize = 0;
    let mut v___x_3902_: usize = 0;
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_a_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3883_ = lean_usize_dec_lt(v_i_3875_, v_sz_3874_);
                if v___x_3883_ == 0 {
                    v___x_3884_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3884_, 0, v_b_3876_);
                    leanh::lean_ctor_set(v___x_3884_, 1, v___y_3877_);
                    v___x_3885_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3885_, 0, v___x_3884_);
                    return v___x_3885_;
                } else {
                    v_snd_3886_ = leanh::lean_ctor_get(v_b_3876_, 1);
                    leanh::lean_inc(v_snd_3886_);
                    leanh::lean_dec_ref(v_b_3876_);
                    v_a_3887_ = lean_array_uget_borrowed(v_as_3873_, v_i_3875_);
                    v___x_3888_ = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0(v_a_3887_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
                    if leanh::lean_obj_tag(v___x_3888_) == 0 {
                        v_a_3889_ = leanh::lean_ctor_get(v___x_3888_, 0);
                        leanh::lean_inc(v_a_3889_);
                        leanh::lean_dec_ref_known(v___x_3888_, 1);
                        v_fst_3890_ = leanh::lean_ctor_get(v_a_3889_, 0);
                        v_snd_3891_ = leanh::lean_ctor_get(v_a_3889_, 1);
                        v_isSharedCheck_3905_ = (!leanh::lean_is_exclusive(v_a_3889_)) as u8;
                        if v_isSharedCheck_3905_ == 0 {
                            v___x_3893_ = v_a_3889_;
                            v_isShared_3894_ = v_isSharedCheck_3905_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3891_);
                            leanh::lean_inc(v_fst_3890_);
                            leanh::lean_dec(v_a_3889_);
                            v___x_3893_ = leanh::lean_box(0);
                            v_isShared_3894_ = v_isSharedCheck_3905_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_3886_);
                        v_a_3906_ = leanh::lean_ctor_get(v___x_3888_, 0);
                        v_isSharedCheck_3913_ =
                            (!leanh::lean_is_exclusive(v___x_3888_)) as u8;
                        if v_isSharedCheck_3913_ == 0 {
                            v___x_3908_ = v___x_3888_;
                            v_isShared_3909_ = v_isSharedCheck_3913_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3906_);
                            leanh::lean_dec(v___x_3888_);
                            v___x_3908_ = leanh::lean_box(0);
                            v_isShared_3909_ = v_isSharedCheck_3913_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3895_ = leanh::lean_box(0);
                v___x_3896_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_3897_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1(v_fst_3890_, v___x_3896_);
                v___x_3898_ = lean_array_push(v_snd_3886_, v___x_3897_);
                if v_isShared_3894_ == 0 {
                    leanh::lean_ctor_set(v___x_3893_, 1, v___x_3898_);
                    leanh::lean_ctor_set(v___x_3893_, 0, v___x_3895_);
                    v___x_3900_ = v___x_3893_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___x_3898_);
                    v___x_3900_ = v_reuseFailAlloc_3904_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3901_ = 1usize;
                v___x_3902_ = lean_usize_add(v_i_3875_, v___x_3901_);
                v___x_3903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__3_spec__6(v_as_3873_, v_sz_3874_, v___x_3902_, v___x_3900_, v_snd_3891_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
                return v___x_3903_;
            }
            3 => {
                if v_isShared_3909_ == 0 {
                    v___x_3911_ = v___x_3908_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3912_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
                    v___x_3911_ = v_reuseFailAlloc_3912_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__3___boxed(
    mut v_as_3914_: *mut leanh::LeanObject,
    mut v_sz_3915_: *mut leanh::LeanObject,
    mut v_i_3916_: *mut leanh::LeanObject,
    mut v_b_3917_: *mut leanh::LeanObject,
    mut v___y_3918_: *mut leanh::LeanObject,
    mut v___y_3919_: *mut leanh::LeanObject,
    mut v___y_3920_: *mut leanh::LeanObject,
    mut v___y_3921_: *mut leanh::LeanObject,
    mut v___y_3922_: *mut leanh::LeanObject,
    mut v___y_3923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3924_: usize = 0;
    let mut v_i_boxed_3925_: usize = 0;
    let mut v_res_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3924_ = leanh::lean_unbox_usize(v_sz_3915_);
    leanh::lean_dec(v_sz_3915_);
    v_i_boxed_3925_ = leanh::lean_unbox_usize(v_i_3916_);
    leanh::lean_dec(v_i_3916_);
    v_res_3926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__3(v_as_3914_, v_sz_boxed_3924_, v_i_boxed_3925_, v_b_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
    leanh::lean_dec(v___y_3922_);
    leanh::lean_dec_ref(v___y_3921_);
    leanh::lean_dec(v___y_3920_);
    leanh::lean_dec_ref(v___y_3919_);
    leanh::lean_dec_ref(v_as_3914_);
    return v_res_3926_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__4_spec__5(
    mut v_as_3927_: *mut leanh::LeanObject,
    mut v_sz_3928_: usize,
    mut v_i_3929_: usize,
    mut v_b_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
    mut v___y_3935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3937_: u8 = 0;
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3948_: u8 = 0;
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: usize = 0;
    let mut v___x_3956_: usize = 0;
    let mut v_reuseFailAlloc_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3959_: u8 = 0;
    let mut v_a_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3963_: u8 = 0;
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3937_ = lean_usize_dec_lt(v_i_3929_, v_sz_3928_);
                if v___x_3937_ == 0 {
                    v___x_3938_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3938_, 0, v_b_3930_);
                    leanh::lean_ctor_set(v___x_3938_, 1, v___y_3931_);
                    v___x_3939_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3939_, 0, v___x_3938_);
                    return v___x_3939_;
                } else {
                    v_snd_3940_ = leanh::lean_ctor_get(v_b_3930_, 1);
                    leanh::lean_inc(v_snd_3940_);
                    leanh::lean_dec_ref(v_b_3930_);
                    v_a_3941_ = lean_array_uget_borrowed(v_as_3927_, v_i_3929_);
                    v___x_3942_ = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0(v_a_3941_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
                    if leanh::lean_obj_tag(v___x_3942_) == 0 {
                        v_a_3943_ = leanh::lean_ctor_get(v___x_3942_, 0);
                        leanh::lean_inc(v_a_3943_);
                        leanh::lean_dec_ref_known(v___x_3942_, 1);
                        v_fst_3944_ = leanh::lean_ctor_get(v_a_3943_, 0);
                        v_snd_3945_ = leanh::lean_ctor_get(v_a_3943_, 1);
                        v_isSharedCheck_3959_ = (!leanh::lean_is_exclusive(v_a_3943_)) as u8;
                        if v_isSharedCheck_3959_ == 0 {
                            v___x_3947_ = v_a_3943_;
                            v_isShared_3948_ = v_isSharedCheck_3959_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3945_);
                            leanh::lean_inc(v_fst_3944_);
                            leanh::lean_dec(v_a_3943_);
                            v___x_3947_ = leanh::lean_box(0);
                            v_isShared_3948_ = v_isSharedCheck_3959_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_3940_);
                        v_a_3960_ = leanh::lean_ctor_get(v___x_3942_, 0);
                        v_isSharedCheck_3967_ =
                            (!leanh::lean_is_exclusive(v___x_3942_)) as u8;
                        if v_isSharedCheck_3967_ == 0 {
                            v___x_3962_ = v___x_3942_;
                            v_isShared_3963_ = v_isSharedCheck_3967_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3960_);
                            leanh::lean_dec(v___x_3942_);
                            v___x_3962_ = leanh::lean_box(0);
                            v_isShared_3963_ = v_isSharedCheck_3967_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3949_ = leanh::lean_box(0);
                v___x_3950_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_3951_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1(v_fst_3944_, v___x_3950_);
                v___x_3952_ = lean_array_push(v_snd_3940_, v___x_3951_);
                if v_isShared_3948_ == 0 {
                    leanh::lean_ctor_set(v___x_3947_, 1, v___x_3952_);
                    leanh::lean_ctor_set(v___x_3947_, 0, v___x_3949_);
                    v___x_3954_ = v___x_3947_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3958_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3958_, 1, v___x_3952_);
                    v___x_3954_ = v_reuseFailAlloc_3958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3955_ = 1usize;
                v___x_3956_ = lean_usize_add(v_i_3929_, v___x_3955_);
                v_i_3929_ = v___x_3956_;
                v_b_3930_ = v___x_3954_;
                v___y_3931_ = v_snd_3945_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_3963_ == 0 {
                    v___x_3965_ = v___x_3962_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3966_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
                    v___x_3965_ = v_reuseFailAlloc_3966_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__4_spec__5___boxed(
    mut v_as_3968_: *mut leanh::LeanObject,
    mut v_sz_3969_: *mut leanh::LeanObject,
    mut v_i_3970_: *mut leanh::LeanObject,
    mut v_b_3971_: *mut leanh::LeanObject,
    mut v___y_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
    mut v___y_3974_: *mut leanh::LeanObject,
    mut v___y_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3978_: usize = 0;
    let mut v_i_boxed_3979_: usize = 0;
    let mut v_res_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3978_ = leanh::lean_unbox_usize(v_sz_3969_);
    leanh::lean_dec(v_sz_3969_);
    v_i_boxed_3979_ = leanh::lean_unbox_usize(v_i_3970_);
    leanh::lean_dec(v_i_3970_);
    v_res_3980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__4_spec__5(v_as_3968_, v_sz_boxed_3978_, v_i_boxed_3979_, v_b_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
    leanh::lean_dec(v___y_3976_);
    leanh::lean_dec_ref(v___y_3975_);
    leanh::lean_dec(v___y_3974_);
    leanh::lean_dec_ref(v___y_3973_);
    leanh::lean_dec_ref(v_as_3968_);
    return v_res_3980_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__4(
    mut v_as_3981_: *mut leanh::LeanObject,
    mut v_sz_3982_: usize,
    mut v_i_3983_: usize,
    mut v_b_3984_: *mut leanh::LeanObject,
    mut v___y_3985_: *mut leanh::LeanObject,
    mut v___y_3986_: *mut leanh::LeanObject,
    mut v___y_3987_: *mut leanh::LeanObject,
    mut v___y_3988_: *mut leanh::LeanObject,
    mut v___y_3989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3991_: u8 = 0;
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4002_: u8 = 0;
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: usize = 0;
    let mut v___x_4010_: usize = 0;
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut v_a_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4017_: u8 = 0;
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3991_ = lean_usize_dec_lt(v_i_3983_, v_sz_3982_);
                if v___x_3991_ == 0 {
                    v___x_3992_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3992_, 0, v_b_3984_);
                    leanh::lean_ctor_set(v___x_3992_, 1, v___y_3985_);
                    v___x_3993_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3993_, 0, v___x_3992_);
                    return v___x_3993_;
                } else {
                    v_snd_3994_ = leanh::lean_ctor_get(v_b_3984_, 1);
                    leanh::lean_inc(v_snd_3994_);
                    leanh::lean_dec_ref(v_b_3984_);
                    v_a_3995_ = lean_array_uget_borrowed(v_as_3981_, v_i_3983_);
                    v___x_3996_ = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__0(v_a_3995_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
                    if leanh::lean_obj_tag(v___x_3996_) == 0 {
                        v_a_3997_ = leanh::lean_ctor_get(v___x_3996_, 0);
                        leanh::lean_inc(v_a_3997_);
                        leanh::lean_dec_ref_known(v___x_3996_, 1);
                        v_fst_3998_ = leanh::lean_ctor_get(v_a_3997_, 0);
                        v_snd_3999_ = leanh::lean_ctor_get(v_a_3997_, 1);
                        v_isSharedCheck_4013_ = (!leanh::lean_is_exclusive(v_a_3997_)) as u8;
                        if v_isSharedCheck_4013_ == 0 {
                            v___x_4001_ = v_a_3997_;
                            v_isShared_4002_ = v_isSharedCheck_4013_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3999_);
                            leanh::lean_inc(v_fst_3998_);
                            leanh::lean_dec(v_a_3997_);
                            v___x_4001_ = leanh::lean_box(0);
                            v_isShared_4002_ = v_isSharedCheck_4013_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_3994_);
                        v_a_4014_ = leanh::lean_ctor_get(v___x_3996_, 0);
                        v_isSharedCheck_4021_ =
                            (!leanh::lean_is_exclusive(v___x_3996_)) as u8;
                        if v_isSharedCheck_4021_ == 0 {
                            v___x_4016_ = v___x_3996_;
                            v_isShared_4017_ = v_isSharedCheck_4021_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4014_);
                            leanh::lean_dec(v___x_3996_);
                            v___x_4016_ = leanh::lean_box(0);
                            v_isShared_4017_ = v_isSharedCheck_4021_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4003_ = leanh::lean_box(0);
                v___x_4004_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_4005_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1(v_fst_3998_, v___x_4004_);
                v___x_4006_ = lean_array_push(v_snd_3994_, v___x_4005_);
                if v_isShared_4002_ == 0 {
                    leanh::lean_ctor_set(v___x_4001_, 1, v___x_4006_);
                    leanh::lean_ctor_set(v___x_4001_, 0, v___x_4003_);
                    v___x_4008_ = v___x_4001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4012_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 1, v___x_4006_);
                    v___x_4008_ = v_reuseFailAlloc_4012_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4009_ = 1usize;
                v___x_4010_ = lean_usize_add(v_i_3983_, v___x_4009_);
                v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__4_spec__5(v_as_3981_, v_sz_3982_, v___x_4010_, v___x_4008_, v_snd_3999_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
                return v___x_4011_;
            }
            3 => {
                if v_isShared_4017_ == 0 {
                    v___x_4019_ = v___x_4016_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4020_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
                    v___x_4019_ = v_reuseFailAlloc_4020_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__4___boxed(
    mut v_as_4022_: *mut leanh::LeanObject,
    mut v_sz_4023_: *mut leanh::LeanObject,
    mut v_i_4024_: *mut leanh::LeanObject,
    mut v_b_4025_: *mut leanh::LeanObject,
    mut v___y_4026_: *mut leanh::LeanObject,
    mut v___y_4027_: *mut leanh::LeanObject,
    mut v___y_4028_: *mut leanh::LeanObject,
    mut v___y_4029_: *mut leanh::LeanObject,
    mut v___y_4030_: *mut leanh::LeanObject,
    mut v___y_4031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4032_: usize = 0;
    let mut v_i_boxed_4033_: usize = 0;
    let mut v_res_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4032_ = leanh::lean_unbox_usize(v_sz_4023_);
    leanh::lean_dec(v_sz_4023_);
    v_i_boxed_4033_ = leanh::lean_unbox_usize(v_i_4024_);
    leanh::lean_dec(v_i_4024_);
    v_res_4034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__4(v_as_4022_, v_sz_boxed_4032_, v_i_boxed_4033_, v_b_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
    leanh::lean_dec(v___y_4030_);
    leanh::lean_dec_ref(v___y_4029_);
    leanh::lean_dec(v___y_4028_);
    leanh::lean_dec_ref(v___y_4027_);
    leanh::lean_dec_ref(v_as_4022_);
    return v_res_4034_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2(
    mut v_init_4035_: *mut leanh::LeanObject,
    mut v_n_4036_: *mut leanh::LeanObject,
    mut v_b_4037_: *mut leanh::LeanObject,
    mut v___y_4038_: *mut leanh::LeanObject,
    mut v___y_4039_: *mut leanh::LeanObject,
    mut v___y_4040_: *mut leanh::LeanObject,
    mut v___y_4041_: *mut leanh::LeanObject,
    mut v___y_4042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4047_: usize = 0;
    let mut v___x_4048_: usize = 0;
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4053_: u8 = 0;
    let mut v_fst_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut v_unused_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4072_: u8 = 0;
    let mut v_snd_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4081_: u8 = 0;
    let mut v_unused_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4084_: u8 = 0;
    let mut v_a_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4088_: u8 = 0;
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v_vs_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4096_: usize = 0;
    let mut v___x_4097_: usize = 0;
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4102_: u8 = 0;
    let mut v_fst_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4109_: u8 = 0;
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4117_: u8 = 0;
    let mut v_unused_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v_snd_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4130_: u8 = 0;
    let mut v_unused_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4133_: u8 = 0;
    let mut v_a_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4137_: u8 = 0;
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_4036_) == 0 {
                    v_cs_4044_ = leanh::lean_ctor_get(v_n_4036_, 0);
                    v___x_4045_ = leanh::lean_box(0);
                    v___x_4046_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4046_, 0, v___x_4045_);
                    leanh::lean_ctor_set(v___x_4046_, 1, v_b_4037_);
                    v_sz_4047_ = lean_array_size(v_cs_4044_);
                    v___x_4048_ = 0usize;
                    v___x_4049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__3(v_init_4035_, v_cs_4044_, v_sz_4047_, v___x_4048_, v___x_4046_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
                    if leanh::lean_obj_tag(v___x_4049_) == 0 {
                        v_a_4050_ = leanh::lean_ctor_get(v___x_4049_, 0);
                        v_isSharedCheck_4084_ =
                            (!leanh::lean_is_exclusive(v___x_4049_)) as u8;
                        if v_isSharedCheck_4084_ == 0 {
                            v___x_4052_ = v___x_4049_;
                            v_isShared_4053_ = v_isSharedCheck_4084_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4050_);
                            leanh::lean_dec(v___x_4049_);
                            v___x_4052_ = leanh::lean_box(0);
                            v_isShared_4053_ = v_isSharedCheck_4084_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4085_ = leanh::lean_ctor_get(v___x_4049_, 0);
                        v_isSharedCheck_4092_ =
                            (!leanh::lean_is_exclusive(v___x_4049_)) as u8;
                        if v_isSharedCheck_4092_ == 0 {
                            v___x_4087_ = v___x_4049_;
                            v_isShared_4088_ = v_isSharedCheck_4092_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4085_);
                            leanh::lean_dec(v___x_4049_);
                            v___x_4087_ = leanh::lean_box(0);
                            v_isShared_4088_ = v_isSharedCheck_4092_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_vs_4093_ = leanh::lean_ctor_get(v_n_4036_, 0);
                    v___x_4094_ = leanh::lean_box(0);
                    v___x_4095_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4095_, 0, v___x_4094_);
                    leanh::lean_ctor_set(v___x_4095_, 1, v_b_4037_);
                    v_sz_4096_ = lean_array_size(v_vs_4093_);
                    v___x_4097_ = 0usize;
                    v___x_4098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__4(v_vs_4093_, v_sz_4096_, v___x_4097_, v___x_4095_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
                    if leanh::lean_obj_tag(v___x_4098_) == 0 {
                        v_a_4099_ = leanh::lean_ctor_get(v___x_4098_, 0);
                        v_isSharedCheck_4133_ =
                            (!leanh::lean_is_exclusive(v___x_4098_)) as u8;
                        if v_isSharedCheck_4133_ == 0 {
                            v___x_4101_ = v___x_4098_;
                            v_isShared_4102_ = v_isSharedCheck_4133_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4099_);
                            leanh::lean_dec(v___x_4098_);
                            v___x_4101_ = leanh::lean_box(0);
                            v_isShared_4102_ = v_isSharedCheck_4133_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_a_4134_ = leanh::lean_ctor_get(v___x_4098_, 0);
                        v_isSharedCheck_4141_ =
                            (!leanh::lean_is_exclusive(v___x_4098_)) as u8;
                        if v_isSharedCheck_4141_ == 0 {
                            v___x_4136_ = v___x_4098_;
                            v_isShared_4137_ = v_isSharedCheck_4141_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4134_);
                            leanh::lean_dec(v___x_4098_);
                            v___x_4136_ = leanh::lean_box(0);
                            v_isShared_4137_ = v_isSharedCheck_4141_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4054_ = leanh::lean_ctor_get(v_a_4050_, 0);
                leanh::lean_inc(v_fst_4054_);
                v_fst_4055_ = leanh::lean_ctor_get(v_fst_4054_, 0);
                if leanh::lean_obj_tag(v_fst_4055_) == 0 {
                    v_snd_4056_ = leanh::lean_ctor_get(v_a_4050_, 1);
                    leanh::lean_inc(v_snd_4056_);
                    leanh::lean_dec(v_a_4050_);
                    v_snd_4057_ = leanh::lean_ctor_get(v_fst_4054_, 1);
                    v_isSharedCheck_4068_ = (!leanh::lean_is_exclusive(v_fst_4054_)) as u8;
                    if v_isSharedCheck_4068_ == 0 {
                        v_unused_4069_ = leanh::lean_ctor_get(v_fst_4054_, 0);
                        leanh::lean_dec(v_unused_4069_);
                        v___x_4059_ = v_fst_4054_;
                        v_isShared_4060_ = v_isSharedCheck_4068_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4057_);
                        leanh::lean_dec(v_fst_4054_);
                        v___x_4059_ = leanh::lean_box(0);
                        v_isShared_4060_ = v_isSharedCheck_4068_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4055_);
                    v_isSharedCheck_4081_ = (!leanh::lean_is_exclusive(v_fst_4054_)) as u8;
                    if v_isSharedCheck_4081_ == 0 {
                        v_unused_4082_ = leanh::lean_ctor_get(v_fst_4054_, 1);
                        leanh::lean_dec(v_unused_4082_);
                        v_unused_4083_ = leanh::lean_ctor_get(v_fst_4054_, 0);
                        leanh::lean_dec(v_unused_4083_);
                        v___x_4071_ = v_fst_4054_;
                        v_isShared_4072_ = v_isSharedCheck_4081_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_4054_);
                        v___x_4071_ = leanh::lean_box(0);
                        v_isShared_4072_ = v_isSharedCheck_4081_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4061_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4061_, 0, v_snd_4057_);
                if v_isShared_4060_ == 0 {
                    leanh::lean_ctor_set(v___x_4059_, 1, v_snd_4056_);
                    leanh::lean_ctor_set(v___x_4059_, 0, v___x_4061_);
                    v___x_4063_ = v___x_4059_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4067_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4061_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4067_, 1, v_snd_4056_);
                    v___x_4063_ = v_reuseFailAlloc_4067_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4053_ == 0 {
                    leanh::lean_ctor_set(v___x_4052_, 0, v___x_4063_);
                    v___x_4065_ = v___x_4052_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4063_);
                    v___x_4065_ = v_reuseFailAlloc_4066_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4065_;
            }
            5 => {
                v_snd_4073_ = leanh::lean_ctor_get(v_a_4050_, 1);
                leanh::lean_inc(v_snd_4073_);
                leanh::lean_dec(v_a_4050_);
                v_val_4074_ = leanh::lean_ctor_get(v_fst_4055_, 0);
                leanh::lean_inc(v_val_4074_);
                leanh::lean_dec_ref_known(v_fst_4055_, 1);
                if v_isShared_4072_ == 0 {
                    leanh::lean_ctor_set(v___x_4071_, 1, v_snd_4073_);
                    leanh::lean_ctor_set(v___x_4071_, 0, v_val_4074_);
                    v___x_4076_ = v___x_4071_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4080_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_val_4074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4080_, 1, v_snd_4073_);
                    v___x_4076_ = v_reuseFailAlloc_4080_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4053_ == 0 {
                    leanh::lean_ctor_set(v___x_4052_, 0, v___x_4076_);
                    v___x_4078_ = v___x_4052_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4079_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4076_);
                    v___x_4078_ = v_reuseFailAlloc_4079_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4078_;
            }
            8 => {
                if v_isShared_4088_ == 0 {
                    v___x_4090_ = v___x_4087_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
                    v___x_4090_ = v_reuseFailAlloc_4091_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4090_;
            }
            10 => {
                v_fst_4103_ = leanh::lean_ctor_get(v_a_4099_, 0);
                leanh::lean_inc(v_fst_4103_);
                v_fst_4104_ = leanh::lean_ctor_get(v_fst_4103_, 0);
                if leanh::lean_obj_tag(v_fst_4104_) == 0 {
                    v_snd_4105_ = leanh::lean_ctor_get(v_a_4099_, 1);
                    leanh::lean_inc(v_snd_4105_);
                    leanh::lean_dec(v_a_4099_);
                    v_snd_4106_ = leanh::lean_ctor_get(v_fst_4103_, 1);
                    v_isSharedCheck_4117_ = (!leanh::lean_is_exclusive(v_fst_4103_)) as u8;
                    if v_isSharedCheck_4117_ == 0 {
                        v_unused_4118_ = leanh::lean_ctor_get(v_fst_4103_, 0);
                        leanh::lean_dec(v_unused_4118_);
                        v___x_4108_ = v_fst_4103_;
                        v_isShared_4109_ = v_isSharedCheck_4117_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4106_);
                        leanh::lean_dec(v_fst_4103_);
                        v___x_4108_ = leanh::lean_box(0);
                        v_isShared_4109_ = v_isSharedCheck_4117_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4104_);
                    v_isSharedCheck_4130_ = (!leanh::lean_is_exclusive(v_fst_4103_)) as u8;
                    if v_isSharedCheck_4130_ == 0 {
                        v_unused_4131_ = leanh::lean_ctor_get(v_fst_4103_, 1);
                        leanh::lean_dec(v_unused_4131_);
                        v_unused_4132_ = leanh::lean_ctor_get(v_fst_4103_, 0);
                        leanh::lean_dec(v_unused_4132_);
                        v___x_4120_ = v_fst_4103_;
                        v_isShared_4121_ = v_isSharedCheck_4130_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_4103_);
                        v___x_4120_ = leanh::lean_box(0);
                        v_isShared_4121_ = v_isSharedCheck_4130_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v___x_4110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4110_, 0, v_snd_4106_);
                if v_isShared_4109_ == 0 {
                    leanh::lean_ctor_set(v___x_4108_, 1, v_snd_4105_);
                    leanh::lean_ctor_set(v___x_4108_, 0, v___x_4110_);
                    v___x_4112_ = v___x_4108_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4116_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 0, v___x_4110_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4116_, 1, v_snd_4105_);
                    v___x_4112_ = v_reuseFailAlloc_4116_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4102_ == 0 {
                    leanh::lean_ctor_set(v___x_4101_, 0, v___x_4112_);
                    v___x_4114_ = v___x_4101_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4115_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4112_);
                    v___x_4114_ = v_reuseFailAlloc_4115_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4114_;
            }
            14 => {
                v_snd_4122_ = leanh::lean_ctor_get(v_a_4099_, 1);
                leanh::lean_inc(v_snd_4122_);
                leanh::lean_dec(v_a_4099_);
                v_val_4123_ = leanh::lean_ctor_get(v_fst_4104_, 0);
                leanh::lean_inc(v_val_4123_);
                leanh::lean_dec_ref_known(v_fst_4104_, 1);
                if v_isShared_4121_ == 0 {
                    leanh::lean_ctor_set(v___x_4120_, 1, v_snd_4122_);
                    leanh::lean_ctor_set(v___x_4120_, 0, v_val_4123_);
                    v___x_4125_ = v___x_4120_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4129_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_val_4123_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4129_, 1, v_snd_4122_);
                    v___x_4125_ = v_reuseFailAlloc_4129_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_4102_ == 0 {
                    leanh::lean_ctor_set(v___x_4101_, 0, v___x_4125_);
                    v___x_4127_ = v___x_4101_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 0, v___x_4125_);
                    v___x_4127_ = v_reuseFailAlloc_4128_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4127_;
            }
            17 => {
                if v_isShared_4137_ == 0 {
                    v___x_4139_ = v___x_4136_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
                    v___x_4139_ = v_reuseFailAlloc_4140_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__3(
    mut v_init_4142_: *mut leanh::LeanObject,
    mut v_as_4143_: *mut leanh::LeanObject,
    mut v_sz_4144_: usize,
    mut v_i_4145_: usize,
    mut v_b_4146_: *mut leanh::LeanObject,
    mut v___y_4147_: *mut leanh::LeanObject,
    mut v___y_4148_: *mut leanh::LeanObject,
    mut v___y_4149_: *mut leanh::LeanObject,
    mut v___y_4150_: *mut leanh::LeanObject,
    mut v___y_4151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4153_: u8 = 0;
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4159_: u8 = 0;
    let mut v_a_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4165_: u8 = 0;
    let mut v_fst_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4170_: u8 = 0;
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut v_unused_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v_a_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: usize = 0;
    let mut v___x_4192_: usize = 0;
    let mut v_reuseFailAlloc_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4195_: u8 = 0;
    let mut v_unused_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4197_: u8 = 0;
    let mut v_a_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4201_: u8 = 0;
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4205_: u8 = 0;
    let mut v_isSharedCheck_4206_: u8 = 0;
    let mut v_unused_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4153_ = lean_usize_dec_lt(v_i_4145_, v_sz_4144_);
                if v___x_4153_ == 0 {
                    v___x_4154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4154_, 0, v_b_4146_);
                    leanh::lean_ctor_set(v___x_4154_, 1, v___y_4147_);
                    v___x_4155_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4155_, 0, v___x_4154_);
                    return v___x_4155_;
                } else {
                    v_snd_4156_ = leanh::lean_ctor_get(v_b_4146_, 1);
                    v_isSharedCheck_4206_ = (!leanh::lean_is_exclusive(v_b_4146_)) as u8;
                    if v_isSharedCheck_4206_ == 0 {
                        v_unused_4207_ = leanh::lean_ctor_get(v_b_4146_, 0);
                        leanh::lean_dec(v_unused_4207_);
                        v___x_4158_ = v_b_4146_;
                        v_isShared_4159_ = v_isSharedCheck_4206_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4156_);
                        leanh::lean_dec(v_b_4146_);
                        v___x_4158_ = leanh::lean_box(0);
                        v_isShared_4159_ = v_isSharedCheck_4206_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4160_ = lean_array_uget_borrowed(v_as_4143_, v_i_4145_);
                leanh::lean_inc(v_snd_4156_);
                v___x_4161_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2(v_init_4142_, v_a_4160_, v_snd_4156_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
                if leanh::lean_obj_tag(v___x_4161_) == 0 {
                    v_a_4162_ = leanh::lean_ctor_get(v___x_4161_, 0);
                    v_isSharedCheck_4197_ = (!leanh::lean_is_exclusive(v___x_4161_)) as u8;
                    if v_isSharedCheck_4197_ == 0 {
                        v___x_4164_ = v___x_4161_;
                        v_isShared_4165_ = v_isSharedCheck_4197_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4162_);
                        leanh::lean_dec(v___x_4161_);
                        v___x_4164_ = leanh::lean_box(0);
                        v_isShared_4165_ = v_isSharedCheck_4197_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4158_);
                    leanh::lean_dec(v_snd_4156_);
                    v_a_4198_ = leanh::lean_ctor_get(v___x_4161_, 0);
                    v_isSharedCheck_4205_ = (!leanh::lean_is_exclusive(v___x_4161_)) as u8;
                    if v_isSharedCheck_4205_ == 0 {
                        v___x_4200_ = v___x_4161_;
                        v_isShared_4201_ = v_isSharedCheck_4205_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4198_);
                        leanh::lean_dec(v___x_4161_);
                        v___x_4200_ = leanh::lean_box(0);
                        v_isShared_4201_ = v_isSharedCheck_4205_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_4166_ = leanh::lean_ctor_get(v_a_4162_, 0);
                leanh::lean_inc(v_fst_4166_);
                if leanh::lean_obj_tag(v_fst_4166_) == 0 {
                    v_snd_4167_ = leanh::lean_ctor_get(v_a_4162_, 1);
                    v_isSharedCheck_4181_ = (!leanh::lean_is_exclusive(v_a_4162_)) as u8;
                    if v_isSharedCheck_4181_ == 0 {
                        v_unused_4182_ = leanh::lean_ctor_get(v_a_4162_, 0);
                        leanh::lean_dec(v_unused_4182_);
                        v___x_4169_ = v_a_4162_;
                        v_isShared_4170_ = v_isSharedCheck_4181_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4167_);
                        leanh::lean_dec(v_a_4162_);
                        v___x_4169_ = leanh::lean_box(0);
                        v_isShared_4170_ = v_isSharedCheck_4181_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4164_);
                    leanh::lean_del_object(v___x_4158_);
                    leanh::lean_dec(v_snd_4156_);
                    v_snd_4183_ = leanh::lean_ctor_get(v_a_4162_, 1);
                    v_isSharedCheck_4195_ = (!leanh::lean_is_exclusive(v_a_4162_)) as u8;
                    if v_isSharedCheck_4195_ == 0 {
                        v_unused_4196_ = leanh::lean_ctor_get(v_a_4162_, 0);
                        leanh::lean_dec(v_unused_4196_);
                        v___x_4185_ = v_a_4162_;
                        v_isShared_4186_ = v_isSharedCheck_4195_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4183_);
                        leanh::lean_dec(v_a_4162_);
                        v___x_4185_ = leanh::lean_box(0);
                        v_isShared_4186_ = v_isSharedCheck_4195_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4171_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4171_, 0, v_fst_4166_);
                if v_isShared_4170_ == 0 {
                    leanh::lean_ctor_set(v___x_4169_, 1, v_snd_4156_);
                    leanh::lean_ctor_set(v___x_4169_, 0, v___x_4171_);
                    v___x_4173_ = v___x_4169_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4180_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4180_, 1, v_snd_4156_);
                    v___x_4173_ = v_reuseFailAlloc_4180_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4159_ == 0 {
                    leanh::lean_ctor_set(v___x_4158_, 1, v_snd_4167_);
                    leanh::lean_ctor_set(v___x_4158_, 0, v___x_4173_);
                    v___x_4175_ = v___x_4158_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4179_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4179_, 0, v___x_4173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4179_, 1, v_snd_4167_);
                    v___x_4175_ = v_reuseFailAlloc_4179_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4165_ == 0 {
                    leanh::lean_ctor_set(v___x_4164_, 0, v___x_4175_);
                    v___x_4177_ = v___x_4164_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4178_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4175_);
                    v___x_4177_ = v_reuseFailAlloc_4178_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4177_;
            }
            7 => {
                v_a_4187_ = leanh::lean_ctor_get(v_fst_4166_, 0);
                leanh::lean_inc(v_a_4187_);
                leanh::lean_dec_ref_known(v_fst_4166_, 1);
                v___x_4188_ = leanh::lean_box(0);
                if v_isShared_4186_ == 0 {
                    leanh::lean_ctor_set(v___x_4185_, 1, v_a_4187_);
                    leanh::lean_ctor_set(v___x_4185_, 0, v___x_4188_);
                    v___x_4190_ = v___x_4185_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4194_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4194_, 0, v___x_4188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_a_4187_);
                    v___x_4190_ = v_reuseFailAlloc_4194_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4191_ = 1usize;
                v___x_4192_ = lean_usize_add(v_i_4145_, v___x_4191_);
                v_i_4145_ = v___x_4192_;
                v_b_4146_ = v___x_4190_;
                v___y_4147_ = v_snd_4183_;
                state = 0;
                continue;
            }
            9 => {
                if v_isShared_4201_ == 0 {
                    v___x_4203_ = v___x_4200_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4204_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
                    v___x_4203_ = v_reuseFailAlloc_4204_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4203_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__3___boxed(
    mut v_init_4208_: *mut leanh::LeanObject,
    mut v_as_4209_: *mut leanh::LeanObject,
    mut v_sz_4210_: *mut leanh::LeanObject,
    mut v_i_4211_: *mut leanh::LeanObject,
    mut v_b_4212_: *mut leanh::LeanObject,
    mut v___y_4213_: *mut leanh::LeanObject,
    mut v___y_4214_: *mut leanh::LeanObject,
    mut v___y_4215_: *mut leanh::LeanObject,
    mut v___y_4216_: *mut leanh::LeanObject,
    mut v___y_4217_: *mut leanh::LeanObject,
    mut v___y_4218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4219_: usize = 0;
    let mut v_i_boxed_4220_: usize = 0;
    let mut v_res_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4219_ = leanh::lean_unbox_usize(v_sz_4210_);
    leanh::lean_dec(v_sz_4210_);
    v_i_boxed_4220_ = leanh::lean_unbox_usize(v_i_4211_);
    leanh::lean_dec(v_i_4211_);
    v_res_4221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2_spec__3(v_init_4208_, v_as_4209_, v_sz_boxed_4219_, v_i_boxed_4220_, v_b_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
    leanh::lean_dec(v___y_4217_);
    leanh::lean_dec_ref(v___y_4216_);
    leanh::lean_dec(v___y_4215_);
    leanh::lean_dec_ref(v___y_4214_);
    leanh::lean_dec_ref(v_as_4209_);
    leanh::lean_dec_ref(v_init_4208_);
    return v_res_4221_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2___boxed(
    mut v_init_4222_: *mut leanh::LeanObject,
    mut v_n_4223_: *mut leanh::LeanObject,
    mut v_b_4224_: *mut leanh::LeanObject,
    mut v___y_4225_: *mut leanh::LeanObject,
    mut v___y_4226_: *mut leanh::LeanObject,
    mut v___y_4227_: *mut leanh::LeanObject,
    mut v___y_4228_: *mut leanh::LeanObject,
    mut v___y_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4231_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2(v_init_4222_, v_n_4223_, v_b_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
    leanh::lean_dec(v___y_4229_);
    leanh::lean_dec_ref(v___y_4228_);
    leanh::lean_dec(v___y_4227_);
    leanh::lean_dec_ref(v___y_4226_);
    leanh::lean_dec_ref(v_n_4223_);
    leanh::lean_dec_ref(v_init_4222_);
    return v_res_4231_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1(
    mut v_t_4232_: *mut leanh::LeanObject,
    mut v_init_4233_: *mut leanh::LeanObject,
    mut v___y_4234_: *mut leanh::LeanObject,
    mut v___y_4235_: *mut leanh::LeanObject,
    mut v___y_4236_: *mut leanh::LeanObject,
    mut v___y_4237_: *mut leanh::LeanObject,
    mut v___y_4238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v_a_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4260_: usize = 0;
    let mut v___x_4261_: usize = 0;
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v_fst_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4273_: u8 = 0;
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4280_: u8 = 0;
    let mut v_unused_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4284_: u8 = 0;
    let mut v_a_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4292_: u8 = 0;
    let mut v_reuseFailAlloc_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4294_: u8 = 0;
    let mut v_unused_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4299_: u8 = 0;
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4245_ = leanh::lean_ctor_get(v_t_4232_, 0);
                v_tail_4246_ = leanh::lean_ctor_get(v_t_4232_, 1);
                leanh::lean_inc_ref(v_init_4233_);
                v___x_4247_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__2(v_init_4233_, v_root_4245_, v_init_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
                leanh::lean_dec_ref(v_init_4233_);
                if leanh::lean_obj_tag(v___x_4247_) == 0 {
                    v_a_4248_ = leanh::lean_ctor_get(v___x_4247_, 0);
                    leanh::lean_inc(v_a_4248_);
                    leanh::lean_dec_ref_known(v___x_4247_, 1);
                    v_fst_4249_ = leanh::lean_ctor_get(v_a_4248_, 0);
                    leanh::lean_inc(v_fst_4249_);
                    if leanh::lean_obj_tag(v_fst_4249_) == 0 {
                        v_snd_4250_ = leanh::lean_ctor_get(v_a_4248_, 1);
                        leanh::lean_inc(v_snd_4250_);
                        leanh::lean_dec(v_a_4248_);
                        v_a_4251_ = leanh::lean_ctor_get(v_fst_4249_, 0);
                        leanh::lean_inc(v_a_4251_);
                        leanh::lean_dec_ref_known(v_fst_4249_, 1);
                        v_b_4241_ = v_a_4251_;
                        v___y_4242_ = v_snd_4250_;
                        state = 1;
                        continue;
                    } else {
                        v_snd_4252_ = leanh::lean_ctor_get(v_a_4248_, 1);
                        v_isSharedCheck_4294_ = (!leanh::lean_is_exclusive(v_a_4248_)) as u8;
                        if v_isSharedCheck_4294_ == 0 {
                            v_unused_4295_ = leanh::lean_ctor_get(v_a_4248_, 0);
                            leanh::lean_dec(v_unused_4295_);
                            v___x_4254_ = v_a_4248_;
                            v_isShared_4255_ = v_isSharedCheck_4294_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_4252_);
                            leanh::lean_dec(v_a_4248_);
                            v___x_4254_ = leanh::lean_box(0);
                            v_isShared_4255_ = v_isSharedCheck_4294_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_a_4296_ = leanh::lean_ctor_get(v___x_4247_, 0);
                    v_isSharedCheck_4303_ = (!leanh::lean_is_exclusive(v___x_4247_)) as u8;
                    if v_isSharedCheck_4303_ == 0 {
                        v___x_4298_ = v___x_4247_;
                        v_isShared_4299_ = v_isSharedCheck_4303_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4296_);
                        leanh::lean_dec(v___x_4247_);
                        v___x_4298_ = leanh::lean_box(0);
                        v_isShared_4299_ = v_isSharedCheck_4303_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4243_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4243_, 0, v_b_4241_);
                leanh::lean_ctor_set(v___x_4243_, 1, v___y_4242_);
                v___x_4244_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4244_, 0, v___x_4243_);
                return v___x_4244_;
            }
            2 => {
                v_a_4256_ = leanh::lean_ctor_get(v_fst_4249_, 0);
                leanh::lean_inc(v_a_4256_);
                leanh::lean_dec_ref_known(v_fst_4249_, 1);
                v___x_4257_ = leanh::lean_box(0);
                if v_isShared_4255_ == 0 {
                    leanh::lean_ctor_set(v___x_4254_, 1, v_a_4256_);
                    leanh::lean_ctor_set(v___x_4254_, 0, v___x_4257_);
                    v___x_4259_ = v___x_4254_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4293_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4257_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4293_, 1, v_a_4256_);
                    v___x_4259_ = v_reuseFailAlloc_4293_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_sz_4260_ = lean_array_size(v_tail_4246_);
                v___x_4261_ = 0usize;
                v___x_4262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1_spec__3(v_tail_4246_, v_sz_4260_, v___x_4261_, v___x_4259_, v_snd_4252_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
                if leanh::lean_obj_tag(v___x_4262_) == 0 {
                    v_a_4263_ = leanh::lean_ctor_get(v___x_4262_, 0);
                    v_isSharedCheck_4284_ = (!leanh::lean_is_exclusive(v___x_4262_)) as u8;
                    if v_isSharedCheck_4284_ == 0 {
                        v___x_4265_ = v___x_4262_;
                        v_isShared_4266_ = v_isSharedCheck_4284_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4263_);
                        leanh::lean_dec(v___x_4262_);
                        v___x_4265_ = leanh::lean_box(0);
                        v_isShared_4266_ = v_isSharedCheck_4284_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4285_ = leanh::lean_ctor_get(v___x_4262_, 0);
                    v_isSharedCheck_4292_ = (!leanh::lean_is_exclusive(v___x_4262_)) as u8;
                    if v_isSharedCheck_4292_ == 0 {
                        v___x_4287_ = v___x_4262_;
                        v_isShared_4288_ = v_isSharedCheck_4292_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4285_);
                        leanh::lean_dec(v___x_4262_);
                        v___x_4287_ = leanh::lean_box(0);
                        v_isShared_4288_ = v_isSharedCheck_4292_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_4267_ = leanh::lean_ctor_get(v_a_4263_, 0);
                leanh::lean_inc(v_fst_4267_);
                v_fst_4268_ = leanh::lean_ctor_get(v_fst_4267_, 0);
                if leanh::lean_obj_tag(v_fst_4268_) == 0 {
                    v_snd_4269_ = leanh::lean_ctor_get(v_a_4263_, 1);
                    leanh::lean_inc(v_snd_4269_);
                    leanh::lean_dec(v_a_4263_);
                    v_snd_4270_ = leanh::lean_ctor_get(v_fst_4267_, 1);
                    v_isSharedCheck_4280_ = (!leanh::lean_is_exclusive(v_fst_4267_)) as u8;
                    if v_isSharedCheck_4280_ == 0 {
                        v_unused_4281_ = leanh::lean_ctor_get(v_fst_4267_, 0);
                        leanh::lean_dec(v_unused_4281_);
                        v___x_4272_ = v_fst_4267_;
                        v_isShared_4273_ = v_isSharedCheck_4280_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4270_);
                        leanh::lean_dec(v_fst_4267_);
                        v___x_4272_ = leanh::lean_box(0);
                        v_isShared_4273_ = v_isSharedCheck_4280_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4268_);
                    leanh::lean_dec(v_fst_4267_);
                    leanh::lean_del_object(v___x_4265_);
                    v_snd_4282_ = leanh::lean_ctor_get(v_a_4263_, 1);
                    leanh::lean_inc(v_snd_4282_);
                    leanh::lean_dec(v_a_4263_);
                    v_val_4283_ = leanh::lean_ctor_get(v_fst_4268_, 0);
                    leanh::lean_inc(v_val_4283_);
                    leanh::lean_dec_ref_known(v_fst_4268_, 1);
                    v_b_4241_ = v_val_4283_;
                    v___y_4242_ = v_snd_4282_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_4273_ == 0 {
                    leanh::lean_ctor_set(v___x_4272_, 1, v_snd_4269_);
                    leanh::lean_ctor_set(v___x_4272_, 0, v_snd_4270_);
                    v___x_4275_ = v___x_4272_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4279_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_snd_4270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4279_, 1, v_snd_4269_);
                    v___x_4275_ = v_reuseFailAlloc_4279_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4266_ == 0 {
                    leanh::lean_ctor_set(v___x_4265_, 0, v___x_4275_);
                    v___x_4277_ = v___x_4265_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4278_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
                    v___x_4277_ = v_reuseFailAlloc_4278_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4277_;
            }
            8 => {
                if v_isShared_4288_ == 0 {
                    v___x_4290_ = v___x_4287_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4291_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
                    v___x_4290_ = v_reuseFailAlloc_4291_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4290_;
            }
            10 => {
                if v_isShared_4299_ == 0 {
                    v___x_4301_ = v___x_4298_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4296_);
                    v___x_4301_ = v_reuseFailAlloc_4302_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4301_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1___boxed(
    mut v_t_4304_: *mut leanh::LeanObject,
    mut v_init_4305_: *mut leanh::LeanObject,
    mut v___y_4306_: *mut leanh::LeanObject,
    mut v___y_4307_: *mut leanh::LeanObject,
    mut v___y_4308_: *mut leanh::LeanObject,
    mut v___y_4309_: *mut leanh::LeanObject,
    mut v___y_4310_: *mut leanh::LeanObject,
    mut v___y_4311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4312_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1(v_t_4304_, v_init_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
    leanh::lean_dec(v___y_4310_);
    leanh::lean_dec_ref(v___y_4309_);
    leanh::lean_dec(v___y_4308_);
    leanh::lean_dec_ref(v___y_4307_);
    leanh::lean_dec_ref(v_t_4304_);
    return v_res_4312_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__3()
-> *mut leanh::LeanObject {
    let mut v___f_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4317_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__0;
    v___x_4318_ = lean_mk_thunk(v___f_4317_);
    return v___x_4318_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f(
    mut v_a_4319_: *mut leanh::LeanObject,
    mut v_a_4320_: *mut leanh::LeanObject,
    mut v_a_4321_: *mut leanh::LeanObject,
    mut v_a_4322_: *mut leanh::LeanObject,
    mut v_a_4323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_diseqs_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4331_: u8 = 0;
    let mut v_fst_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4336_: u8 = 0;
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_isSharedCheck_4347_: u8 = 0;
    let mut v_a_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4351_: u8 = 0;
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4355_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_diseqs_4325_ = leanh::lean_ctor_get(v_a_4319_, 13);
                leanh::lean_inc_ref(v_diseqs_4325_);
                v_diseqs_4326_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1___closed__0;
                v___x_4327_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f_spec__1(v_diseqs_4325_, v_diseqs_4326_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
                leanh::lean_dec_ref(v_diseqs_4325_);
                if leanh::lean_obj_tag(v___x_4327_) == 0 {
                    v_a_4328_ = leanh::lean_ctor_get(v___x_4327_, 0);
                    v_isSharedCheck_4347_ = (!leanh::lean_is_exclusive(v___x_4327_)) as u8;
                    if v_isSharedCheck_4347_ == 0 {
                        v___x_4330_ = v___x_4327_;
                        v_isShared_4331_ = v_isSharedCheck_4347_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4328_);
                        leanh::lean_dec(v___x_4327_);
                        v___x_4330_ = leanh::lean_box(0);
                        v_isShared_4331_ = v_isSharedCheck_4347_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4348_ = leanh::lean_ctor_get(v___x_4327_, 0);
                    v_isSharedCheck_4355_ = (!leanh::lean_is_exclusive(v___x_4327_)) as u8;
                    if v_isSharedCheck_4355_ == 0 {
                        v___x_4350_ = v___x_4327_;
                        v_isShared_4351_ = v_isSharedCheck_4355_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4348_);
                        leanh::lean_dec(v___x_4327_);
                        v___x_4350_ = leanh::lean_box(0);
                        v_isShared_4351_ = v_isSharedCheck_4355_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4332_ = leanh::lean_ctor_get(v_a_4328_, 0);
                v_snd_4333_ = leanh::lean_ctor_get(v_a_4328_, 1);
                v_isSharedCheck_4346_ = (!leanh::lean_is_exclusive(v_a_4328_)) as u8;
                if v_isSharedCheck_4346_ == 0 {
                    v___x_4335_ = v_a_4328_;
                    v_isShared_4336_ = v_isSharedCheck_4346_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4333_);
                    leanh::lean_inc(v_fst_4332_);
                    leanh::lean_dec(v_a_4328_);
                    v___x_4335_ = leanh::lean_box(0);
                    v_isShared_4336_ = v_isSharedCheck_4346_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4337_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__2;
                v___x_4338_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___closed__3);
                v___x_4339_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption(v___x_4337_, v___x_4338_, v_fst_4332_);
                if v_isShared_4336_ == 0 {
                    leanh::lean_ctor_set(v___x_4335_, 0, v___x_4339_);
                    v___x_4341_ = v___x_4335_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4345_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4345_, 0, v___x_4339_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4345_, 1, v_snd_4333_);
                    v___x_4341_ = v_reuseFailAlloc_4345_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4331_ == 0 {
                    leanh::lean_ctor_set(v___x_4330_, 0, v___x_4341_);
                    v___x_4343_ = v___x_4330_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4344_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4341_);
                    v___x_4343_ = v_reuseFailAlloc_4344_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4343_;
            }
            5 => {
                if v_isShared_4351_ == 0 {
                    v___x_4353_ = v___x_4350_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
                    v___x_4353_ = v_reuseFailAlloc_4354_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4353_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f___boxed(
    mut v_a_4356_: *mut leanh::LeanObject,
    mut v_a_4357_: *mut leanh::LeanObject,
    mut v_a_4358_: *mut leanh::LeanObject,
    mut v_a_4359_: *mut leanh::LeanObject,
    mut v_a_4360_: *mut leanh::LeanObject,
    mut v_a_4361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4362_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f(v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
    leanh::lean_dec(v_a_4360_);
    leanh::lean_dec_ref(v_a_4359_);
    leanh::lean_dec(v_a_4358_);
    leanh::lean_dec_ref(v_a_4357_);
    return v_res_4362_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4364_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__0;
    v___x_4365_ = l_Lean_stringToMessageData(v___x_4364_);
    return v___x_4365_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4367_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__2;
    v___x_4368_ = l_Lean_stringToMessageData(v___x_4367_);
    return v___x_4368_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0(
    mut v_toRing_4369_: *mut leanh::LeanObject,
    mut v_x_4370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_type_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_type_4371_ = leanh::lean_ctor_get(v_toRing_4369_, 1);
    leanh::lean_inc_ref(v_type_4371_);
    leanh::lean_dec_ref(v_toRing_4369_);
    v___x_4372_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__1);
    v___x_4373_ = l_Lean_MessageData_ofExpr(v_type_4371_);
    v___x_4374_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4374_, 0, v___x_4372_);
    leanh::lean_ctor_set(v___x_4374_, 1, v___x_4373_);
    v___x_4375_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0___closed__3);
    v___x_4376_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4376_, 0, v___x_4374_);
    leanh::lean_ctor_set(v___x_4376_, 1, v___x_4375_);
    return v___x_4376_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f(
    mut v_a_4380_: *mut leanh::LeanObject,
    mut v_a_4381_: *mut leanh::LeanObject,
    mut v_a_4382_: *mut leanh::LeanObject,
    mut v_a_4383_: *mut leanh::LeanObject,
    mut v_a_4384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4394_: u8 = 0;
    let mut v_snd_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4399_: u8 = 0;
    let mut v_toRing_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v_isSharedCheck_4415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4386_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f(v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
                if leanh::lean_obj_tag(v___x_4386_) == 0 {
                    v_a_4387_ = leanh::lean_ctor_get(v___x_4386_, 0);
                    leanh::lean_inc(v_a_4387_);
                    leanh::lean_dec_ref_known(v___x_4386_, 1);
                    v_fst_4388_ = leanh::lean_ctor_get(v_a_4387_, 0);
                    leanh::lean_inc(v_fst_4388_);
                    v_snd_4389_ = leanh::lean_ctor_get(v_a_4387_, 1);
                    leanh::lean_inc(v_snd_4389_);
                    leanh::lean_dec(v_a_4387_);
                    v___x_4390_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppDiseqs_x3f(v_snd_4389_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_);
                    if leanh::lean_obj_tag(v___x_4390_) == 0 {
                        v_a_4391_ = leanh::lean_ctor_get(v___x_4390_, 0);
                        v_isSharedCheck_4415_ =
                            (!leanh::lean_is_exclusive(v___x_4390_)) as u8;
                        if v_isSharedCheck_4415_ == 0 {
                            v___x_4393_ = v___x_4390_;
                            v_isShared_4394_ = v_isSharedCheck_4415_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4391_);
                            leanh::lean_dec(v___x_4390_);
                            v___x_4393_ = leanh::lean_box(0);
                            v_isShared_4394_ = v_isSharedCheck_4415_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fst_4388_);
                        return v___x_4390_;
                    }
                } else {
                    return v___x_4386_;
                }
            }
            1 => {
                v_snd_4395_ = leanh::lean_ctor_get(v_a_4391_, 1);
                v_fst_4396_ = leanh::lean_ctor_get(v_a_4391_, 0);
                v_isSharedCheck_4414_ = (!leanh::lean_is_exclusive(v_a_4391_)) as u8;
                if v_isSharedCheck_4414_ == 0 {
                    v___x_4398_ = v_a_4391_;
                    v_isShared_4399_ = v_isSharedCheck_4414_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4395_);
                    leanh::lean_inc(v_fst_4396_);
                    leanh::lean_dec(v_a_4391_);
                    v___x_4398_ = leanh::lean_box(0);
                    v_isShared_4399_ = v_isSharedCheck_4414_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toRing_4400_ = leanh::lean_ctor_get(v_snd_4395_, 0);
                v_msgs_4401_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1___closed__0;
                v___x_4402_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_push(v_msgs_4401_, v_fst_4388_);
                v___x_4403_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_push(v___x_4402_, v_fst_4396_);
                leanh::lean_inc_ref(v_toRing_4400_);
                v___f_4404_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_4404_, 0, v_toRing_4400_);
                v___x_4405_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___closed__1;
                v___x_4406_ = lean_mk_thunk(v___f_4404_);
                v___x_4407_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption(v___x_4405_, v___x_4406_, v___x_4403_);
                leanh::lean_dec_ref(v___x_4406_);
                if v_isShared_4399_ == 0 {
                    leanh::lean_ctor_set(v___x_4398_, 0, v___x_4407_);
                    v___x_4409_ = v___x_4398_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4413_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4413_, 1, v_snd_4395_);
                    v___x_4409_ = v_reuseFailAlloc_4413_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4394_ == 0 {
                    leanh::lean_ctor_set(v___x_4393_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4393_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4412_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___boxed(
    mut v_a_4416_: *mut leanh::LeanObject,
    mut v_a_4417_: *mut leanh::LeanObject,
    mut v_a_4418_: *mut leanh::LeanObject,
    mut v_a_4419_: *mut leanh::LeanObject,
    mut v_a_4420_: *mut leanh::LeanObject,
    mut v_a_4421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4422_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f(v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
    leanh::lean_dec(v_a_4420_);
    leanh::lean_dec_ref(v_a_4419_);
    leanh::lean_dec(v_a_4418_);
    leanh::lean_dec_ref(v_a_4417_);
    return v_res_4422_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_CommRing_pp_x3f_spec__0(
    mut v_as_4423_: *mut leanh::LeanObject,
    mut v_sz_4424_: usize,
    mut v_i_4425_: usize,
    mut v_b_4426_: *mut leanh::LeanObject,
    mut v___y_4427_: *mut leanh::LeanObject,
    mut v___y_4428_: *mut leanh::LeanObject,
    mut v___y_4429_: *mut leanh::LeanObject,
    mut v___y_4430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: usize = 0;
    let mut v___x_4435_: usize = 0;
    let mut v___x_4437_: u8 = 0;
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4448_: u8 = 0;
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4452_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4437_ = lean_usize_dec_lt(v_i_4425_, v_sz_4424_);
                if v___x_4437_ == 0 {
                    v___x_4438_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4438_, 0, v_b_4426_);
                    return v___x_4438_;
                } else {
                    v_a_4439_ = lean_array_uget_borrowed(v_as_4423_, v_i_4425_);
                    leanh::lean_inc(v_a_4439_);
                    v___x_4440_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f(v_a_4439_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
                    if leanh::lean_obj_tag(v___x_4440_) == 0 {
                        v_a_4441_ = leanh::lean_ctor_get(v___x_4440_, 0);
                        leanh::lean_inc(v_a_4441_);
                        leanh::lean_dec_ref_known(v___x_4440_, 1);
                        v_fst_4442_ = leanh::lean_ctor_get(v_a_4441_, 0);
                        leanh::lean_inc(v_fst_4442_);
                        leanh::lean_dec(v_a_4441_);
                        if leanh::lean_obj_tag(v_fst_4442_) == 1 {
                            v_val_4443_ = leanh::lean_ctor_get(v_fst_4442_, 0);
                            leanh::lean_inc(v_val_4443_);
                            leanh::lean_dec_ref_known(v_fst_4442_, 1);
                            v___x_4444_ = lean_array_push(v_b_4426_, v_val_4443_);
                            v_a_4433_ = v___x_4444_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_fst_4442_);
                            v_a_4433_ = v_b_4426_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_4426_);
                        v_a_4445_ = leanh::lean_ctor_get(v___x_4440_, 0);
                        v_isSharedCheck_4452_ =
                            (!leanh::lean_is_exclusive(v___x_4440_)) as u8;
                        if v_isSharedCheck_4452_ == 0 {
                            v___x_4447_ = v___x_4440_;
                            v_isShared_4448_ = v_isSharedCheck_4452_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4445_);
                            leanh::lean_dec(v___x_4440_);
                            v___x_4447_ = leanh::lean_box(0);
                            v_isShared_4448_ = v_isSharedCheck_4452_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4434_ = 1usize;
                v___x_4435_ = lean_usize_add(v_i_4425_, v___x_4434_);
                v_i_4425_ = v___x_4435_;
                v_b_4426_ = v_a_4433_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_4448_ == 0 {
                    v___x_4450_ = v___x_4447_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4451_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
                    v___x_4450_ = v_reuseFailAlloc_4451_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4450_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_CommRing_pp_x3f_spec__0___boxed(
    mut v_as_4453_: *mut leanh::LeanObject,
    mut v_sz_4454_: *mut leanh::LeanObject,
    mut v_i_4455_: *mut leanh::LeanObject,
    mut v_b_4456_: *mut leanh::LeanObject,
    mut v___y_4457_: *mut leanh::LeanObject,
    mut v___y_4458_: *mut leanh::LeanObject,
    mut v___y_4459_: *mut leanh::LeanObject,
    mut v___y_4460_: *mut leanh::LeanObject,
    mut v___y_4461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4462_: usize = 0;
    let mut v_i_boxed_4463_: usize = 0;
    let mut v_res_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4462_ = leanh::lean_unbox_usize(v_sz_4454_);
    leanh::lean_dec(v_sz_4454_);
    v_i_boxed_4463_ = leanh::lean_unbox_usize(v_i_4455_);
    leanh::lean_dec(v_i_4455_);
    v_res_4464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_CommRing_pp_x3f_spec__0(v_as_4453_, v_sz_boxed_4462_, v_i_boxed_4463_, v_b_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
    leanh::lean_dec(v___y_4460_);
    leanh::lean_dec_ref(v___y_4459_);
    leanh::lean_dec(v___y_4458_);
    leanh::lean_dec_ref(v___y_4457_);
    leanh::lean_dec_ref(v_as_4453_);
    return v_res_4464_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: u8 = 0;
    let mut v___x_4467_: f64 = 0.0;
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4465_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__1;
    v___x_4466_ = 1;
    v___x_4467_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0);
    v___x_4468_ = leanh::lean_box(0);
    v___x_4469_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppRing_x3f___closed__1;
    v___x_4470_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
    leanh::lean_ctor_set(v___x_4470_, 0, v___x_4469_);
    leanh::lean_ctor_set(v___x_4470_, 1, v___x_4468_);
    leanh::lean_ctor_set(v___x_4470_, 2, v___x_4465_);
    leanh::lean_ctor_set_float(
        v___x_4470_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_4467_,
    );
    leanh::lean_ctor_set_float(
        v___x_4470_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        v___x_4467_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4470_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
        v___x_4466_,
    );
    return v___x_4470_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4474_ = l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__2;
    v___x_4475_ = l_Lean_MessageData_ofFormat(v___x_4474_);
    return v___x_4475_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_pp_x3f(
    mut v_goal_4476_: *mut leanh::LeanObject,
    mut v_a_4477_: *mut leanh::LeanObject,
    mut v_a_4478_: *mut leanh::LeanObject,
    mut v_a_4479_: *mut leanh::LeanObject,
    mut v_a_4480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4488_: usize = 0;
    let mut v___x_4489_: usize = 0;
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4494_: u8 = 0;
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: u8 = 0;
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4515_: u8 = 0;
    let mut v_a_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4519_: u8 = 0;
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_a_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4527_: u8 = 0;
    let mut v_ref_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4482_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                v___x_4483_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_4482_, v_goal_4476_);
                if leanh::lean_obj_tag(v___x_4483_) == 0 {
                    v_a_4484_ = leanh::lean_ctor_get(v___x_4483_, 0);
                    leanh::lean_inc(v_a_4484_);
                    leanh::lean_dec_ref_known(v___x_4483_, 1);
                    v_rings_4485_ = leanh::lean_ctor_get(v_a_4484_, 0);
                    leanh::lean_inc_ref(v_rings_4485_);
                    leanh::lean_dec(v_a_4484_);
                    v___x_4486_ = leanh::lean_unsigned_to_nat(0);
                    v_msgs_4487_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1___closed__0;
                    v_sz_4488_ = lean_array_size(v_rings_4485_);
                    v___x_4489_ = 0usize;
                    v___x_4490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_CommRing_pp_x3f_spec__0(v_rings_4485_, v_sz_4488_, v___x_4489_, v_msgs_4487_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_);
                    leanh::lean_dec_ref(v_rings_4485_);
                    if leanh::lean_obj_tag(v___x_4490_) == 0 {
                        v_a_4491_ = leanh::lean_ctor_get(v___x_4490_, 0);
                        v_isSharedCheck_4515_ =
                            (!leanh::lean_is_exclusive(v___x_4490_)) as u8;
                        if v_isSharedCheck_4515_ == 0 {
                            v___x_4493_ = v___x_4490_;
                            v_isShared_4494_ = v_isSharedCheck_4515_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4491_);
                            leanh::lean_dec(v___x_4490_);
                            v___x_4493_ = leanh::lean_box(0);
                            v_isShared_4494_ = v_isSharedCheck_4515_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4516_ = leanh::lean_ctor_get(v___x_4490_, 0);
                        v_isSharedCheck_4523_ =
                            (!leanh::lean_is_exclusive(v___x_4490_)) as u8;
                        if v_isSharedCheck_4523_ == 0 {
                            v___x_4518_ = v___x_4490_;
                            v_isShared_4519_ = v_isSharedCheck_4523_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4516_);
                            leanh::lean_dec(v___x_4490_);
                            v___x_4518_ = leanh::lean_box(0);
                            v_isShared_4519_ = v_isSharedCheck_4523_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_4524_ = leanh::lean_ctor_get(v___x_4483_, 0);
                    v_isSharedCheck_4536_ = (!leanh::lean_is_exclusive(v___x_4483_)) as u8;
                    if v_isSharedCheck_4536_ == 0 {
                        v___x_4526_ = v___x_4483_;
                        v_isShared_4527_ = v_isSharedCheck_4536_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4524_);
                        leanh::lean_dec(v___x_4483_);
                        v___x_4526_ = leanh::lean_box(0);
                        v_isShared_4527_ = v_isSharedCheck_4536_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4495_ = lean_array_get_size(v_a_4491_);
                v___x_4496_ = lean_nat_dec_eq(v___x_4495_, v___x_4486_);
                if v___x_4496_ == 0 {
                    v___x_4497_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4498_ = lean_nat_dec_eq(v___x_4495_, v___x_4497_);
                    if v___x_4498_ == 0 {
                        v___x_4499_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__0_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__0,
                        );
                        v___x_4500_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__3_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___closed__3,
                        );
                        v___x_4501_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_4501_, 0, v___x_4499_);
                        leanh::lean_ctor_set(v___x_4501_, 1, v___x_4500_);
                        leanh::lean_ctor_set(v___x_4501_, 2, v_a_4491_);
                        v___x_4502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4502_, 0, v___x_4501_);
                        if v_isShared_4494_ == 0 {
                            leanh::lean_ctor_set(v___x_4493_, 0, v___x_4502_);
                            v___x_4504_ = v___x_4493_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4505_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
                            v___x_4504_ = v_reuseFailAlloc_4505_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_4506_ = lean_array_fget(v_a_4491_, v___x_4486_);
                        leanh::lean_dec(v_a_4491_);
                        v___x_4507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4507_, 0, v___x_4506_);
                        if v_isShared_4494_ == 0 {
                            leanh::lean_ctor_set(v___x_4493_, 0, v___x_4507_);
                            v___x_4509_ = v___x_4493_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4510_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4507_);
                            v___x_4509_ = v_reuseFailAlloc_4510_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4491_);
                    v___x_4511_ = leanh::lean_box(0);
                    if v_isShared_4494_ == 0 {
                        leanh::lean_ctor_set(v___x_4493_, 0, v___x_4511_);
                        v___x_4513_ = v___x_4493_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4514_, 0, v___x_4511_);
                        v___x_4513_ = v_reuseFailAlloc_4514_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4504_;
            }
            3 => {
                return v___x_4509_;
            }
            4 => {
                return v___x_4513_;
            }
            5 => {
                if v_isShared_4519_ == 0 {
                    v___x_4521_ = v___x_4518_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4522_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
                    v___x_4521_ = v_reuseFailAlloc_4522_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4521_;
            }
            7 => {
                v_ref_4528_ = leanh::lean_ctor_get(v_a_4479_, 5);
                v___x_4529_ = lean_io_error_to_string(v_a_4524_);
                v___x_4530_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4530_, 0, v___x_4529_);
                v___x_4531_ = l_Lean_MessageData_ofFormat(v___x_4530_);
                leanh::lean_inc(v_ref_4528_);
                v___x_4532_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4532_, 0, v_ref_4528_);
                leanh::lean_ctor_set(v___x_4532_, 1, v___x_4531_);
                if v_isShared_4527_ == 0 {
                    leanh::lean_ctor_set(v___x_4526_, 0, v___x_4532_);
                    v___x_4534_ = v___x_4526_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4535_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4532_);
                    v___x_4534_ = v_reuseFailAlloc_4535_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_pp_x3f___boxed(
    mut v_goal_4537_: *mut leanh::LeanObject,
    mut v_a_4538_: *mut leanh::LeanObject,
    mut v_a_4539_: *mut leanh::LeanObject,
    mut v_a_4540_: *mut leanh::LeanObject,
    mut v_a_4541_: *mut leanh::LeanObject,
    mut v_a_4542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4543_ = l_Lean_Meta_Grind_Arith_CommRing_pp_x3f(
        v_goal_4537_,
        v_a_4538_,
        v_a_4539_,
        v_a_4540_,
        v_a_4541_,
    );
    leanh::lean_dec(v_a_4541_);
    leanh::lean_dec_ref(v_a_4540_);
    leanh::lean_dec(v_a_4539_);
    leanh::lean_dec_ref(v_a_4538_);
    leanh::lean_dec_ref(v_goal_4537_);
    return v_res_4543_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4548_ = l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__2;
    v___x_4549_ = l_Lean_stringToMessageData(v___x_4548_);
    return v___x_4549_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4551_ = l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__4;
    v___x_4552_ = l_Lean_stringToMessageData(v___x_4551_);
    return v___x_4552_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage(
    mut v_goal_4553_: *mut leanh::LeanObject,
    mut v_c_4554_: *mut leanh::LeanObject,
    mut v_msgs_4555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v_ringSteps_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: u8 = 0;
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: f64 = 0.0;
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4587_: u8 = 0;
    let mut v_a_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4591_: u8 = 0;
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4557_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                v___x_4558_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_4557_, v_goal_4553_);
                if leanh::lean_obj_tag(v___x_4558_) == 0 {
                    v_a_4559_ = leanh::lean_ctor_get(v___x_4558_, 0);
                    v_isSharedCheck_4587_ = (!leanh::lean_is_exclusive(v___x_4558_)) as u8;
                    if v_isSharedCheck_4587_ == 0 {
                        v___x_4561_ = v___x_4558_;
                        v_isShared_4562_ = v_isSharedCheck_4587_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4559_);
                        leanh::lean_dec(v___x_4558_);
                        v___x_4561_ = leanh::lean_box(0);
                        v_isShared_4562_ = v_isSharedCheck_4587_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgs_4555_);
                    leanh::lean_dec_ref(v_c_4554_);
                    v_a_4588_ = leanh::lean_ctor_get(v___x_4558_, 0);
                    v_isSharedCheck_4595_ = (!leanh::lean_is_exclusive(v___x_4558_)) as u8;
                    if v_isSharedCheck_4595_ == 0 {
                        v___x_4590_ = v___x_4558_;
                        v_isShared_4591_ = v_isSharedCheck_4595_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4588_);
                        leanh::lean_dec(v___x_4558_);
                        v___x_4590_ = leanh::lean_box(0);
                        v_isShared_4591_ = v_isSharedCheck_4595_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_ringSteps_4563_ = leanh::lean_ctor_get(v_c_4554_, 6);
                leanh::lean_inc(v_ringSteps_4563_);
                leanh::lean_dec_ref(v_c_4554_);
                v_steps_4564_ = leanh::lean_ctor_get(v_a_4559_, 12);
                leanh::lean_inc(v_steps_4564_);
                leanh::lean_dec(v_a_4559_);
                v___x_4565_ = lean_nat_dec_le(v_ringSteps_4563_, v_steps_4564_);
                leanh::lean_dec(v_steps_4564_);
                if v___x_4565_ == 0 {
                    leanh::lean_dec(v_ringSteps_4563_);
                    if v_isShared_4562_ == 0 {
                        leanh::lean_ctor_set(v___x_4561_, 0, v_msgs_4555_);
                        v___x_4567_ = v___x_4561_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_msgs_4555_);
                        v___x_4567_ = v_reuseFailAlloc_4568_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4569_ = l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__1;
                    v___x_4570_ = leanh::lean_box(0);
                    v___x_4571_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__0);
                    v___x_4572_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_toOption___closed__1;
                    v___x_4573_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v___x_4573_, 0, v___x_4569_);
                    leanh::lean_ctor_set(v___x_4573_, 1, v___x_4570_);
                    leanh::lean_ctor_set(v___x_4573_, 2, v___x_4572_);
                    leanh::lean_ctor_set_float(
                        v___x_4573_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_4571_,
                    );
                    leanh::lean_ctor_set_float(
                        v___x_4573_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_4571_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4573_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                        v___x_4565_,
                    );
                    v___x_4574_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__3_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__3,
                    );
                    v___x_4575_ = l_Nat_reprFast(v_ringSteps_4563_);
                    v___x_4576_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4576_, 0, v___x_4575_);
                    v___x_4577_ = l_Lean_MessageData_ofFormat(v___x_4576_);
                    v___x_4578_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4578_, 0, v___x_4574_);
                    leanh::lean_ctor_set(v___x_4578_, 1, v___x_4577_);
                    v___x_4579_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__5_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___closed__5,
                    );
                    v___x_4580_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4580_, 0, v___x_4578_);
                    leanh::lean_ctor_set(v___x_4580_, 1, v___x_4579_);
                    v___x_4581_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_ppBasis_x3f_spec__1___closed__0;
                    v___x_4582_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4582_, 0, v___x_4573_);
                    leanh::lean_ctor_set(v___x_4582_, 1, v___x_4580_);
                    leanh::lean_ctor_set(v___x_4582_, 2, v___x_4581_);
                    v___x_4583_ = lean_array_push(v_msgs_4555_, v___x_4582_);
                    if v_isShared_4562_ == 0 {
                        leanh::lean_ctor_set(v___x_4561_, 0, v___x_4583_);
                        v___x_4585_ = v___x_4561_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4586_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4583_);
                        v___x_4585_ = v_reuseFailAlloc_4586_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4567_;
            }
            3 => {
                return v___x_4585_;
            }
            4 => {
                if v_isShared_4591_ == 0 {
                    v___x_4593_ = v___x_4590_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4594_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
                    v___x_4593_ = v_reuseFailAlloc_4594_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage___boxed(
    mut v_goal_4596_: *mut leanh::LeanObject,
    mut v_c_4597_: *mut leanh::LeanObject,
    mut v_msgs_4598_: *mut leanh::LeanObject,
    mut v_a_4599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4600_ =
        l_Lean_Meta_Grind_Arith_CommRing_addThresholdMessage(v_goal_4596_, v_c_4597_, v_msgs_4598_);
    leanh::lean_dec_ref(v_goal_4596_);
    return v_res_4600_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM();
    leanh::lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_PP_0__Lean_Meta_Grind_Arith_CommRing_instMonadCommRingM);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin);
}