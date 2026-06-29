// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.PP
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.AC.DenoteExpr Init.Omega
use crate::r#gen::Init::Control::State::l_StateT_get;
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::DenoteExpr::{
    initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Types::l_Lean_Meta_Grind_AC_acExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types,
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::ffi::{lean_mk_thunk, lean_thunk_get_own};
use crate::ffi::{lean_array_size, lean_array_uget_borrowed};
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_nat_dec_eq, lean_nat_dec_lt,
};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0:
    f64 = 0.0;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [66, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject,13286986945483979944 as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value) as *mut crate::leanh::LeanObject,6004542540932731919 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [68, 105, 115, 101, 113, 117, 97, 108, 105, 116, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [78, 101, 0]};
static mut l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,6695605208187598753 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 105, 115, 101, 113, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value) as *mut crate::leanh::LeanObject,12150963035389937170 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [79, 112, 101, 114, 97, 116, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [80, 114, 111, 112, 101, 114, 116, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 115, 115, 111, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value) as *mut crate::leanh::LeanObject,12101614322480916425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [112, 114, 111, 112, 101, 114, 116, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value) as *mut crate::leanh::LeanObject,4640836329272094479 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 100, 101, 110, 116, 105, 116, 121, 58, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 100, 101, 109, 112, 111, 116, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 109, 109, 117, 116, 97, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [79, 112, 101, 114, 97, 116, 111, 114, 115, 0],
    };
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_pp_x3f___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_pp_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1213_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_1213_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1214_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0);
    v___x_1215_ = l_StateRefT_x27_instMonad___redArg(v___x_1214_);
    return v___x_1215_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v_toFunctor_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1247_: u8 = 0;
    let mut v___f_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut v_unused_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_unused_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1220_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1);
                v_toApplicative_1221_ = crate::leanh::lean_ctor_get(v___x_1220_, 0);
                v_toFunctor_1222_ = crate::leanh::lean_ctor_get(v_toApplicative_1221_, 0);
                v_toSeq_1223_ = crate::leanh::lean_ctor_get(v_toApplicative_1221_, 2);
                v_toSeqLeft_1224_ = crate::leanh::lean_ctor_get(v_toApplicative_1221_, 3);
                v_toSeqRight_1225_ = crate::leanh::lean_ctor_get(v_toApplicative_1221_, 4);
                v___f_1226_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2;
                v___f_1227_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_1222_, 2);
                v___f_1228_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1228_, 0, v_toFunctor_1222_);
                v___f_1229_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1229_, 0, v_toFunctor_1222_);
                v___x_1230_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1230_, 0, v___f_1228_);
                crate::leanh::lean_ctor_set(v___x_1230_, 1, v___f_1229_);
                crate::leanh::lean_inc(v_toSeqRight_1225_);
                v___f_1231_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1231_, 0, v_toSeqRight_1225_);
                crate::leanh::lean_inc(v_toSeqLeft_1224_);
                v___f_1232_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1232_, 0, v_toSeqLeft_1224_);
                crate::leanh::lean_inc(v_toSeq_1223_);
                v___f_1233_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1233_, 0, v_toSeq_1223_);
                v___x_1234_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1234_, 0, v___x_1230_);
                crate::leanh::lean_ctor_set(v___x_1234_, 1, v___f_1226_);
                crate::leanh::lean_ctor_set(v___x_1234_, 2, v___f_1233_);
                crate::leanh::lean_ctor_set(v___x_1234_, 3, v___f_1232_);
                crate::leanh::lean_ctor_set(v___x_1234_, 4, v___f_1231_);
                v___x_1235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1235_, 0, v___x_1234_);
                crate::leanh::lean_ctor_set(v___x_1235_, 1, v___f_1227_);
                v___x_1236_ = l_StateRefT_x27_instMonad___redArg(v___x_1235_);
                v_toApplicative_1237_ = crate::leanh::lean_ctor_get(v___x_1236_, 0);
                v_isSharedCheck_1265_ = (!crate::leanh::lean_is_exclusive(v___x_1236_)) as u8;
                if v_isSharedCheck_1265_ == 0 {
                    v_unused_1266_ = crate::leanh::lean_ctor_get(v___x_1236_, 1);
                    crate::leanh::lean_dec(v_unused_1266_);
                    v___x_1239_ = v___x_1236_;
                    v_isShared_1240_ = v_isSharedCheck_1265_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_1237_);
                    crate::leanh::lean_dec(v___x_1236_);
                    v___x_1239_ = crate::leanh::lean_box(0);
                    v_isShared_1240_ = v_isSharedCheck_1265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1241_ = crate::leanh::lean_ctor_get(v_toApplicative_1237_, 0);
                v_toSeq_1242_ = crate::leanh::lean_ctor_get(v_toApplicative_1237_, 2);
                v_toSeqLeft_1243_ = crate::leanh::lean_ctor_get(v_toApplicative_1237_, 3);
                v_toSeqRight_1244_ = crate::leanh::lean_ctor_get(v_toApplicative_1237_, 4);
                v_isSharedCheck_1263_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_1237_)) as u8;
                if v_isSharedCheck_1263_ == 0 {
                    v_unused_1264_ = crate::leanh::lean_ctor_get(v_toApplicative_1237_, 1);
                    crate::leanh::lean_dec(v_unused_1264_);
                    v___x_1246_ = v_toApplicative_1237_;
                    v_isShared_1247_ = v_isSharedCheck_1263_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_1244_);
                    crate::leanh::lean_inc(v_toSeqLeft_1243_);
                    crate::leanh::lean_inc(v_toSeq_1242_);
                    crate::leanh::lean_inc(v_toFunctor_1241_);
                    crate::leanh::lean_dec(v_toApplicative_1237_);
                    v___x_1246_ = crate::leanh::lean_box(0);
                    v_isShared_1247_ = v_isSharedCheck_1263_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1248_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4;
                v___f_1249_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_1241_);
                v___f_1250_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1250_, 0, v_toFunctor_1241_);
                v___f_1251_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1251_, 0, v_toFunctor_1241_);
                v___x_1252_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1252_, 0, v___f_1250_);
                crate::leanh::lean_ctor_set(v___x_1252_, 1, v___f_1251_);
                v___f_1253_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1253_, 0, v_toSeqRight_1244_);
                v___f_1254_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1254_, 0, v_toSeqLeft_1243_);
                v___f_1255_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1255_, 0, v_toSeq_1242_);
                if v_isShared_1247_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1246_, 4, v___f_1253_);
                    crate::leanh::lean_ctor_set(v___x_1246_, 3, v___f_1254_);
                    crate::leanh::lean_ctor_set(v___x_1246_, 2, v___f_1255_);
                    crate::leanh::lean_ctor_set(v___x_1246_, 1, v___f_1248_);
                    crate::leanh::lean_ctor_set(v___x_1246_, 0, v___x_1252_);
                    v___x_1257_ = v___x_1246_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___f_1248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 2, v___f_1255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 3, v___f_1254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 4, v___f_1253_);
                    v___x_1257_ = v_reuseFailAlloc_1262_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1240_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1239_, 1, v___f_1249_);
                    crate::leanh::lean_ctor_set(v___x_1239_, 0, v___x_1257_);
                    v___x_1259_ = v___x_1239_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1261_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___f_1249_);
                    v___x_1259_ = v_reuseFailAlloc_1261_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1260_ =
                    crate::leanh::lean_alloc_closure(l_StateT_get as *mut core::ffi::c_void, 4, 3);
                crate::leanh::lean_closure_set(v___x_1260_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1260_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_1260_, 2, v___x_1259_);
                return v___x_1260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0()
-> f64 {
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: f64 = 0.0;
    v___x_1267_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1268_ = lean_float_of_nat(v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
    mut v_cls_1270_: *mut crate::leanh::LeanObject,
    mut v_header_1271_: *mut crate::leanh::LeanObject,
    mut v_msgs_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: u8 = 0;
    v___x_1273_ = lean_array_get_size(v_msgs_1272_);
    v___x_1274_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1275_ = lean_nat_dec_eq(v___x_1273_, v___x_1274_);
    if v___x_1275_ == 0 {
        let mut v___x_1276_: u8 = 0;
        let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1278_: f64 = 0.0;
        let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1276_ = 1;
        v___x_1277_ = crate::leanh::lean_box(0);
        v___x_1278_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
        v___x_1279_ =
            l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
        v___x_1280_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
        crate::leanh::lean_ctor_set(v___x_1280_, 0, v_cls_1270_);
        crate::leanh::lean_ctor_set(v___x_1280_, 1, v___x_1277_);
        crate::leanh::lean_ctor_set(v___x_1280_, 2, v___x_1279_);
        crate::leanh::lean_ctor_set_float(
            v___x_1280_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            v___x_1278_,
        );
        crate::leanh::lean_ctor_set_float(
            v___x_1280_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
            v___x_1278_,
        );
        crate::leanh::lean_ctor_set_uint8(
            v___x_1280_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
            v___x_1276_,
        );
        v___x_1281_ = lean_thunk_get_own(v_header_1271_);
        v___x_1282_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1282_, 0, v___x_1280_);
        crate::leanh::lean_ctor_set(v___x_1282_, 1, v___x_1281_);
        crate::leanh::lean_ctor_set(v___x_1282_, 2, v_msgs_1272_);
        v___x_1283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1283_, 0, v___x_1282_);
        return v___x_1283_;
    } else {
        let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_msgs_1272_);
        crate::leanh::lean_dec(v_cls_1270_);
        v___x_1284_ = crate::leanh::lean_box(0);
        return v___x_1284_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___boxed(
    mut v_cls_1285_: *mut crate::leanh::LeanObject,
    mut v_header_1286_: *mut crate::leanh::LeanObject,
    mut v_msgs_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1288_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
        v_cls_1285_,
        v_header_1286_,
        v_msgs_1287_,
    );
    crate::leanh::lean_dec_ref(v_header_1286_);
    return v_res_1288_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(
    mut v_msgs_1289_: *mut crate::leanh::LeanObject,
    mut v_msg_x3f_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_msg_x3f_1290_) == 1 {
        let mut v_val_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1291_ = crate::leanh::lean_ctor_get(v_msg_x3f_1290_, 0);
        crate::leanh::lean_inc(v_val_1291_);
        crate::leanh::lean_dec_ref_known(v_msg_x3f_1290_, 1);
        v___x_1292_ = lean_array_push(v_msgs_1289_, v_val_1291_);
        return v___x_1292_;
    } else {
        crate::leanh::lean_dec(v_msg_x3f_1290_);
        return v_msgs_1289_;
    }
}
pub unsafe fn l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(
    mut v_e_1295_: *mut crate::leanh::LeanObject,
    mut v_cls_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: f64 = 0.0;
    let mut v___x_1299_: u8 = 0;
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = crate::leanh::lean_box(0);
    v___x_1298_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_1299_ = 1;
    v___x_1300_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_1301_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_1301_, 0, v_cls_1296_);
    crate::leanh::lean_ctor_set(v___x_1301_, 1, v___x_1297_);
    crate::leanh::lean_ctor_set(v___x_1301_, 2, v___x_1300_);
    crate::leanh::lean_ctor_set_float(
        v___x_1301_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1298_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_1301_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_1298_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1301_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_1299_,
    );
    v___x_1302_ = l_Lean_MessageData_ofExpr(v_e_1295_);
    v___x_1303_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_1304_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1304_, 0, v___x_1301_);
    crate::leanh::lean_ctor_set(v___x_1304_, 1, v___x_1302_);
    crate::leanh::lean_ctor_set(v___x_1304_, 2, v___x_1303_);
    return v___x_1304_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1308_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1;
    v___x_1309_ = l_Lean_MessageData_ofFormat(v___x_1308_);
    return v___x_1309_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0(
    mut v_x_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1311_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2);
    return v___x_1311_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(
    mut v_s_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1320_: u8 = 0;
    let mut v_size_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut v_x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v_fst_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v_op_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1315_ = l_Lean_instInhabitedExpr;
                if crate::leanh::lean_obj_tag(v_s_1312_) == 0 {
                    v_vars_1316_ = crate::leanh::lean_ctor_get(v___y_1313_, 10);
                    v_x_1317_ = crate::leanh::lean_ctor_get(v_s_1312_, 0);
                    v_isSharedCheck_1333_ = (!crate::leanh::lean_is_exclusive(v_s_1312_)) as u8;
                    if v_isSharedCheck_1333_ == 0 {
                        v___x_1319_ = v_s_1312_;
                        v_isShared_1320_ = v_isSharedCheck_1333_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_x_1317_);
                        crate::leanh::lean_dec(v_s_1312_);
                        v___x_1319_ = crate::leanh::lean_box(0);
                        v_isShared_1320_ = v_isSharedCheck_1333_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_x_1334_ = crate::leanh::lean_ctor_get(v_s_1312_, 0);
                    crate::leanh::lean_inc(v_x_1334_);
                    v_s_1335_ = crate::leanh::lean_ctor_get(v_s_1312_, 1);
                    crate::leanh::lean_inc_ref(v_s_1335_);
                    crate::leanh::lean_dec_ref_known(v_s_1312_, 2);
                    crate::leanh::lean_inc_ref(v___y_1313_);
                    v___x_1336_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_1335_, v___y_1313_);
                    v_a_1337_ = crate::leanh::lean_ctor_get(v___x_1336_, 0);
                    v_isSharedCheck_1362_ = (!crate::leanh::lean_is_exclusive(v___x_1336_)) as u8;
                    if v_isSharedCheck_1362_ == 0 {
                        v___x_1339_ = v___x_1336_;
                        v_isShared_1340_ = v_isSharedCheck_1362_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1337_);
                        crate::leanh::lean_dec(v___x_1336_);
                        v___x_1339_ = crate::leanh::lean_box(0);
                        v_isShared_1340_ = v_isSharedCheck_1362_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_size_1321_ = crate::leanh::lean_ctor_get(v_vars_1316_, 2);
                v___x_1322_ = lean_nat_dec_lt(v_x_1317_, v_size_1321_);
                if v___x_1322_ == 0 {
                    crate::leanh::lean_dec(v_x_1317_);
                    v___x_1323_ = l_outOfBounds___redArg(v___x_1315_);
                    v___x_1324_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1324_, 0, v___x_1323_);
                    crate::leanh::lean_ctor_set(v___x_1324_, 1, v___y_1313_);
                    if v_isShared_1320_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1319_, 0, v___x_1324_);
                        v___x_1326_ = v___x_1319_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
                        v___x_1326_ = v_reuseFailAlloc_1327_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1328_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_1315_,
                        v_vars_1316_,
                        v_x_1317_,
                    );
                    crate::leanh::lean_dec(v_x_1317_);
                    v___x_1329_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1329_, 0, v___x_1328_);
                    crate::leanh::lean_ctor_set(v___x_1329_, 1, v___y_1313_);
                    if v_isShared_1320_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1319_, 0, v___x_1329_);
                        v___x_1331_ = v___x_1319_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
                        v___x_1331_ = v_reuseFailAlloc_1332_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1326_;
            }
            3 => {
                return v___x_1331_;
            }
            4 => {
                v_fst_1341_ = crate::leanh::lean_ctor_get(v_a_1337_, 0);
                v_snd_1342_ = crate::leanh::lean_ctor_get(v_a_1337_, 1);
                v_isSharedCheck_1361_ = (!crate::leanh::lean_is_exclusive(v_a_1337_)) as u8;
                if v_isSharedCheck_1361_ == 0 {
                    v___x_1344_ = v_a_1337_;
                    v_isShared_1345_ = v_isSharedCheck_1361_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1342_);
                    crate::leanh::lean_inc(v_fst_1341_);
                    crate::leanh::lean_dec(v_a_1337_);
                    v___x_1344_ = crate::leanh::lean_box(0);
                    v_isShared_1345_ = v_isSharedCheck_1361_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_op_1346_ = crate::leanh::lean_ctor_get(v___y_1313_, 3);
                crate::leanh::lean_inc_ref(v_op_1346_);
                v_vars_1347_ = crate::leanh::lean_ctor_get(v___y_1313_, 10);
                crate::leanh::lean_inc_ref(v_vars_1347_);
                crate::leanh::lean_dec_ref(v___y_1313_);
                v_size_1357_ = crate::leanh::lean_ctor_get(v_vars_1347_, 2);
                v___x_1358_ = lean_nat_dec_lt(v_x_1334_, v_size_1357_);
                if v___x_1358_ == 0 {
                    crate::leanh::lean_dec_ref(v_vars_1347_);
                    crate::leanh::lean_dec(v_x_1334_);
                    v___x_1359_ = l_outOfBounds___redArg(v___x_1315_);
                    v___y_1349_ = v___x_1359_;
                    state = 6;
                    continue;
                } else {
                    v___x_1360_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_1315_,
                        v_vars_1347_,
                        v_x_1334_,
                    );
                    crate::leanh::lean_dec(v_x_1334_);
                    crate::leanh::lean_dec_ref(v_vars_1347_);
                    v___y_1349_ = v___x_1360_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1350_ = l_Lean_mkAppB(v_op_1346_, v___y_1349_, v_fst_1341_);
                if v_isShared_1345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1344_, 0, v___x_1350_);
                    v___x_1352_ = v___x_1344_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1356_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_snd_1342_);
                    v___x_1352_ = v_reuseFailAlloc_1356_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1340_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1339_, 0, v___x_1352_);
                    v___x_1354_ = v___x_1339_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
                    v___x_1354_ = v_reuseFailAlloc_1355_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg___boxed(
    mut v_s_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1366_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_1363_, v___y_1364_);
    return v_res_1366_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(
    mut v_c_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
    mut v___y_1372_: *mut crate::leanh::LeanObject,
    mut v___y_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1385_: u8 = 0;
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v_fst_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1395_: u8 = 0;
    let mut v_type_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1377_ = crate::leanh::lean_ctor_get(v_c_1370_, 0);
                crate::leanh::lean_inc_ref(v_lhs_1377_);
                v_rhs_1378_ = crate::leanh::lean_ctor_get(v_c_1370_, 1);
                crate::leanh::lean_inc_ref(v_rhs_1378_);
                crate::leanh::lean_dec_ref(v_c_1370_);
                crate::leanh::lean_inc_ref(v___y_1371_);
                v___x_1379_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_1377_, v___y_1371_);
                v_a_1380_ = crate::leanh::lean_ctor_get(v___x_1379_, 0);
                crate::leanh::lean_inc(v_a_1380_);
                crate::leanh::lean_dec_ref(v___x_1379_);
                v_fst_1381_ = crate::leanh::lean_ctor_get(v_a_1380_, 0);
                v_snd_1382_ = crate::leanh::lean_ctor_get(v_a_1380_, 1);
                v_isSharedCheck_1413_ = (!crate::leanh::lean_is_exclusive(v_a_1380_)) as u8;
                if v_isSharedCheck_1413_ == 0 {
                    v___x_1384_ = v_a_1380_;
                    v_isShared_1385_ = v_isSharedCheck_1413_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1382_);
                    crate::leanh::lean_inc(v_fst_1381_);
                    crate::leanh::lean_dec(v_a_1380_);
                    v___x_1384_ = crate::leanh::lean_box(0);
                    v_isShared_1385_ = v_isSharedCheck_1413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1386_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_1378_, v_snd_1382_);
                v_a_1387_ = crate::leanh::lean_ctor_get(v___x_1386_, 0);
                v_isSharedCheck_1412_ = (!crate::leanh::lean_is_exclusive(v___x_1386_)) as u8;
                if v_isSharedCheck_1412_ == 0 {
                    v___x_1389_ = v___x_1386_;
                    v_isShared_1390_ = v_isSharedCheck_1412_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1387_);
                    crate::leanh::lean_dec(v___x_1386_);
                    v___x_1389_ = crate::leanh::lean_box(0);
                    v_isShared_1390_ = v_isSharedCheck_1412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_1391_ = crate::leanh::lean_ctor_get(v_a_1387_, 0);
                v_snd_1392_ = crate::leanh::lean_ctor_get(v_a_1387_, 1);
                v_isSharedCheck_1411_ = (!crate::leanh::lean_is_exclusive(v_a_1387_)) as u8;
                if v_isSharedCheck_1411_ == 0 {
                    v___x_1394_ = v_a_1387_;
                    v_isShared_1395_ = v_isSharedCheck_1411_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1392_);
                    crate::leanh::lean_inc(v_fst_1391_);
                    crate::leanh::lean_dec(v_a_1387_);
                    v___x_1394_ = crate::leanh::lean_box(0);
                    v_isShared_1395_ = v_isSharedCheck_1411_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_type_1396_ = crate::leanh::lean_ctor_get(v___y_1371_, 1);
                crate::leanh::lean_inc_ref(v_type_1396_);
                v_u_1397_ = crate::leanh::lean_ctor_get(v___y_1371_, 2);
                crate::leanh::lean_inc(v_u_1397_);
                crate::leanh::lean_dec_ref(v___y_1371_);
                v___x_1398_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1;
                v___x_1399_ = crate::leanh::lean_box(0);
                if v_isShared_1385_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1384_, 1);
                    crate::leanh::lean_ctor_set(v___x_1384_, 1, v___x_1399_);
                    crate::leanh::lean_ctor_set(v___x_1384_, 0, v_u_1397_);
                    v___x_1401_ = v___x_1384_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_u_1397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1399_);
                    v___x_1401_ = v_reuseFailAlloc_1410_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1402_ = l_Lean_mkConst(v___x_1398_, v___x_1401_);
                v___x_1403_ = l_Lean_mkApp3(v___x_1402_, v_type_1396_, v_fst_1381_, v_fst_1391_);
                if v_isShared_1395_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1394_, 0, v___x_1403_);
                    v___x_1405_ = v___x_1394_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_snd_1392_);
                    v___x_1405_ = v_reuseFailAlloc_1409_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1390_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1389_, 0, v___x_1405_);
                    v___x_1407_ = v___x_1389_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
                    v___x_1407_ = v_reuseFailAlloc_1408_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1407_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___boxed(
    mut v_c_1414_: *mut crate::leanh::LeanObject,
    mut v___y_1415_: *mut crate::leanh::LeanObject,
    mut v___y_1416_: *mut crate::leanh::LeanObject,
    mut v___y_1417_: *mut crate::leanh::LeanObject,
    mut v___y_1418_: *mut crate::leanh::LeanObject,
    mut v___y_1419_: *mut crate::leanh::LeanObject,
    mut v___y_1420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_c_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
    crate::leanh::lean_dec(v___y_1419_);
    crate::leanh::lean_dec_ref(v___y_1418_);
    crate::leanh::lean_dec(v___y_1417_);
    crate::leanh::lean_dec_ref(v___y_1416_);
    return v_res_1421_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(
    mut v_as_x27_1426_: *mut crate::leanh::LeanObject,
    mut v_b_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_1426_) == 0 {
                    v___x_1434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1434_, 0, v_b_1427_);
                    crate::leanh::lean_ctor_set(v___x_1434_, 1, v___y_1428_);
                    v___x_1435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1435_, 0, v___x_1434_);
                    return v___x_1435_;
                } else {
                    v_head_1436_ = crate::leanh::lean_ctor_get(v_as_x27_1426_, 0);
                    v_tail_1437_ = crate::leanh::lean_ctor_get(v_as_x27_1426_, 1);
                    crate::leanh::lean_inc(v_head_1436_);
                    v___x_1438_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_head_1436_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
                    v_a_1439_ = crate::leanh::lean_ctor_get(v___x_1438_, 0);
                    crate::leanh::lean_inc(v_a_1439_);
                    crate::leanh::lean_dec_ref(v___x_1438_);
                    v_fst_1440_ = crate::leanh::lean_ctor_get(v_a_1439_, 0);
                    crate::leanh::lean_inc(v_fst_1440_);
                    v_snd_1441_ = crate::leanh::lean_ctor_get(v_a_1439_, 1);
                    crate::leanh::lean_inc(v_snd_1441_);
                    crate::leanh::lean_dec(v_a_1439_);
                    v___x_1442_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                    v___x_1443_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1440_, v___x_1442_);
                    v___x_1444_ = lean_array_push(v_b_1427_, v___x_1443_);
                    v_as_x27_1426_ = v_tail_1437_;
                    v_b_1427_ = v___x_1444_;
                    v___y_1428_ = v_snd_1441_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___boxed(
    mut v_as_x27_1446_: *mut crate::leanh::LeanObject,
    mut v_b_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
    mut v___y_1452_: *mut crate::leanh::LeanObject,
    mut v___y_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1454_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_1446_, v_b_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
    crate::leanh::lean_dec(v___y_1452_);
    crate::leanh::lean_dec_ref(v___y_1451_);
    crate::leanh::lean_dec(v___y_1450_);
    crate::leanh::lean_dec_ref(v___y_1449_);
    crate::leanh::lean_dec(v_as_x27_1446_);
    return v_res_1454_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1459_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0;
    v___x_1460_ = lean_mk_thunk(v___f_1459_);
    return v___x_1460_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(
    mut v_a_1461_: *mut crate::leanh::LeanObject,
    mut v_a_1462_: *mut crate::leanh::LeanObject,
    mut v_a_1463_: *mut crate::leanh::LeanObject,
    mut v_a_1464_: *mut crate::leanh::LeanObject,
    mut v_a_1465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_basis_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v_fst_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_a_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_basis_1467_ = crate::leanh::lean_ctor_get(v_a_1461_, 15);
                crate::leanh::lean_inc(v_basis_1467_);
                v_basis_1468_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
                v___x_1469_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_basis_1467_, v_basis_1468_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
                crate::leanh::lean_dec(v_basis_1467_);
                if crate::leanh::lean_obj_tag(v___x_1469_) == 0 {
                    v_a_1470_ = crate::leanh::lean_ctor_get(v___x_1469_, 0);
                    v_isSharedCheck_1489_ = (!crate::leanh::lean_is_exclusive(v___x_1469_)) as u8;
                    if v_isSharedCheck_1489_ == 0 {
                        v___x_1472_ = v___x_1469_;
                        v_isShared_1473_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1470_);
                        crate::leanh::lean_dec(v___x_1469_);
                        v___x_1472_ = crate::leanh::lean_box(0);
                        v_isShared_1473_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1490_ = crate::leanh::lean_ctor_get(v___x_1469_, 0);
                    v_isSharedCheck_1497_ = (!crate::leanh::lean_is_exclusive(v___x_1469_)) as u8;
                    if v_isSharedCheck_1497_ == 0 {
                        v___x_1492_ = v___x_1469_;
                        v_isShared_1493_ = v_isSharedCheck_1497_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1490_);
                        crate::leanh::lean_dec(v___x_1469_);
                        v___x_1492_ = crate::leanh::lean_box(0);
                        v_isShared_1493_ = v_isSharedCheck_1497_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1474_ = crate::leanh::lean_ctor_get(v_a_1470_, 0);
                v_snd_1475_ = crate::leanh::lean_ctor_get(v_a_1470_, 1);
                v_isSharedCheck_1488_ = (!crate::leanh::lean_is_exclusive(v_a_1470_)) as u8;
                if v_isSharedCheck_1488_ == 0 {
                    v___x_1477_ = v_a_1470_;
                    v_isShared_1478_ = v_isSharedCheck_1488_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1475_);
                    crate::leanh::lean_inc(v_fst_1474_);
                    crate::leanh::lean_dec(v_a_1470_);
                    v___x_1477_ = crate::leanh::lean_box(0);
                    v_isShared_1478_ = v_isSharedCheck_1488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1479_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2;
                v___x_1480_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3);
                v___x_1481_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
                        v___x_1479_,
                        v___x_1480_,
                        v_fst_1474_,
                    );
                if v_isShared_1478_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1477_, 0, v___x_1481_);
                    v___x_1483_ = v___x_1477_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_snd_1475_);
                    v___x_1483_ = v_reuseFailAlloc_1487_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1473_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1472_, 0, v___x_1483_);
                    v___x_1485_ = v___x_1472_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
                    v___x_1485_ = v_reuseFailAlloc_1486_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1485_;
            }
            5 => {
                if v_isShared_1493_ == 0 {
                    v___x_1495_ = v___x_1492_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
                    v___x_1495_ = v_reuseFailAlloc_1496_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___boxed(
    mut v_a_1498_: *mut crate::leanh::LeanObject,
    mut v_a_1499_: *mut crate::leanh::LeanObject,
    mut v_a_1500_: *mut crate::leanh::LeanObject,
    mut v_a_1501_: *mut crate::leanh::LeanObject,
    mut v_a_1502_: *mut crate::leanh::LeanObject,
    mut v_a_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1504_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(
        v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_,
    );
    crate::leanh::lean_dec(v_a_1502_);
    crate::leanh::lean_dec_ref(v_a_1501_);
    crate::leanh::lean_dec(v_a_1500_);
    crate::leanh::lean_dec_ref(v_a_1499_);
    return v_res_1504_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(
    mut v_as_1505_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1506_: *mut crate::leanh::LeanObject,
    mut v_b_1507_: *mut crate::leanh::LeanObject,
    mut v_a_1508_: *mut crate::leanh::LeanObject,
    mut v___y_1509_: *mut crate::leanh::LeanObject,
    mut v___y_1510_: *mut crate::leanh::LeanObject,
    mut v___y_1511_: *mut crate::leanh::LeanObject,
    mut v___y_1512_: *mut crate::leanh::LeanObject,
    mut v___y_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1515_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_1506_, v_b_1507_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
    return v___x_1515_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___boxed(
    mut v_as_1516_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1517_: *mut crate::leanh::LeanObject,
    mut v_b_1518_: *mut crate::leanh::LeanObject,
    mut v_a_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
    mut v___y_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1526_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(v_as_1516_, v_as_x27_1517_, v_b_1518_, v_a_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
    crate::leanh::lean_dec(v___y_1524_);
    crate::leanh::lean_dec_ref(v___y_1523_);
    crate::leanh::lean_dec(v___y_1522_);
    crate::leanh::lean_dec_ref(v___y_1521_);
    crate::leanh::lean_dec(v_as_x27_1517_);
    crate::leanh::lean_dec(v_as_1516_);
    return v_res_1526_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(
    mut v_s_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
    mut v___y_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_1527_, v___y_1528_);
    return v___x_1534_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___boxed(
    mut v_s_1535_: *mut crate::leanh::LeanObject,
    mut v___y_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
    mut v___y_1538_: *mut crate::leanh::LeanObject,
    mut v___y_1539_: *mut crate::leanh::LeanObject,
    mut v___y_1540_: *mut crate::leanh::LeanObject,
    mut v___y_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(v_s_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
    crate::leanh::lean_dec(v___y_1540_);
    crate::leanh::lean_dec_ref(v___y_1539_);
    crate::leanh::lean_dec(v___y_1538_);
    crate::leanh::lean_dec_ref(v___y_1537_);
    return v_res_1542_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1;
    v___x_1547_ = l_Lean_MessageData_ofFormat(v___x_1546_);
    return v___x_1547_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0(
    mut v_x_1548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1549_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2);
    return v___x_1549_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(
    mut v_c_1553_: *mut crate::leanh::LeanObject,
    mut v___y_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v_fst_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v_type_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_isSharedCheck_1592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1556_ = crate::leanh::lean_ctor_get(v_c_1553_, 0);
                crate::leanh::lean_inc_ref(v_lhs_1556_);
                v_rhs_1557_ = crate::leanh::lean_ctor_get(v_c_1553_, 1);
                crate::leanh::lean_inc_ref(v_rhs_1557_);
                crate::leanh::lean_dec_ref(v_c_1553_);
                crate::leanh::lean_inc_ref(v___y_1554_);
                v___x_1558_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_1556_, v___y_1554_);
                v_a_1559_ = crate::leanh::lean_ctor_get(v___x_1558_, 0);
                crate::leanh::lean_inc(v_a_1559_);
                crate::leanh::lean_dec_ref(v___x_1558_);
                v_fst_1560_ = crate::leanh::lean_ctor_get(v_a_1559_, 0);
                v_snd_1561_ = crate::leanh::lean_ctor_get(v_a_1559_, 1);
                v_isSharedCheck_1592_ = (!crate::leanh::lean_is_exclusive(v_a_1559_)) as u8;
                if v_isSharedCheck_1592_ == 0 {
                    v___x_1563_ = v_a_1559_;
                    v_isShared_1564_ = v_isSharedCheck_1592_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1561_);
                    crate::leanh::lean_inc(v_fst_1560_);
                    crate::leanh::lean_dec(v_a_1559_);
                    v___x_1563_ = crate::leanh::lean_box(0);
                    v_isShared_1564_ = v_isSharedCheck_1592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1565_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_1557_, v_snd_1561_);
                v_a_1566_ = crate::leanh::lean_ctor_get(v___x_1565_, 0);
                v_isSharedCheck_1591_ = (!crate::leanh::lean_is_exclusive(v___x_1565_)) as u8;
                if v_isSharedCheck_1591_ == 0 {
                    v___x_1568_ = v___x_1565_;
                    v_isShared_1569_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1566_);
                    crate::leanh::lean_dec(v___x_1565_);
                    v___x_1568_ = crate::leanh::lean_box(0);
                    v_isShared_1569_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_1570_ = crate::leanh::lean_ctor_get(v_a_1566_, 0);
                v_snd_1571_ = crate::leanh::lean_ctor_get(v_a_1566_, 1);
                v_isSharedCheck_1590_ = (!crate::leanh::lean_is_exclusive(v_a_1566_)) as u8;
                if v_isSharedCheck_1590_ == 0 {
                    v___x_1573_ = v_a_1566_;
                    v_isShared_1574_ = v_isSharedCheck_1590_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1571_);
                    crate::leanh::lean_inc(v_fst_1570_);
                    crate::leanh::lean_dec(v_a_1566_);
                    v___x_1573_ = crate::leanh::lean_box(0);
                    v_isShared_1574_ = v_isSharedCheck_1590_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_type_1575_ = crate::leanh::lean_ctor_get(v___y_1554_, 1);
                crate::leanh::lean_inc_ref(v_type_1575_);
                v_u_1576_ = crate::leanh::lean_ctor_get(v___y_1554_, 2);
                crate::leanh::lean_inc(v_u_1576_);
                crate::leanh::lean_dec_ref(v___y_1554_);
                v___x_1577_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1;
                v___x_1578_ = crate::leanh::lean_box(0);
                if v_isShared_1564_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1563_, 1);
                    crate::leanh::lean_ctor_set(v___x_1563_, 1, v___x_1578_);
                    crate::leanh::lean_ctor_set(v___x_1563_, 0, v_u_1576_);
                    v___x_1580_ = v___x_1563_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_u_1576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1578_);
                    v___x_1580_ = v_reuseFailAlloc_1589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1581_ = l_Lean_mkConst(v___x_1577_, v___x_1580_);
                v___x_1582_ = l_Lean_mkApp3(v___x_1581_, v_type_1575_, v_fst_1560_, v_fst_1570_);
                if v_isShared_1574_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1573_, 0, v___x_1582_);
                    v___x_1584_ = v___x_1573_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1588_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_snd_1571_);
                    v___x_1584_ = v_reuseFailAlloc_1588_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1568_, 0, v___x_1584_);
                    v___x_1586_ = v___x_1568_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
                    v___x_1586_ = v_reuseFailAlloc_1587_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1586_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___boxed(
    mut v_c_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1596_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_1593_, v___y_1594_);
    return v_res_1596_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(
    mut v_as_1597_: *mut crate::leanh::LeanObject,
    mut v_sz_1598_: usize,
    mut v_i_1599_: usize,
    mut v_b_1600_: *mut crate::leanh::LeanObject,
    mut v___y_1601_: *mut crate::leanh::LeanObject,
    mut v___y_1602_: *mut crate::leanh::LeanObject,
    mut v___y_1603_: *mut crate::leanh::LeanObject,
    mut v___y_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1618_: u8 = 0;
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: usize = 0;
    let mut v___x_1626_: usize = 0;
    let mut v_reuseFailAlloc_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut v_a_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1633_: u8 = 0;
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1607_ = lean_usize_dec_lt(v_i_1599_, v_sz_1598_);
                if v___x_1607_ == 0 {
                    v___x_1608_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1608_, 0, v_b_1600_);
                    crate::leanh::lean_ctor_set(v___x_1608_, 1, v___y_1601_);
                    v___x_1609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1609_, 0, v___x_1608_);
                    return v___x_1609_;
                } else {
                    v_snd_1610_ = crate::leanh::lean_ctor_get(v_b_1600_, 1);
                    crate::leanh::lean_inc(v_snd_1610_);
                    crate::leanh::lean_dec_ref(v_b_1600_);
                    v_a_1611_ = lean_array_uget_borrowed(v_as_1597_, v_i_1599_);
                    crate::leanh::lean_inc(v_a_1611_);
                    v___x_1612_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1611_, v___y_1601_);
                    if crate::leanh::lean_obj_tag(v___x_1612_) == 0 {
                        v_a_1613_ = crate::leanh::lean_ctor_get(v___x_1612_, 0);
                        crate::leanh::lean_inc(v_a_1613_);
                        crate::leanh::lean_dec_ref_known(v___x_1612_, 1);
                        v_fst_1614_ = crate::leanh::lean_ctor_get(v_a_1613_, 0);
                        v_snd_1615_ = crate::leanh::lean_ctor_get(v_a_1613_, 1);
                        v_isSharedCheck_1629_ = (!crate::leanh::lean_is_exclusive(v_a_1613_)) as u8;
                        if v_isSharedCheck_1629_ == 0 {
                            v___x_1617_ = v_a_1613_;
                            v_isShared_1618_ = v_isSharedCheck_1629_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1615_);
                            crate::leanh::lean_inc(v_fst_1614_);
                            crate::leanh::lean_dec(v_a_1613_);
                            v___x_1617_ = crate::leanh::lean_box(0);
                            v_isShared_1618_ = v_isSharedCheck_1629_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1610_);
                        v_a_1630_ = crate::leanh::lean_ctor_get(v___x_1612_, 0);
                        v_isSharedCheck_1637_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1612_)) as u8;
                        if v_isSharedCheck_1637_ == 0 {
                            v___x_1632_ = v___x_1612_;
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1630_);
                            crate::leanh::lean_dec(v___x_1612_);
                            v___x_1632_ = crate::leanh::lean_box(0);
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1619_ = crate::leanh::lean_box(0);
                v___x_1620_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1621_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1614_, v___x_1620_);
                v___x_1622_ = lean_array_push(v_snd_1610_, v___x_1621_);
                if v_isShared_1618_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1617_, 1, v___x_1622_);
                    crate::leanh::lean_ctor_set(v___x_1617_, 0, v___x_1619_);
                    v___x_1624_ = v___x_1617_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1628_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1622_);
                    v___x_1624_ = v_reuseFailAlloc_1628_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1625_ = 1usize;
                v___x_1626_ = lean_usize_add(v_i_1599_, v___x_1625_);
                v_i_1599_ = v___x_1626_;
                v_b_1600_ = v___x_1624_;
                v___y_1601_ = v_snd_1615_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_1633_ == 0 {
                    v___x_1635_ = v___x_1632_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
                    v___x_1635_ = v_reuseFailAlloc_1636_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1635_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_as_1638_: *mut crate::leanh::LeanObject,
    mut v_sz_1639_: *mut crate::leanh::LeanObject,
    mut v_i_1640_: *mut crate::leanh::LeanObject,
    mut v_b_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1648_: usize = 0;
    let mut v_i_boxed_1649_: usize = 0;
    let mut v_res_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1648_ = crate::leanh::lean_unbox_usize(v_sz_1639_);
    crate::leanh::lean_dec(v_sz_1639_);
    v_i_boxed_1649_ = crate::leanh::lean_unbox_usize(v_i_1640_);
    crate::leanh::lean_dec(v_i_1640_);
    v_res_1650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_1638_, v_sz_boxed_1648_, v_i_boxed_1649_, v_b_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
    crate::leanh::lean_dec(v___y_1646_);
    crate::leanh::lean_dec_ref(v___y_1645_);
    crate::leanh::lean_dec(v___y_1644_);
    crate::leanh::lean_dec_ref(v___y_1643_);
    crate::leanh::lean_dec_ref(v_as_1638_);
    return v_res_1650_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(
    mut v_as_1651_: *mut crate::leanh::LeanObject,
    mut v_sz_1652_: usize,
    mut v_i_1653_: usize,
    mut v_b_1654_: *mut crate::leanh::LeanObject,
    mut v___y_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: usize = 0;
    let mut v___x_1680_: usize = 0;
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut v_a_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1661_ = lean_usize_dec_lt(v_i_1653_, v_sz_1652_);
                if v___x_1661_ == 0 {
                    v___x_1662_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1662_, 0, v_b_1654_);
                    crate::leanh::lean_ctor_set(v___x_1662_, 1, v___y_1655_);
                    v___x_1663_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1663_, 0, v___x_1662_);
                    return v___x_1663_;
                } else {
                    v_snd_1664_ = crate::leanh::lean_ctor_get(v_b_1654_, 1);
                    crate::leanh::lean_inc(v_snd_1664_);
                    crate::leanh::lean_dec_ref(v_b_1654_);
                    v_a_1665_ = lean_array_uget_borrowed(v_as_1651_, v_i_1653_);
                    crate::leanh::lean_inc(v_a_1665_);
                    v___x_1666_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1665_, v___y_1655_);
                    if crate::leanh::lean_obj_tag(v___x_1666_) == 0 {
                        v_a_1667_ = crate::leanh::lean_ctor_get(v___x_1666_, 0);
                        crate::leanh::lean_inc(v_a_1667_);
                        crate::leanh::lean_dec_ref_known(v___x_1666_, 1);
                        v_fst_1668_ = crate::leanh::lean_ctor_get(v_a_1667_, 0);
                        v_snd_1669_ = crate::leanh::lean_ctor_get(v_a_1667_, 1);
                        v_isSharedCheck_1683_ = (!crate::leanh::lean_is_exclusive(v_a_1667_)) as u8;
                        if v_isSharedCheck_1683_ == 0 {
                            v___x_1671_ = v_a_1667_;
                            v_isShared_1672_ = v_isSharedCheck_1683_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1669_);
                            crate::leanh::lean_inc(v_fst_1668_);
                            crate::leanh::lean_dec(v_a_1667_);
                            v___x_1671_ = crate::leanh::lean_box(0);
                            v_isShared_1672_ = v_isSharedCheck_1683_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1664_);
                        v_a_1684_ = crate::leanh::lean_ctor_get(v___x_1666_, 0);
                        v_isSharedCheck_1691_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1666_)) as u8;
                        if v_isSharedCheck_1691_ == 0 {
                            v___x_1686_ = v___x_1666_;
                            v_isShared_1687_ = v_isSharedCheck_1691_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1684_);
                            crate::leanh::lean_dec(v___x_1666_);
                            v___x_1686_ = crate::leanh::lean_box(0);
                            v_isShared_1687_ = v_isSharedCheck_1691_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1673_ = crate::leanh::lean_box(0);
                v___x_1674_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1675_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1668_, v___x_1674_);
                v___x_1676_ = lean_array_push(v_snd_1664_, v___x_1675_);
                if v_isShared_1672_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1671_, 1, v___x_1676_);
                    crate::leanh::lean_ctor_set(v___x_1671_, 0, v___x_1673_);
                    v___x_1678_ = v___x_1671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1676_);
                    v___x_1678_ = v_reuseFailAlloc_1682_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1679_ = 1usize;
                v___x_1680_ = lean_usize_add(v_i_1653_, v___x_1679_);
                v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_1651_, v_sz_1652_, v___x_1680_, v___x_1678_, v_snd_1669_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
                return v___x_1681_;
            }
            3 => {
                if v_isShared_1687_ == 0 {
                    v___x_1689_ = v___x_1686_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
                    v___x_1689_ = v_reuseFailAlloc_1690_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2___boxed(
    mut v_as_1692_: *mut crate::leanh::LeanObject,
    mut v_sz_1693_: *mut crate::leanh::LeanObject,
    mut v_i_1694_: *mut crate::leanh::LeanObject,
    mut v_b_1695_: *mut crate::leanh::LeanObject,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1702_: usize = 0;
    let mut v_i_boxed_1703_: usize = 0;
    let mut v_res_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1702_ = crate::leanh::lean_unbox_usize(v_sz_1693_);
    crate::leanh::lean_dec(v_sz_1693_);
    v_i_boxed_1703_ = crate::leanh::lean_unbox_usize(v_i_1694_);
    crate::leanh::lean_dec(v_i_1694_);
    v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_as_1692_, v_sz_boxed_1702_, v_i_boxed_1703_, v_b_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
    crate::leanh::lean_dec(v___y_1700_);
    crate::leanh::lean_dec_ref(v___y_1699_);
    crate::leanh::lean_dec(v___y_1698_);
    crate::leanh::lean_dec_ref(v___y_1697_);
    crate::leanh::lean_dec_ref(v_as_1692_);
    return v_res_1704_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(
    mut v_as_1705_: *mut crate::leanh::LeanObject,
    mut v_sz_1706_: usize,
    mut v_i_1707_: usize,
    mut v_b_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: usize = 0;
    let mut v___x_1734_: usize = 0;
    let mut v_reuseFailAlloc_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_a_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1715_ = lean_usize_dec_lt(v_i_1707_, v_sz_1706_);
                if v___x_1715_ == 0 {
                    v___x_1716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1716_, 0, v_b_1708_);
                    crate::leanh::lean_ctor_set(v___x_1716_, 1, v___y_1709_);
                    v___x_1717_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1717_, 0, v___x_1716_);
                    return v___x_1717_;
                } else {
                    v_snd_1718_ = crate::leanh::lean_ctor_get(v_b_1708_, 1);
                    crate::leanh::lean_inc(v_snd_1718_);
                    crate::leanh::lean_dec_ref(v_b_1708_);
                    v_a_1719_ = lean_array_uget_borrowed(v_as_1705_, v_i_1707_);
                    crate::leanh::lean_inc(v_a_1719_);
                    v___x_1720_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1719_, v___y_1709_);
                    if crate::leanh::lean_obj_tag(v___x_1720_) == 0 {
                        v_a_1721_ = crate::leanh::lean_ctor_get(v___x_1720_, 0);
                        crate::leanh::lean_inc(v_a_1721_);
                        crate::leanh::lean_dec_ref_known(v___x_1720_, 1);
                        v_fst_1722_ = crate::leanh::lean_ctor_get(v_a_1721_, 0);
                        v_snd_1723_ = crate::leanh::lean_ctor_get(v_a_1721_, 1);
                        v_isSharedCheck_1737_ = (!crate::leanh::lean_is_exclusive(v_a_1721_)) as u8;
                        if v_isSharedCheck_1737_ == 0 {
                            v___x_1725_ = v_a_1721_;
                            v_isShared_1726_ = v_isSharedCheck_1737_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1723_);
                            crate::leanh::lean_inc(v_fst_1722_);
                            crate::leanh::lean_dec(v_a_1721_);
                            v___x_1725_ = crate::leanh::lean_box(0);
                            v_isShared_1726_ = v_isSharedCheck_1737_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1718_);
                        v_a_1738_ = crate::leanh::lean_ctor_get(v___x_1720_, 0);
                        v_isSharedCheck_1745_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1720_)) as u8;
                        if v_isSharedCheck_1745_ == 0 {
                            v___x_1740_ = v___x_1720_;
                            v_isShared_1741_ = v_isSharedCheck_1745_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1738_);
                            crate::leanh::lean_dec(v___x_1720_);
                            v___x_1740_ = crate::leanh::lean_box(0);
                            v_isShared_1741_ = v_isSharedCheck_1745_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1727_ = crate::leanh::lean_box(0);
                v___x_1728_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1729_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1722_, v___x_1728_);
                v___x_1730_ = lean_array_push(v_snd_1718_, v___x_1729_);
                if v_isShared_1726_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1725_, 1, v___x_1730_);
                    crate::leanh::lean_ctor_set(v___x_1725_, 0, v___x_1727_);
                    v___x_1732_ = v___x_1725_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1730_);
                    v___x_1732_ = v_reuseFailAlloc_1736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1733_ = 1usize;
                v___x_1734_ = lean_usize_add(v_i_1707_, v___x_1733_);
                v_i_1707_ = v___x_1734_;
                v_b_1708_ = v___x_1732_;
                v___y_1709_ = v_snd_1723_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_1741_ == 0 {
                    v___x_1743_ = v___x_1740_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
                    v___x_1743_ = v_reuseFailAlloc_1744_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4___boxed(
    mut v_as_1746_: *mut crate::leanh::LeanObject,
    mut v_sz_1747_: *mut crate::leanh::LeanObject,
    mut v_i_1748_: *mut crate::leanh::LeanObject,
    mut v_b_1749_: *mut crate::leanh::LeanObject,
    mut v___y_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
    mut v___y_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
    mut v___y_1755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1756_: usize = 0;
    let mut v_i_boxed_1757_: usize = 0;
    let mut v_res_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1756_ = crate::leanh::lean_unbox_usize(v_sz_1747_);
    crate::leanh::lean_dec(v_sz_1747_);
    v_i_boxed_1757_ = crate::leanh::lean_unbox_usize(v_i_1748_);
    crate::leanh::lean_dec(v_i_1748_);
    v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_1746_, v_sz_boxed_1756_, v_i_boxed_1757_, v_b_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
    crate::leanh::lean_dec(v___y_1754_);
    crate::leanh::lean_dec_ref(v___y_1753_);
    crate::leanh::lean_dec(v___y_1752_);
    crate::leanh::lean_dec_ref(v___y_1751_);
    crate::leanh::lean_dec_ref(v_as_1746_);
    return v_res_1758_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(
    mut v_as_1759_: *mut crate::leanh::LeanObject,
    mut v_sz_1760_: usize,
    mut v_i_1761_: usize,
    mut v_b_1762_: *mut crate::leanh::LeanObject,
    mut v___y_1763_: *mut crate::leanh::LeanObject,
    mut v___y_1764_: *mut crate::leanh::LeanObject,
    mut v___y_1765_: *mut crate::leanh::LeanObject,
    mut v___y_1766_: *mut crate::leanh::LeanObject,
    mut v___y_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: usize = 0;
    let mut v___x_1788_: usize = 0;
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v_a_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1769_ = lean_usize_dec_lt(v_i_1761_, v_sz_1760_);
                if v___x_1769_ == 0 {
                    v___x_1770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1770_, 0, v_b_1762_);
                    crate::leanh::lean_ctor_set(v___x_1770_, 1, v___y_1763_);
                    v___x_1771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1771_, 0, v___x_1770_);
                    return v___x_1771_;
                } else {
                    v_snd_1772_ = crate::leanh::lean_ctor_get(v_b_1762_, 1);
                    crate::leanh::lean_inc(v_snd_1772_);
                    crate::leanh::lean_dec_ref(v_b_1762_);
                    v_a_1773_ = lean_array_uget_borrowed(v_as_1759_, v_i_1761_);
                    crate::leanh::lean_inc(v_a_1773_);
                    v___x_1774_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1773_, v___y_1763_);
                    if crate::leanh::lean_obj_tag(v___x_1774_) == 0 {
                        v_a_1775_ = crate::leanh::lean_ctor_get(v___x_1774_, 0);
                        crate::leanh::lean_inc(v_a_1775_);
                        crate::leanh::lean_dec_ref_known(v___x_1774_, 1);
                        v_fst_1776_ = crate::leanh::lean_ctor_get(v_a_1775_, 0);
                        v_snd_1777_ = crate::leanh::lean_ctor_get(v_a_1775_, 1);
                        v_isSharedCheck_1791_ = (!crate::leanh::lean_is_exclusive(v_a_1775_)) as u8;
                        if v_isSharedCheck_1791_ == 0 {
                            v___x_1779_ = v_a_1775_;
                            v_isShared_1780_ = v_isSharedCheck_1791_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1777_);
                            crate::leanh::lean_inc(v_fst_1776_);
                            crate::leanh::lean_dec(v_a_1775_);
                            v___x_1779_ = crate::leanh::lean_box(0);
                            v_isShared_1780_ = v_isSharedCheck_1791_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_1772_);
                        v_a_1792_ = crate::leanh::lean_ctor_get(v___x_1774_, 0);
                        v_isSharedCheck_1799_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1774_)) as u8;
                        if v_isSharedCheck_1799_ == 0 {
                            v___x_1794_ = v___x_1774_;
                            v_isShared_1795_ = v_isSharedCheck_1799_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1792_);
                            crate::leanh::lean_dec(v___x_1774_);
                            v___x_1794_ = crate::leanh::lean_box(0);
                            v_isShared_1795_ = v_isSharedCheck_1799_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1781_ = crate::leanh::lean_box(0);
                v___x_1782_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1783_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1776_, v___x_1782_);
                v___x_1784_ = lean_array_push(v_snd_1772_, v___x_1783_);
                if v_isShared_1780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1779_, 1, v___x_1784_);
                    crate::leanh::lean_ctor_set(v___x_1779_, 0, v___x_1781_);
                    v___x_1786_ = v___x_1779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1784_);
                    v___x_1786_ = v_reuseFailAlloc_1790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1787_ = 1usize;
                v___x_1788_ = lean_usize_add(v_i_1761_, v___x_1787_);
                v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_1759_, v_sz_1760_, v___x_1788_, v___x_1786_, v_snd_1777_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
                return v___x_1789_;
            }
            3 => {
                if v_isShared_1795_ == 0 {
                    v___x_1797_ = v___x_1794_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
                    v___x_1797_ = v_reuseFailAlloc_1798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3___boxed(
    mut v_as_1800_: *mut crate::leanh::LeanObject,
    mut v_sz_1801_: *mut crate::leanh::LeanObject,
    mut v_i_1802_: *mut crate::leanh::LeanObject,
    mut v_b_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1810_: usize = 0;
    let mut v_i_boxed_1811_: usize = 0;
    let mut v_res_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1810_ = crate::leanh::lean_unbox_usize(v_sz_1801_);
    crate::leanh::lean_dec(v_sz_1801_);
    v_i_boxed_1811_ = crate::leanh::lean_unbox_usize(v_i_1802_);
    crate::leanh::lean_dec(v_i_1802_);
    v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_as_1800_, v_sz_boxed_1810_, v_i_boxed_1811_, v_b_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
    crate::leanh::lean_dec(v___y_1808_);
    crate::leanh::lean_dec_ref(v___y_1807_);
    crate::leanh::lean_dec(v___y_1806_);
    crate::leanh::lean_dec_ref(v___y_1805_);
    crate::leanh::lean_dec_ref(v_as_1800_);
    return v_res_1812_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(
    mut v_init_1813_: *mut crate::leanh::LeanObject,
    mut v_n_1814_: *mut crate::leanh::LeanObject,
    mut v_b_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
    mut v___y_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1825_: usize = 0;
    let mut v___x_1826_: usize = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v_fst_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1838_: u8 = 0;
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v_unused_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v_snd_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1859_: u8 = 0;
    let mut v_unused_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_a_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_vs_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1874_: usize = 0;
    let mut v___x_1875_: usize = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v_fst_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1887_: u8 = 0;
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut v_unused_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1899_: u8 = 0;
    let mut v_snd_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut v_unused_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_a_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_1814_) == 0 {
                    v_cs_1822_ = crate::leanh::lean_ctor_get(v_n_1814_, 0);
                    v___x_1823_ = crate::leanh::lean_box(0);
                    v___x_1824_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1824_, 0, v___x_1823_);
                    crate::leanh::lean_ctor_set(v___x_1824_, 1, v_b_1815_);
                    v_sz_1825_ = lean_array_size(v_cs_1822_);
                    v___x_1826_ = 0usize;
                    v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_1813_, v_cs_1822_, v_sz_1825_, v___x_1826_, v___x_1824_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
                    if crate::leanh::lean_obj_tag(v___x_1827_) == 0 {
                        v_a_1828_ = crate::leanh::lean_ctor_get(v___x_1827_, 0);
                        v_isSharedCheck_1862_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1827_)) as u8;
                        if v_isSharedCheck_1862_ == 0 {
                            v___x_1830_ = v___x_1827_;
                            v_isShared_1831_ = v_isSharedCheck_1862_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1828_);
                            crate::leanh::lean_dec(v___x_1827_);
                            v___x_1830_ = crate::leanh::lean_box(0);
                            v_isShared_1831_ = v_isSharedCheck_1862_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1863_ = crate::leanh::lean_ctor_get(v___x_1827_, 0);
                        v_isSharedCheck_1870_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1827_)) as u8;
                        if v_isSharedCheck_1870_ == 0 {
                            v___x_1865_ = v___x_1827_;
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1863_);
                            crate::leanh::lean_dec(v___x_1827_);
                            v___x_1865_ = crate::leanh::lean_box(0);
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_vs_1871_ = crate::leanh::lean_ctor_get(v_n_1814_, 0);
                    v___x_1872_ = crate::leanh::lean_box(0);
                    v___x_1873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                    crate::leanh::lean_ctor_set(v___x_1873_, 1, v_b_1815_);
                    v_sz_1874_ = lean_array_size(v_vs_1871_);
                    v___x_1875_ = 0usize;
                    v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_vs_1871_, v_sz_1874_, v___x_1875_, v___x_1873_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
                    if crate::leanh::lean_obj_tag(v___x_1876_) == 0 {
                        v_a_1877_ = crate::leanh::lean_ctor_get(v___x_1876_, 0);
                        v_isSharedCheck_1911_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1876_)) as u8;
                        if v_isSharedCheck_1911_ == 0 {
                            v___x_1879_ = v___x_1876_;
                            v_isShared_1880_ = v_isSharedCheck_1911_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1877_);
                            crate::leanh::lean_dec(v___x_1876_);
                            v___x_1879_ = crate::leanh::lean_box(0);
                            v_isShared_1880_ = v_isSharedCheck_1911_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_a_1912_ = crate::leanh::lean_ctor_get(v___x_1876_, 0);
                        v_isSharedCheck_1919_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1876_)) as u8;
                        if v_isSharedCheck_1919_ == 0 {
                            v___x_1914_ = v___x_1876_;
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1912_);
                            crate::leanh::lean_dec(v___x_1876_);
                            v___x_1914_ = crate::leanh::lean_box(0);
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1832_ = crate::leanh::lean_ctor_get(v_a_1828_, 0);
                crate::leanh::lean_inc(v_fst_1832_);
                v_fst_1833_ = crate::leanh::lean_ctor_get(v_fst_1832_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1833_) == 0 {
                    v_snd_1834_ = crate::leanh::lean_ctor_get(v_a_1828_, 1);
                    crate::leanh::lean_inc(v_snd_1834_);
                    crate::leanh::lean_dec(v_a_1828_);
                    v_snd_1835_ = crate::leanh::lean_ctor_get(v_fst_1832_, 1);
                    v_isSharedCheck_1846_ = (!crate::leanh::lean_is_exclusive(v_fst_1832_)) as u8;
                    if v_isSharedCheck_1846_ == 0 {
                        v_unused_1847_ = crate::leanh::lean_ctor_get(v_fst_1832_, 0);
                        crate::leanh::lean_dec(v_unused_1847_);
                        v___x_1837_ = v_fst_1832_;
                        v_isShared_1838_ = v_isSharedCheck_1846_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1835_);
                        crate::leanh::lean_dec(v_fst_1832_);
                        v___x_1837_ = crate::leanh::lean_box(0);
                        v_isShared_1838_ = v_isSharedCheck_1846_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1833_);
                    v_isSharedCheck_1859_ = (!crate::leanh::lean_is_exclusive(v_fst_1832_)) as u8;
                    if v_isSharedCheck_1859_ == 0 {
                        v_unused_1860_ = crate::leanh::lean_ctor_get(v_fst_1832_, 1);
                        crate::leanh::lean_dec(v_unused_1860_);
                        v_unused_1861_ = crate::leanh::lean_ctor_get(v_fst_1832_, 0);
                        crate::leanh::lean_dec(v_unused_1861_);
                        v___x_1849_ = v_fst_1832_;
                        v_isShared_1850_ = v_isSharedCheck_1859_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_1832_);
                        v___x_1849_ = crate::leanh::lean_box(0);
                        v_isShared_1850_ = v_isSharedCheck_1859_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1839_, 0, v_snd_1835_);
                if v_isShared_1838_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1837_, 1, v_snd_1834_);
                    crate::leanh::lean_ctor_set(v___x_1837_, 0, v___x_1839_);
                    v___x_1841_ = v___x_1837_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_snd_1834_);
                    v___x_1841_ = v_reuseFailAlloc_1845_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1830_, 0, v___x_1841_);
                    v___x_1843_ = v___x_1830_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1844_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
                    v___x_1843_ = v_reuseFailAlloc_1844_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1843_;
            }
            5 => {
                v_snd_1851_ = crate::leanh::lean_ctor_get(v_a_1828_, 1);
                crate::leanh::lean_inc(v_snd_1851_);
                crate::leanh::lean_dec(v_a_1828_);
                v_val_1852_ = crate::leanh::lean_ctor_get(v_fst_1833_, 0);
                crate::leanh::lean_inc(v_val_1852_);
                crate::leanh::lean_dec_ref_known(v_fst_1833_, 1);
                if v_isShared_1850_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1849_, 1, v_snd_1851_);
                    crate::leanh::lean_ctor_set(v___x_1849_, 0, v_val_1852_);
                    v___x_1854_ = v___x_1849_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_val_1852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_snd_1851_);
                    v___x_1854_ = v_reuseFailAlloc_1858_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1830_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1830_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1856_;
            }
            8 => {
                if v_isShared_1866_ == 0 {
                    v___x_1868_ = v___x_1865_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
                    v___x_1868_ = v_reuseFailAlloc_1869_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1868_;
            }
            10 => {
                v_fst_1881_ = crate::leanh::lean_ctor_get(v_a_1877_, 0);
                crate::leanh::lean_inc(v_fst_1881_);
                v_fst_1882_ = crate::leanh::lean_ctor_get(v_fst_1881_, 0);
                if crate::leanh::lean_obj_tag(v_fst_1882_) == 0 {
                    v_snd_1883_ = crate::leanh::lean_ctor_get(v_a_1877_, 1);
                    crate::leanh::lean_inc(v_snd_1883_);
                    crate::leanh::lean_dec(v_a_1877_);
                    v_snd_1884_ = crate::leanh::lean_ctor_get(v_fst_1881_, 1);
                    v_isSharedCheck_1895_ = (!crate::leanh::lean_is_exclusive(v_fst_1881_)) as u8;
                    if v_isSharedCheck_1895_ == 0 {
                        v_unused_1896_ = crate::leanh::lean_ctor_get(v_fst_1881_, 0);
                        crate::leanh::lean_dec(v_unused_1896_);
                        v___x_1886_ = v_fst_1881_;
                        v_isShared_1887_ = v_isSharedCheck_1895_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1884_);
                        crate::leanh::lean_dec(v_fst_1881_);
                        v___x_1886_ = crate::leanh::lean_box(0);
                        v_isShared_1887_ = v_isSharedCheck_1895_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_1882_);
                    v_isSharedCheck_1908_ = (!crate::leanh::lean_is_exclusive(v_fst_1881_)) as u8;
                    if v_isSharedCheck_1908_ == 0 {
                        v_unused_1909_ = crate::leanh::lean_ctor_get(v_fst_1881_, 1);
                        crate::leanh::lean_dec(v_unused_1909_);
                        v_unused_1910_ = crate::leanh::lean_ctor_get(v_fst_1881_, 0);
                        crate::leanh::lean_dec(v_unused_1910_);
                        v___x_1898_ = v_fst_1881_;
                        v_isShared_1899_ = v_isSharedCheck_1908_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_1881_);
                        v___x_1898_ = crate::leanh::lean_box(0);
                        v_isShared_1899_ = v_isSharedCheck_1908_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v___x_1888_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1888_, 0, v_snd_1884_);
                if v_isShared_1887_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1886_, 1, v_snd_1883_);
                    crate::leanh::lean_ctor_set(v___x_1886_, 0, v___x_1888_);
                    v___x_1890_ = v___x_1886_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1894_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_snd_1883_);
                    v___x_1890_ = v_reuseFailAlloc_1894_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1880_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1879_, 0, v___x_1890_);
                    v___x_1892_ = v___x_1879_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1893_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
                    v___x_1892_ = v_reuseFailAlloc_1893_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1892_;
            }
            14 => {
                v_snd_1900_ = crate::leanh::lean_ctor_get(v_a_1877_, 1);
                crate::leanh::lean_inc(v_snd_1900_);
                crate::leanh::lean_dec(v_a_1877_);
                v_val_1901_ = crate::leanh::lean_ctor_get(v_fst_1882_, 0);
                crate::leanh::lean_inc(v_val_1901_);
                crate::leanh::lean_dec_ref_known(v_fst_1882_, 1);
                if v_isShared_1899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1898_, 1, v_snd_1900_);
                    crate::leanh::lean_ctor_set(v___x_1898_, 0, v_val_1901_);
                    v___x_1903_ = v___x_1898_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_val_1901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_snd_1900_);
                    v___x_1903_ = v_reuseFailAlloc_1907_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1880_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1879_, 0, v___x_1903_);
                    v___x_1905_ = v___x_1879_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
                    v___x_1905_ = v_reuseFailAlloc_1906_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1905_;
            }
            17 => {
                if v_isShared_1915_ == 0 {
                    v___x_1917_ = v___x_1914_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
                    v___x_1917_ = v_reuseFailAlloc_1918_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(
    mut v_init_1920_: *mut crate::leanh::LeanObject,
    mut v_as_1921_: *mut crate::leanh::LeanObject,
    mut v_sz_1922_: usize,
    mut v_i_1923_: usize,
    mut v_b_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1931_: u8 = 0;
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v_a_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1943_: u8 = 0;
    let mut v_fst_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v_unused_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v_a_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: usize = 0;
    let mut v___x_1970_: usize = 0;
    let mut v_reuseFailAlloc_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut v_unused_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut v_a_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_isSharedCheck_1984_: u8 = 0;
    let mut v_unused_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1931_ = lean_usize_dec_lt(v_i_1923_, v_sz_1922_);
                if v___x_1931_ == 0 {
                    v___x_1932_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1932_, 0, v_b_1924_);
                    crate::leanh::lean_ctor_set(v___x_1932_, 1, v___y_1925_);
                    v___x_1933_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1933_, 0, v___x_1932_);
                    return v___x_1933_;
                } else {
                    v_snd_1934_ = crate::leanh::lean_ctor_get(v_b_1924_, 1);
                    v_isSharedCheck_1984_ = (!crate::leanh::lean_is_exclusive(v_b_1924_)) as u8;
                    if v_isSharedCheck_1984_ == 0 {
                        v_unused_1985_ = crate::leanh::lean_ctor_get(v_b_1924_, 0);
                        crate::leanh::lean_dec(v_unused_1985_);
                        v___x_1936_ = v_b_1924_;
                        v_isShared_1937_ = v_isSharedCheck_1984_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1934_);
                        crate::leanh::lean_dec(v_b_1924_);
                        v___x_1936_ = crate::leanh::lean_box(0);
                        v_isShared_1937_ = v_isSharedCheck_1984_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1938_ = lean_array_uget_borrowed(v_as_1921_, v_i_1923_);
                crate::leanh::lean_inc(v_snd_1934_);
                v___x_1939_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_1920_, v_a_1938_, v_snd_1934_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
                if crate::leanh::lean_obj_tag(v___x_1939_) == 0 {
                    v_a_1940_ = crate::leanh::lean_ctor_get(v___x_1939_, 0);
                    v_isSharedCheck_1975_ = (!crate::leanh::lean_is_exclusive(v___x_1939_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1942_ = v___x_1939_;
                        v_isShared_1943_ = v_isSharedCheck_1975_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1940_);
                        crate::leanh::lean_dec(v___x_1939_);
                        v___x_1942_ = crate::leanh::lean_box(0);
                        v_isShared_1943_ = v_isSharedCheck_1975_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1936_);
                    crate::leanh::lean_dec(v_snd_1934_);
                    v_a_1976_ = crate::leanh::lean_ctor_get(v___x_1939_, 0);
                    v_isSharedCheck_1983_ = (!crate::leanh::lean_is_exclusive(v___x_1939_)) as u8;
                    if v_isSharedCheck_1983_ == 0 {
                        v___x_1978_ = v___x_1939_;
                        v_isShared_1979_ = v_isSharedCheck_1983_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1976_);
                        crate::leanh::lean_dec(v___x_1939_);
                        v___x_1978_ = crate::leanh::lean_box(0);
                        v_isShared_1979_ = v_isSharedCheck_1983_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1944_ = crate::leanh::lean_ctor_get(v_a_1940_, 0);
                crate::leanh::lean_inc(v_fst_1944_);
                if crate::leanh::lean_obj_tag(v_fst_1944_) == 0 {
                    v_snd_1945_ = crate::leanh::lean_ctor_get(v_a_1940_, 1);
                    v_isSharedCheck_1959_ = (!crate::leanh::lean_is_exclusive(v_a_1940_)) as u8;
                    if v_isSharedCheck_1959_ == 0 {
                        v_unused_1960_ = crate::leanh::lean_ctor_get(v_a_1940_, 0);
                        crate::leanh::lean_dec(v_unused_1960_);
                        v___x_1947_ = v_a_1940_;
                        v_isShared_1948_ = v_isSharedCheck_1959_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1945_);
                        crate::leanh::lean_dec(v_a_1940_);
                        v___x_1947_ = crate::leanh::lean_box(0);
                        v_isShared_1948_ = v_isSharedCheck_1959_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1942_);
                    crate::leanh::lean_del_object(v___x_1936_);
                    crate::leanh::lean_dec(v_snd_1934_);
                    v_snd_1961_ = crate::leanh::lean_ctor_get(v_a_1940_, 1);
                    v_isSharedCheck_1973_ = (!crate::leanh::lean_is_exclusive(v_a_1940_)) as u8;
                    if v_isSharedCheck_1973_ == 0 {
                        v_unused_1974_ = crate::leanh::lean_ctor_get(v_a_1940_, 0);
                        crate::leanh::lean_dec(v_unused_1974_);
                        v___x_1963_ = v_a_1940_;
                        v_isShared_1964_ = v_isSharedCheck_1973_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1961_);
                        crate::leanh::lean_dec(v_a_1940_);
                        v___x_1963_ = crate::leanh::lean_box(0);
                        v_isShared_1964_ = v_isSharedCheck_1973_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1949_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1949_, 0, v_fst_1944_);
                if v_isShared_1948_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1947_, 1, v_snd_1934_);
                    crate::leanh::lean_ctor_set(v___x_1947_, 0, v___x_1949_);
                    v___x_1951_ = v___x_1947_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_snd_1934_);
                    v___x_1951_ = v_reuseFailAlloc_1958_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1937_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1936_, 1, v_snd_1945_);
                    crate::leanh::lean_ctor_set(v___x_1936_, 0, v___x_1951_);
                    v___x_1953_ = v___x_1936_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_snd_1945_);
                    v___x_1953_ = v_reuseFailAlloc_1957_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1943_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1942_, 0, v___x_1953_);
                    v___x_1955_ = v___x_1942_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
                    v___x_1955_ = v_reuseFailAlloc_1956_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1955_;
            }
            7 => {
                v_a_1965_ = crate::leanh::lean_ctor_get(v_fst_1944_, 0);
                crate::leanh::lean_inc(v_a_1965_);
                crate::leanh::lean_dec_ref_known(v_fst_1944_, 1);
                v___x_1966_ = crate::leanh::lean_box(0);
                if v_isShared_1964_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1963_, 1, v_a_1965_);
                    crate::leanh::lean_ctor_set(v___x_1963_, 0, v___x_1966_);
                    v___x_1968_ = v___x_1963_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1966_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_a_1965_);
                    v___x_1968_ = v_reuseFailAlloc_1972_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1969_ = 1usize;
                v___x_1970_ = lean_usize_add(v_i_1923_, v___x_1969_);
                v_i_1923_ = v___x_1970_;
                v_b_1924_ = v___x_1968_;
                v___y_1925_ = v_snd_1961_;
                state = 0;
                continue;
            }
            9 => {
                if v_isShared_1979_ == 0 {
                    v___x_1981_ = v___x_1978_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
                    v___x_1981_ = v_reuseFailAlloc_1982_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2___boxed(
    mut v_init_1986_: *mut crate::leanh::LeanObject,
    mut v_as_1987_: *mut crate::leanh::LeanObject,
    mut v_sz_1988_: *mut crate::leanh::LeanObject,
    mut v_i_1989_: *mut crate::leanh::LeanObject,
    mut v_b_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
    mut v___y_1996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1997_: usize = 0;
    let mut v_i_boxed_1998_: usize = 0;
    let mut v_res_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1997_ = crate::leanh::lean_unbox_usize(v_sz_1988_);
    crate::leanh::lean_dec(v_sz_1988_);
    v_i_boxed_1998_ = crate::leanh::lean_unbox_usize(v_i_1989_);
    crate::leanh::lean_dec(v_i_1989_);
    v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_1986_, v_as_1987_, v_sz_boxed_1997_, v_i_boxed_1998_, v_b_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
    crate::leanh::lean_dec(v___y_1995_);
    crate::leanh::lean_dec_ref(v___y_1994_);
    crate::leanh::lean_dec(v___y_1993_);
    crate::leanh::lean_dec_ref(v___y_1992_);
    crate::leanh::lean_dec_ref(v_as_1987_);
    crate::leanh::lean_dec_ref(v_init_1986_);
    return v_res_1999_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1___boxed(
    mut v_init_2000_: *mut crate::leanh::LeanObject,
    mut v_n_2001_: *mut crate::leanh::LeanObject,
    mut v_b_2002_: *mut crate::leanh::LeanObject,
    mut v___y_2003_: *mut crate::leanh::LeanObject,
    mut v___y_2004_: *mut crate::leanh::LeanObject,
    mut v___y_2005_: *mut crate::leanh::LeanObject,
    mut v___y_2006_: *mut crate::leanh::LeanObject,
    mut v___y_2007_: *mut crate::leanh::LeanObject,
    mut v___y_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_2000_, v_n_2001_, v_b_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
    crate::leanh::lean_dec(v___y_2007_);
    crate::leanh::lean_dec_ref(v___y_2006_);
    crate::leanh::lean_dec(v___y_2005_);
    crate::leanh::lean_dec_ref(v___y_2004_);
    crate::leanh::lean_dec_ref(v_n_2001_);
    crate::leanh::lean_dec_ref(v_init_2000_);
    return v_res_2009_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(
    mut v_t_2010_: *mut crate::leanh::LeanObject,
    mut v_init_2011_: *mut crate::leanh::LeanObject,
    mut v___y_2012_: *mut crate::leanh::LeanObject,
    mut v___y_2013_: *mut crate::leanh::LeanObject,
    mut v___y_2014_: *mut crate::leanh::LeanObject,
    mut v___y_2015_: *mut crate::leanh::LeanObject,
    mut v___y_2016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2033_: u8 = 0;
    let mut v_a_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2038_: usize = 0;
    let mut v___x_2039_: usize = 0;
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2044_: u8 = 0;
    let mut v_fst_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_unused_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2062_: u8 = 0;
    let mut v_a_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2066_: u8 = 0;
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_reuseFailAlloc_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v_unused_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2023_ = crate::leanh::lean_ctor_get(v_t_2010_, 0);
                v_tail_2024_ = crate::leanh::lean_ctor_get(v_t_2010_, 1);
                crate::leanh::lean_inc_ref(v_init_2011_);
                v___x_2025_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_2011_, v_root_2023_, v_init_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
                crate::leanh::lean_dec_ref(v_init_2011_);
                if crate::leanh::lean_obj_tag(v___x_2025_) == 0 {
                    v_a_2026_ = crate::leanh::lean_ctor_get(v___x_2025_, 0);
                    crate::leanh::lean_inc(v_a_2026_);
                    crate::leanh::lean_dec_ref_known(v___x_2025_, 1);
                    v_fst_2027_ = crate::leanh::lean_ctor_get(v_a_2026_, 0);
                    crate::leanh::lean_inc(v_fst_2027_);
                    if crate::leanh::lean_obj_tag(v_fst_2027_) == 0 {
                        v_snd_2028_ = crate::leanh::lean_ctor_get(v_a_2026_, 1);
                        crate::leanh::lean_inc(v_snd_2028_);
                        crate::leanh::lean_dec(v_a_2026_);
                        v_a_2029_ = crate::leanh::lean_ctor_get(v_fst_2027_, 0);
                        crate::leanh::lean_inc(v_a_2029_);
                        crate::leanh::lean_dec_ref_known(v_fst_2027_, 1);
                        v_b_2019_ = v_a_2029_;
                        v___y_2020_ = v_snd_2028_;
                        state = 1;
                        continue;
                    } else {
                        v_snd_2030_ = crate::leanh::lean_ctor_get(v_a_2026_, 1);
                        v_isSharedCheck_2072_ = (!crate::leanh::lean_is_exclusive(v_a_2026_)) as u8;
                        if v_isSharedCheck_2072_ == 0 {
                            v_unused_2073_ = crate::leanh::lean_ctor_get(v_a_2026_, 0);
                            crate::leanh::lean_dec(v_unused_2073_);
                            v___x_2032_ = v_a_2026_;
                            v_isShared_2033_ = v_isSharedCheck_2072_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_2030_);
                            crate::leanh::lean_dec(v_a_2026_);
                            v___x_2032_ = crate::leanh::lean_box(0);
                            v_isShared_2033_ = v_isSharedCheck_2072_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_a_2074_ = crate::leanh::lean_ctor_get(v___x_2025_, 0);
                    v_isSharedCheck_2081_ = (!crate::leanh::lean_is_exclusive(v___x_2025_)) as u8;
                    if v_isSharedCheck_2081_ == 0 {
                        v___x_2076_ = v___x_2025_;
                        v_isShared_2077_ = v_isSharedCheck_2081_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2074_);
                        crate::leanh::lean_dec(v___x_2025_);
                        v___x_2076_ = crate::leanh::lean_box(0);
                        v_isShared_2077_ = v_isSharedCheck_2081_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2021_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2021_, 0, v_b_2019_);
                crate::leanh::lean_ctor_set(v___x_2021_, 1, v___y_2020_);
                v___x_2022_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2022_, 0, v___x_2021_);
                return v___x_2022_;
            }
            2 => {
                v_a_2034_ = crate::leanh::lean_ctor_get(v_fst_2027_, 0);
                crate::leanh::lean_inc(v_a_2034_);
                crate::leanh::lean_dec_ref_known(v_fst_2027_, 1);
                v___x_2035_ = crate::leanh::lean_box(0);
                if v_isShared_2033_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2032_, 1, v_a_2034_);
                    crate::leanh::lean_ctor_set(v___x_2032_, 0, v___x_2035_);
                    v___x_2037_ = v___x_2032_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2071_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_a_2034_);
                    v___x_2037_ = v_reuseFailAlloc_2071_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_sz_2038_ = lean_array_size(v_tail_2024_);
                v___x_2039_ = 0usize;
                v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_tail_2024_, v_sz_2038_, v___x_2039_, v___x_2037_, v_snd_2030_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
                if crate::leanh::lean_obj_tag(v___x_2040_) == 0 {
                    v_a_2041_ = crate::leanh::lean_ctor_get(v___x_2040_, 0);
                    v_isSharedCheck_2062_ = (!crate::leanh::lean_is_exclusive(v___x_2040_)) as u8;
                    if v_isSharedCheck_2062_ == 0 {
                        v___x_2043_ = v___x_2040_;
                        v_isShared_2044_ = v_isSharedCheck_2062_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2041_);
                        crate::leanh::lean_dec(v___x_2040_);
                        v___x_2043_ = crate::leanh::lean_box(0);
                        v_isShared_2044_ = v_isSharedCheck_2062_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2063_ = crate::leanh::lean_ctor_get(v___x_2040_, 0);
                    v_isSharedCheck_2070_ = (!crate::leanh::lean_is_exclusive(v___x_2040_)) as u8;
                    if v_isSharedCheck_2070_ == 0 {
                        v___x_2065_ = v___x_2040_;
                        v_isShared_2066_ = v_isSharedCheck_2070_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2063_);
                        crate::leanh::lean_dec(v___x_2040_);
                        v___x_2065_ = crate::leanh::lean_box(0);
                        v_isShared_2066_ = v_isSharedCheck_2070_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2045_ = crate::leanh::lean_ctor_get(v_a_2041_, 0);
                crate::leanh::lean_inc(v_fst_2045_);
                v_fst_2046_ = crate::leanh::lean_ctor_get(v_fst_2045_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2046_) == 0 {
                    v_snd_2047_ = crate::leanh::lean_ctor_get(v_a_2041_, 1);
                    crate::leanh::lean_inc(v_snd_2047_);
                    crate::leanh::lean_dec(v_a_2041_);
                    v_snd_2048_ = crate::leanh::lean_ctor_get(v_fst_2045_, 1);
                    v_isSharedCheck_2058_ = (!crate::leanh::lean_is_exclusive(v_fst_2045_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v_unused_2059_ = crate::leanh::lean_ctor_get(v_fst_2045_, 0);
                        crate::leanh::lean_dec(v_unused_2059_);
                        v___x_2050_ = v_fst_2045_;
                        v_isShared_2051_ = v_isSharedCheck_2058_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2048_);
                        crate::leanh::lean_dec(v_fst_2045_);
                        v___x_2050_ = crate::leanh::lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2058_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2046_);
                    crate::leanh::lean_dec(v_fst_2045_);
                    crate::leanh::lean_del_object(v___x_2043_);
                    v_snd_2060_ = crate::leanh::lean_ctor_get(v_a_2041_, 1);
                    crate::leanh::lean_inc(v_snd_2060_);
                    crate::leanh::lean_dec(v_a_2041_);
                    v_val_2061_ = crate::leanh::lean_ctor_get(v_fst_2046_, 0);
                    crate::leanh::lean_inc(v_val_2061_);
                    crate::leanh::lean_dec_ref_known(v_fst_2046_, 1);
                    v_b_2019_ = v_val_2061_;
                    v___y_2020_ = v_snd_2060_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_2051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2050_, 1, v_snd_2047_);
                    crate::leanh::lean_ctor_set(v___x_2050_, 0, v_snd_2048_);
                    v___x_2053_ = v___x_2050_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_snd_2048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_snd_2047_);
                    v___x_2053_ = v_reuseFailAlloc_2057_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2044_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2043_, 0, v___x_2053_);
                    v___x_2055_ = v___x_2043_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
                    v___x_2055_ = v_reuseFailAlloc_2056_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2055_;
            }
            8 => {
                if v_isShared_2066_ == 0 {
                    v___x_2068_ = v___x_2065_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
                    v___x_2068_ = v_reuseFailAlloc_2069_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2068_;
            }
            10 => {
                if v_isShared_2077_ == 0 {
                    v___x_2079_ = v___x_2076_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2080_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
                    v___x_2079_ = v_reuseFailAlloc_2080_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2079_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1___boxed(
    mut v_t_2082_: *mut crate::leanh::LeanObject,
    mut v_init_2083_: *mut crate::leanh::LeanObject,
    mut v___y_2084_: *mut crate::leanh::LeanObject,
    mut v___y_2085_: *mut crate::leanh::LeanObject,
    mut v___y_2086_: *mut crate::leanh::LeanObject,
    mut v___y_2087_: *mut crate::leanh::LeanObject,
    mut v___y_2088_: *mut crate::leanh::LeanObject,
    mut v___y_2089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_t_2082_, v_init_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
    crate::leanh::lean_dec(v___y_2088_);
    crate::leanh::lean_dec_ref(v___y_2087_);
    crate::leanh::lean_dec(v___y_2086_);
    crate::leanh::lean_dec_ref(v___y_2085_);
    crate::leanh::lean_dec_ref(v_t_2082_);
    return v_res_2090_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2095_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0;
    v___x_2096_ = lean_mk_thunk(v___f_2095_);
    return v___x_2096_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(
    mut v_a_2097_: *mut crate::leanh::LeanObject,
    mut v_a_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_diseqs_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v_fst_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut v_a_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2129_: u8 = 0;
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_diseqs_2103_ = crate::leanh::lean_ctor_get(v_a_2097_, 16);
                crate::leanh::lean_inc_ref(v_diseqs_2103_);
                v_diseqs_2104_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
                v___x_2105_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_diseqs_2103_, v_diseqs_2104_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
                crate::leanh::lean_dec_ref(v_diseqs_2103_);
                if crate::leanh::lean_obj_tag(v___x_2105_) == 0 {
                    v_a_2106_ = crate::leanh::lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2125_ = (!crate::leanh::lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2125_ == 0 {
                        v___x_2108_ = v___x_2105_;
                        v_isShared_2109_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2106_);
                        crate::leanh::lean_dec(v___x_2105_);
                        v___x_2108_ = crate::leanh::lean_box(0);
                        v_isShared_2109_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2126_ = crate::leanh::lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2133_ = (!crate::leanh::lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2133_ == 0 {
                        v___x_2128_ = v___x_2105_;
                        v_isShared_2129_ = v_isSharedCheck_2133_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2126_);
                        crate::leanh::lean_dec(v___x_2105_);
                        v___x_2128_ = crate::leanh::lean_box(0);
                        v_isShared_2129_ = v_isSharedCheck_2133_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2110_ = crate::leanh::lean_ctor_get(v_a_2106_, 0);
                v_snd_2111_ = crate::leanh::lean_ctor_get(v_a_2106_, 1);
                v_isSharedCheck_2124_ = (!crate::leanh::lean_is_exclusive(v_a_2106_)) as u8;
                if v_isSharedCheck_2124_ == 0 {
                    v___x_2113_ = v_a_2106_;
                    v_isShared_2114_ = v_isSharedCheck_2124_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2111_);
                    crate::leanh::lean_inc(v_fst_2110_);
                    crate::leanh::lean_dec(v_a_2106_);
                    v___x_2113_ = crate::leanh::lean_box(0);
                    v_isShared_2114_ = v_isSharedCheck_2124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2115_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2;
                v___x_2116_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3);
                v___x_2117_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
                        v___x_2115_,
                        v___x_2116_,
                        v_fst_2110_,
                    );
                if v_isShared_2114_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2113_, 0, v___x_2117_);
                    v___x_2119_ = v___x_2113_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_snd_2111_);
                    v___x_2119_ = v_reuseFailAlloc_2123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2109_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2108_, 0, v___x_2119_);
                    v___x_2121_ = v___x_2108_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2122_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
                    v___x_2121_ = v_reuseFailAlloc_2122_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2121_;
            }
            5 => {
                if v_isShared_2129_ == 0 {
                    v___x_2131_ = v___x_2128_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2132_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
                    v___x_2131_ = v_reuseFailAlloc_2132_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___boxed(
    mut v_a_2134_: *mut crate::leanh::LeanObject,
    mut v_a_2135_: *mut crate::leanh::LeanObject,
    mut v_a_2136_: *mut crate::leanh::LeanObject,
    mut v_a_2137_: *mut crate::leanh::LeanObject,
    mut v_a_2138_: *mut crate::leanh::LeanObject,
    mut v_a_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(
        v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_,
    );
    crate::leanh::lean_dec(v_a_2138_);
    crate::leanh::lean_dec_ref(v_a_2137_);
    crate::leanh::lean_dec(v_a_2136_);
    crate::leanh::lean_dec_ref(v_a_2135_);
    return v_res_2140_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(
    mut v_c_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2148_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_2141_, v___y_2142_);
    return v___x_2148_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___boxed(
    mut v_c_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
    mut v___y_2151_: *mut crate::leanh::LeanObject,
    mut v___y_2152_: *mut crate::leanh::LeanObject,
    mut v___y_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(v_c_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
    crate::leanh::lean_dec(v___y_2154_);
    crate::leanh::lean_dec_ref(v___y_2153_);
    crate::leanh::lean_dec(v___y_2152_);
    crate::leanh::lean_dec_ref(v___y_2151_);
    return v_res_2156_;
}
pub unsafe fn l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(
    mut v_e_2157_: *mut crate::leanh::LeanObject,
    mut v_cls_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: f64 = 0.0;
    let mut v___x_2161_: u8 = 0;
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = crate::leanh::lean_box(0);
    v___x_2160_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_2161_ = 1;
    v___x_2162_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_2163_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_2163_, 0, v_cls_2158_);
    crate::leanh::lean_ctor_set(v___x_2163_, 1, v___x_2159_);
    crate::leanh::lean_ctor_set(v___x_2163_, 2, v___x_2162_);
    crate::leanh::lean_ctor_set_float(
        v___x_2163_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_2160_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_2163_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_2160_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2163_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_2161_,
    );
    v___x_2164_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_2165_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2165_, 0, v___x_2163_);
    crate::leanh::lean_ctor_set(v___x_2165_, 1, v_e_2157_);
    crate::leanh::lean_ctor_set(v___x_2165_, 2, v___x_2164_);
    return v___x_2165_;
}
pub unsafe fn l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(
    mut v_e_2166_: *mut crate::leanh::LeanObject,
    mut v_cls_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: f64 = 0.0;
    let mut v___x_2170_: u8 = 0;
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2168_ = crate::leanh::lean_box(0);
    v___x_2169_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_2170_ = 1;
    v___x_2171_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_2172_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_2172_, 0, v_cls_2167_);
    crate::leanh::lean_ctor_set(v___x_2172_, 1, v___x_2168_);
    crate::leanh::lean_ctor_set(v___x_2172_, 2, v___x_2171_);
    crate::leanh::lean_ctor_set_float(
        v___x_2172_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_2169_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_2172_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_2169_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2172_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_2170_,
    );
    v___x_2173_ = l_Lean_stringToMessageData(v_e_2166_);
    v___x_2174_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_2175_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2175_, 0, v___x_2172_);
    crate::leanh::lean_ctor_set(v___x_2175_, 1, v___x_2173_);
    crate::leanh::lean_ctor_set(v___x_2175_, 2, v___x_2174_);
    return v___x_2175_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2177_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0;
    v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
    return v___x_2178_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2;
    v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0(
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v_x_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_op_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_op_2184_ = crate::leanh::lean_ctor_get(v___y_2182_, 3);
    crate::leanh::lean_inc_ref(v_op_2184_);
    crate::leanh::lean_dec_ref(v___y_2182_);
    v___x_2185_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1);
    v___x_2186_ = l_Lean_MessageData_ofExpr(v_op_2184_);
    v___x_2187_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2187_, 0, v___x_2185_);
    crate::leanh::lean_ctor_set(v___x_2187_, 1, v___x_2186_);
    v___x_2188_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
    v___x_2189_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2189_, 0, v___x_2187_);
    crate::leanh::lean_ctor_set(v___x_2189_, 1, v___x_2188_);
    return v___x_2189_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2193_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1;
    v___x_2194_ = l_Lean_MessageData_ofFormat(v___x_2193_);
    return v___x_2194_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1(
    mut v_x_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2);
    return v___x_2196_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2204_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2;
    v___x_2205_ = lean_mk_thunk(v___f_2204_);
    return v___x_2205_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2207_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6;
    v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
    return v___x_2208_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2210_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
    v___x_2211_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8;
    v___x_2212_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_2211_, v___x_2210_);
    return v___x_2212_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2214_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
    v___x_2215_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10;
    v___x_2216_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_2215_, v___x_2214_);
    return v___x_2216_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11);
    v_msgs_2218_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_2219_ = lean_array_push(v_msgs_2218_, v___x_2217_);
    return v___x_2219_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(
    mut v_a_2220_: *mut crate::leanh::LeanObject,
    mut v_a_2221_: *mut crate::leanh::LeanObject,
    mut v_a_2222_: *mut crate::leanh::LeanObject,
    mut v_a_2223_: *mut crate::leanh::LeanObject,
    mut v_a_2224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_msgs_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: u8 = 0;
    let mut v_neutral_x3f_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idempotentInst_x3f_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commInst_x3f_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idempotentInst_x3f_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2295_: u8 = 0;
    let mut v_isSharedCheck_2296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2235_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(
                        v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2235_) == 0 {
                    v_a_2236_ = crate::leanh::lean_ctor_get(v___x_2235_, 0);
                    crate::leanh::lean_inc(v_a_2236_);
                    crate::leanh::lean_dec_ref_known(v___x_2235_, 1);
                    v_fst_2237_ = crate::leanh::lean_ctor_get(v_a_2236_, 0);
                    v_snd_2238_ = crate::leanh::lean_ctor_get(v_a_2236_, 1);
                    v_isSharedCheck_2296_ = (!crate::leanh::lean_is_exclusive(v_a_2236_)) as u8;
                    if v_isSharedCheck_2296_ == 0 {
                        v___x_2240_ = v_a_2236_;
                        v_isShared_2241_ = v_isSharedCheck_2296_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2238_);
                        crate::leanh::lean_inc(v_fst_2237_);
                        crate::leanh::lean_dec(v_a_2236_);
                        v___x_2240_ = crate::leanh::lean_box(0);
                        v_isShared_2241_ = v_isSharedCheck_2296_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2235_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2228_);
                v___f_2229_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_2229_, 0, v___y_2228_);
                v___x_2230_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1;
                v___x_2231_ = lean_mk_thunk(v___f_2229_);
                v___x_2232_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
                        v___x_2230_,
                        v___x_2231_,
                        v_msgs_2227_,
                    );
                crate::leanh::lean_dec_ref(v___x_2231_);
                v___x_2233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2233_, 0, v___x_2232_);
                crate::leanh::lean_ctor_set(v___x_2233_, 1, v___y_2228_);
                v___x_2234_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2234_, 0, v___x_2233_);
                return v___x_2234_;
            }
            2 => {
                v___x_2242_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(
                        v_snd_2238_,
                        v_a_2221_,
                        v_a_2222_,
                        v_a_2223_,
                        v_a_2224_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2242_) == 0 {
                    v_a_2243_ = crate::leanh::lean_ctor_get(v___x_2242_, 0);
                    crate::leanh::lean_inc(v_a_2243_);
                    crate::leanh::lean_dec_ref_known(v___x_2242_, 1);
                    v_fst_2244_ = crate::leanh::lean_ctor_get(v_a_2243_, 0);
                    v_snd_2245_ = crate::leanh::lean_ctor_get(v_a_2243_, 1);
                    v_isSharedCheck_2295_ = (!crate::leanh::lean_is_exclusive(v_a_2243_)) as u8;
                    if v_isSharedCheck_2295_ == 0 {
                        v___x_2247_ = v_a_2243_;
                        v_isShared_2248_ = v_isSharedCheck_2295_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2245_);
                        crate::leanh::lean_inc(v_fst_2244_);
                        crate::leanh::lean_dec(v_a_2243_);
                        v___x_2247_ = crate::leanh::lean_box(0);
                        v_isShared_2248_ = v_isSharedCheck_2295_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2240_);
                    crate::leanh::lean_dec(v_fst_2237_);
                    return v___x_2242_;
                }
            }
            3 => {
                v___x_2249_ = crate::leanh::lean_unsigned_to_nat(0);
                v_msgs_2250_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
                v___x_2251_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(
                    v_msgs_2250_,
                    v_fst_2237_,
                );
                v___x_2252_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(
                    v___x_2251_,
                    v_fst_2244_,
                );
                v___x_2253_ = lean_array_get_size(v___x_2252_);
                v___x_2254_ = lean_nat_dec_eq(v___x_2253_, v___x_2249_);
                if v___x_2254_ == 0 {
                    v_neutral_x3f_2255_ = crate::leanh::lean_ctor_get(v_snd_2245_, 4);
                    crate::leanh::lean_inc(v_neutral_x3f_2255_);
                    v_idempotentInst_x3f_2256_ = crate::leanh::lean_ctor_get(v_snd_2245_, 6);
                    crate::leanh::lean_inc(v_idempotentInst_x3f_2256_);
                    v_commInst_x3f_2257_ = crate::leanh::lean_ctor_get(v_snd_2245_, 7);
                    if crate::leanh::lean_obj_tag(v_commInst_x3f_2257_) == 0 {
                        if v___x_2254_ == 0 {
                            v_info_2289_ = v_msgs_2250_;
                            v___y_2290_ = v_snd_2245_;
                            v_neutral_x3f_2291_ = v_neutral_x3f_2255_;
                            v_idempotentInst_x3f_2292_ = v_idempotentInst_x3f_2256_;
                            state = 9;
                            continue;
                        } else {
                            state = 10;
                            continue;
                        }
                    } else {
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2247_);
                    crate::leanh::lean_del_object(v___x_2240_);
                    v_msgs_2227_ = v___x_2252_;
                    v___y_2228_ = v_snd_2245_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_2261_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4;
                v___x_2262_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5);
                v___x_2263_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
                        v___x_2261_,
                        v___x_2262_,
                        v_info_2259_,
                    );
                v___x_2264_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(
                    v___x_2252_,
                    v___x_2263_,
                );
                v_msgs_2227_ = v___x_2264_;
                v___y_2228_ = v___y_2260_;
                state = 1;
                continue;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_neutral_x3f_2268_) == 1 {
                    v_val_2269_ = crate::leanh::lean_ctor_get(v_neutral_x3f_2268_, 0);
                    crate::leanh::lean_inc(v_val_2269_);
                    crate::leanh::lean_dec_ref_known(v_neutral_x3f_2268_, 1);
                    v___x_2270_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7);
                    v___x_2271_ = l_Lean_MessageData_ofExpr(v_val_2269_);
                    if v_isShared_2248_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2247_, 7);
                        crate::leanh::lean_ctor_set(v___x_2247_, 1, v___x_2271_);
                        crate::leanh::lean_ctor_set(v___x_2247_, 0, v___x_2270_);
                        v___x_2273_ = v___x_2247_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2281_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2270_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2271_);
                        v___x_2273_ = v_reuseFailAlloc_2281_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_neutral_x3f_2268_);
                    crate::leanh::lean_del_object(v___x_2247_);
                    crate::leanh::lean_del_object(v___x_2240_);
                    v_info_2259_ = v_info_2266_;
                    v___y_2260_ = v___y_2267_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_2274_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
                if v_isShared_2241_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2240_, 7);
                    crate::leanh::lean_ctor_set(v___x_2240_, 1, v___x_2274_);
                    crate::leanh::lean_ctor_set(v___x_2240_, 0, v___x_2273_);
                    v___x_2276_ = v___x_2240_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2280_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2274_);
                    v___x_2276_ = v_reuseFailAlloc_2280_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2277_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_2278_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(v___x_2276_, v___x_2277_);
                v___x_2279_ = lean_array_push(v_info_2266_, v___x_2278_);
                v_info_2259_ = v___x_2279_;
                v___y_2260_ = v___y_2267_;
                state = 4;
                continue;
            }
            8 => {
                v_neutral_x3f_2285_ = crate::leanh::lean_ctor_get(v___y_2283_, 4);
                crate::leanh::lean_inc(v_neutral_x3f_2285_);
                v___x_2286_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9);
                v___x_2287_ = lean_array_push(v___y_2284_, v___x_2286_);
                v_info_2266_ = v___x_2287_;
                v___y_2267_ = v___y_2283_;
                v_neutral_x3f_2268_ = v_neutral_x3f_2285_;
                state = 5;
                continue;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_idempotentInst_x3f_2292_) == 0 {
                    if v___x_2254_ == 0 {
                        v_info_2266_ = v_info_2289_;
                        v___y_2267_ = v___y_2290_;
                        v_neutral_x3f_2268_ = v_neutral_x3f_2291_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_neutral_x3f_2291_);
                        v___y_2283_ = v___y_2290_;
                        v___y_2284_ = v_info_2289_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_idempotentInst_x3f_2292_, 1);
                    crate::leanh::lean_dec(v_neutral_x3f_2291_);
                    v___y_2283_ = v___y_2290_;
                    v___y_2284_ = v_info_2289_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_2294_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12);
                v_info_2289_ = v___x_2294_;
                v___y_2290_ = v_snd_2245_;
                v_neutral_x3f_2291_ = v_neutral_x3f_2255_;
                v_idempotentInst_x3f_2292_ = v_idempotentInst_x3f_2256_;
                state = 9;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___boxed(
    mut v_a_2297_: *mut crate::leanh::LeanObject,
    mut v_a_2298_: *mut crate::leanh::LeanObject,
    mut v_a_2299_: *mut crate::leanh::LeanObject,
    mut v_a_2300_: *mut crate::leanh::LeanObject,
    mut v_a_2301_: *mut crate::leanh::LeanObject,
    mut v_a_2302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2303_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(
        v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_,
    );
    crate::leanh::lean_dec(v_a_2301_);
    crate::leanh::lean_dec_ref(v_a_2300_);
    crate::leanh::lean_dec(v_a_2299_);
    crate::leanh::lean_dec_ref(v_a_2298_);
    return v_res_2303_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(
    mut v_as_2304_: *mut crate::leanh::LeanObject,
    mut v_sz_2305_: usize,
    mut v_i_2306_: usize,
    mut v_b_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: usize = 0;
    let mut v___x_2316_: usize = 0;
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2318_ = lean_usize_dec_lt(v_i_2306_, v_sz_2305_);
                if v___x_2318_ == 0 {
                    v___x_2319_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2319_, 0, v_b_2307_);
                    return v___x_2319_;
                } else {
                    v_a_2320_ = lean_array_uget_borrowed(v_as_2304_, v_i_2306_);
                    crate::leanh::lean_inc(v_a_2320_);
                    v___x_2321_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(
                            v_a_2320_,
                            v___y_2308_,
                            v___y_2309_,
                            v___y_2310_,
                            v___y_2311_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2321_) == 0 {
                        v_a_2322_ = crate::leanh::lean_ctor_get(v___x_2321_, 0);
                        crate::leanh::lean_inc(v_a_2322_);
                        crate::leanh::lean_dec_ref_known(v___x_2321_, 1);
                        v_fst_2323_ = crate::leanh::lean_ctor_get(v_a_2322_, 0);
                        crate::leanh::lean_inc(v_fst_2323_);
                        crate::leanh::lean_dec(v_a_2322_);
                        if crate::leanh::lean_obj_tag(v_fst_2323_) == 1 {
                            v_val_2324_ = crate::leanh::lean_ctor_get(v_fst_2323_, 0);
                            crate::leanh::lean_inc(v_val_2324_);
                            crate::leanh::lean_dec_ref_known(v_fst_2323_, 1);
                            v___x_2325_ = lean_array_push(v_b_2307_, v_val_2324_);
                            v_a_2314_ = v___x_2325_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_fst_2323_);
                            v_a_2314_ = v_b_2307_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2307_);
                        v_a_2326_ = crate::leanh::lean_ctor_get(v___x_2321_, 0);
                        v_isSharedCheck_2333_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2321_)) as u8;
                        if v_isSharedCheck_2333_ == 0 {
                            v___x_2328_ = v___x_2321_;
                            v_isShared_2329_ = v_isSharedCheck_2333_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2326_);
                            crate::leanh::lean_dec(v___x_2321_);
                            v___x_2328_ = crate::leanh::lean_box(0);
                            v_isShared_2329_ = v_isSharedCheck_2333_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2315_ = 1usize;
                v___x_2316_ = lean_usize_add(v_i_2306_, v___x_2315_);
                v_i_2306_ = v___x_2316_;
                v_b_2307_ = v_a_2314_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2329_ == 0 {
                    v___x_2331_ = v___x_2328_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
                    v___x_2331_ = v_reuseFailAlloc_2332_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2331_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0___boxed(
    mut v_as_2334_: *mut crate::leanh::LeanObject,
    mut v_sz_2335_: *mut crate::leanh::LeanObject,
    mut v_i_2336_: *mut crate::leanh::LeanObject,
    mut v_b_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2343_: usize = 0;
    let mut v_i_boxed_2344_: usize = 0;
    let mut v_res_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2343_ = crate::leanh::lean_unbox_usize(v_sz_2335_);
    crate::leanh::lean_dec(v_sz_2335_);
    v_i_boxed_2344_ = crate::leanh::lean_unbox_usize(v_i_2336_);
    crate::leanh::lean_dec(v_i_2336_);
    v_res_2345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_as_2334_, v_sz_boxed_2343_, v_i_boxed_2344_, v_b_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
    crate::leanh::lean_dec(v___y_2341_);
    crate::leanh::lean_dec_ref(v___y_2340_);
    crate::leanh::lean_dec(v___y_2339_);
    crate::leanh::lean_dec_ref(v___y_2338_);
    crate::leanh::lean_dec_ref(v_as_2334_);
    return v_res_2345_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: f64 = 0.0;
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2346_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_2347_ = 1;
    v___x_2348_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_2349_ = crate::leanh::lean_box(0);
    v___x_2350_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1;
    v___x_2351_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_2351_, 0, v___x_2350_);
    crate::leanh::lean_ctor_set(v___x_2351_, 1, v___x_2349_);
    crate::leanh::lean_ctor_set(v___x_2351_, 2, v___x_2346_);
    crate::leanh::lean_ctor_set_float(
        v___x_2351_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_2348_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_2351_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_2348_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2351_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_2347_,
    );
    return v___x_2351_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Lean_Meta_Grind_AC_pp_x3f___closed__2;
    v___x_2356_ = l_Lean_MessageData_ofFormat(v___x_2355_);
    return v___x_2356_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_pp_x3f(
    mut v_goal_2357_: *mut crate::leanh::LeanObject,
    mut v_a_2358_: *mut crate::leanh::LeanObject,
    mut v_a_2359_: *mut crate::leanh::LeanObject,
    mut v_a_2360_: *mut crate::leanh::LeanObject,
    mut v_a_2361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structs_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2369_: usize = 0;
    let mut v___x_2370_: usize = 0;
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut v_a_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2404_: u8 = 0;
    let mut v_a_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v_ref_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2363_ = l_Lean_Meta_Grind_AC_acExt;
                v___x_2364_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2363_, v_goal_2357_);
                if crate::leanh::lean_obj_tag(v___x_2364_) == 0 {
                    v_a_2365_ = crate::leanh::lean_ctor_get(v___x_2364_, 0);
                    crate::leanh::lean_inc(v_a_2365_);
                    crate::leanh::lean_dec_ref_known(v___x_2364_, 1);
                    v_structs_2366_ = crate::leanh::lean_ctor_get(v_a_2365_, 0);
                    crate::leanh::lean_inc_ref(v_structs_2366_);
                    crate::leanh::lean_dec(v_a_2365_);
                    v___x_2367_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_msgs_2368_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
                    v_sz_2369_ = lean_array_size(v_structs_2366_);
                    v___x_2370_ = 0usize;
                    v___x_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_structs_2366_, v_sz_2369_, v___x_2370_, v_msgs_2368_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
                    crate::leanh::lean_dec_ref(v_structs_2366_);
                    if crate::leanh::lean_obj_tag(v___x_2371_) == 0 {
                        v_a_2372_ = crate::leanh::lean_ctor_get(v___x_2371_, 0);
                        v_isSharedCheck_2396_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2371_)) as u8;
                        if v_isSharedCheck_2396_ == 0 {
                            v___x_2374_ = v___x_2371_;
                            v_isShared_2375_ = v_isSharedCheck_2396_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2372_);
                            crate::leanh::lean_dec(v___x_2371_);
                            v___x_2374_ = crate::leanh::lean_box(0);
                            v_isShared_2375_ = v_isSharedCheck_2396_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2397_ = crate::leanh::lean_ctor_get(v___x_2371_, 0);
                        v_isSharedCheck_2404_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2371_)) as u8;
                        if v_isSharedCheck_2404_ == 0 {
                            v___x_2399_ = v___x_2371_;
                            v_isShared_2400_ = v_isSharedCheck_2404_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2397_);
                            crate::leanh::lean_dec(v___x_2371_);
                            v___x_2399_ = crate::leanh::lean_box(0);
                            v_isShared_2400_ = v_isSharedCheck_2404_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_2405_ = crate::leanh::lean_ctor_get(v___x_2364_, 0);
                    v_isSharedCheck_2417_ = (!crate::leanh::lean_is_exclusive(v___x_2364_)) as u8;
                    if v_isSharedCheck_2417_ == 0 {
                        v___x_2407_ = v___x_2364_;
                        v_isShared_2408_ = v_isSharedCheck_2417_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2405_);
                        crate::leanh::lean_dec(v___x_2364_);
                        v___x_2407_ = crate::leanh::lean_box(0);
                        v_isShared_2408_ = v_isSharedCheck_2417_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2376_ = lean_array_get_size(v_a_2372_);
                v___x_2377_ = lean_nat_dec_eq(v___x_2376_, v___x_2367_);
                if v___x_2377_ == 0 {
                    v___x_2378_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2379_ = lean_nat_dec_eq(v___x_2376_, v___x_2378_);
                    if v___x_2379_ == 0 {
                        v___x_2380_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__0_once),
                            _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0,
                        );
                        v___x_2381_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__3_once),
                            _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3,
                        );
                        v___x_2382_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2382_, 0, v___x_2380_);
                        crate::leanh::lean_ctor_set(v___x_2382_, 1, v___x_2381_);
                        crate::leanh::lean_ctor_set(v___x_2382_, 2, v_a_2372_);
                        v___x_2383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2383_, 0, v___x_2382_);
                        if v_isShared_2375_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2374_, 0, v___x_2383_);
                            v___x_2385_ = v___x_2374_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2386_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
                            v___x_2385_ = v_reuseFailAlloc_2386_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2387_ = lean_array_fget(v_a_2372_, v___x_2367_);
                        crate::leanh::lean_dec(v_a_2372_);
                        v___x_2388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2388_, 0, v___x_2387_);
                        if v_isShared_2375_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2374_, 0, v___x_2388_);
                            v___x_2390_ = v___x_2374_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2391_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
                            v___x_2390_ = v_reuseFailAlloc_2391_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2372_);
                    v___x_2392_ = crate::leanh::lean_box(0);
                    if v_isShared_2375_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2374_, 0, v___x_2392_);
                        v___x_2394_ = v___x_2374_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
                        v___x_2394_ = v_reuseFailAlloc_2395_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2385_;
            }
            3 => {
                return v___x_2390_;
            }
            4 => {
                return v___x_2394_;
            }
            5 => {
                if v_isShared_2400_ == 0 {
                    v___x_2402_ = v___x_2399_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2403_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
                    v___x_2402_ = v_reuseFailAlloc_2403_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2402_;
            }
            7 => {
                v_ref_2409_ = crate::leanh::lean_ctor_get(v_a_2360_, 5);
                v___x_2410_ = lean_io_error_to_string(v_a_2405_);
                v___x_2411_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2411_, 0, v___x_2410_);
                v___x_2412_ = l_Lean_MessageData_ofFormat(v___x_2411_);
                crate::leanh::lean_inc(v_ref_2409_);
                v___x_2413_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2413_, 0, v_ref_2409_);
                crate::leanh::lean_ctor_set(v___x_2413_, 1, v___x_2412_);
                if v_isShared_2408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2407_, 0, v___x_2413_);
                    v___x_2415_ = v___x_2407_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2416_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
                    v___x_2415_ = v_reuseFailAlloc_2416_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2415_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_pp_x3f___boxed(
    mut v_goal_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
    mut v_a_2420_: *mut crate::leanh::LeanObject,
    mut v_a_2421_: *mut crate::leanh::LeanObject,
    mut v_a_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ =
        l_Lean_Meta_Grind_AC_pp_x3f(v_goal_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
    crate::leanh::lean_dec(v_a_2422_);
    crate::leanh::lean_dec_ref(v_a_2421_);
    crate::leanh::lean_dec(v_a_2420_);
    crate::leanh::lean_dec_ref(v_a_2419_);
    crate::leanh::lean_dec_ref(v_goal_2418_);
    return v_res_2424_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM =
        _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_PP(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_PP(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
}
