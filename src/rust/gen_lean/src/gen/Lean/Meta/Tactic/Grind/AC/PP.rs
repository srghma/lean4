// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.PP
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.AC.DenoteExpr Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_mk_thunk, lean_nat_dec_eq, lean_nat_dec_lt, lean_thunk_get_own,
    lean_usize_add, lean_usize_dec_lt,
};
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
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0:
    f64 = 0.0;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [66, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject,13286986945483979944 as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value) as *mut leanh::LeanObject,6004542540932731919 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [68, 105, 115, 101, 113, 117, 97, 108, 105, 116, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [78, 101, 0]};
static mut l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,6695605208187598753 as *mut leanh::LeanObject] };
static mut l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 105, 115, 101, 113, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value) as *mut leanh::LeanObject,12150963035389937170 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [79, 112, 101, 114, 97, 116, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [80, 114, 111, 112, 101, 114, 116, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 115, 115, 111, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value) as *mut leanh::LeanObject,12101614322480916425 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [112, 114, 111, 112, 101, 114, 116, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value) as *mut leanh::LeanObject,4640836329272094479 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 100, 101, 110, 116, 105, 116, 121, 58, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 100, 101, 109, 112, 111, 116, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 109, 109, 117, 116, 97, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_pp_x3f___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_pp_x3f___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1213_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_1213_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1214_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0);
    v___x_1215_ = l_StateRefT_x27_instMonad___redArg(v___x_1214_);
    return v___x_1215_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM()
-> *mut leanh::LeanObject {
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v_toFunctor_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1247_: u8 = 0;
    let mut v___f_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut v_unused_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_unused_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1220_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1);
                v_toApplicative_1221_ = leanh::lean_ctor_get(v___x_1220_, 0);
                v_toFunctor_1222_ = leanh::lean_ctor_get(v_toApplicative_1221_, 0);
                v_toSeq_1223_ = leanh::lean_ctor_get(v_toApplicative_1221_, 2);
                v_toSeqLeft_1224_ = leanh::lean_ctor_get(v_toApplicative_1221_, 3);
                v_toSeqRight_1225_ = leanh::lean_ctor_get(v_toApplicative_1221_, 4);
                v___f_1226_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2;
                v___f_1227_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_1222_, 2);
                v___f_1228_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1228_, 0, v_toFunctor_1222_);
                v___f_1229_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1229_, 0, v_toFunctor_1222_);
                v___x_1230_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1230_, 0, v___f_1228_);
                leanh::lean_ctor_set(v___x_1230_, 1, v___f_1229_);
                leanh::lean_inc(v_toSeqRight_1225_);
                v___f_1231_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1231_, 0, v_toSeqRight_1225_);
                leanh::lean_inc(v_toSeqLeft_1224_);
                v___f_1232_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1232_, 0, v_toSeqLeft_1224_);
                leanh::lean_inc(v_toSeq_1223_);
                v___f_1233_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1233_, 0, v_toSeq_1223_);
                v___x_1234_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_1234_, 0, v___x_1230_);
                leanh::lean_ctor_set(v___x_1234_, 1, v___f_1226_);
                leanh::lean_ctor_set(v___x_1234_, 2, v___f_1233_);
                leanh::lean_ctor_set(v___x_1234_, 3, v___f_1232_);
                leanh::lean_ctor_set(v___x_1234_, 4, v___f_1231_);
                v___x_1235_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1235_, 0, v___x_1234_);
                leanh::lean_ctor_set(v___x_1235_, 1, v___f_1227_);
                v___x_1236_ = l_StateRefT_x27_instMonad___redArg(v___x_1235_);
                v_toApplicative_1237_ = leanh::lean_ctor_get(v___x_1236_, 0);
                v_isSharedCheck_1265_ = (!leanh::lean_is_exclusive(v___x_1236_)) as u8;
                if v_isSharedCheck_1265_ == 0 {
                    v_unused_1266_ = leanh::lean_ctor_get(v___x_1236_, 1);
                    leanh::lean_dec(v_unused_1266_);
                    v___x_1239_ = v___x_1236_;
                    v_isShared_1240_ = v_isSharedCheck_1265_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_1237_);
                    leanh::lean_dec(v___x_1236_);
                    v___x_1239_ = leanh::lean_box(0);
                    v_isShared_1240_ = v_isSharedCheck_1265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1241_ = leanh::lean_ctor_get(v_toApplicative_1237_, 0);
                v_toSeq_1242_ = leanh::lean_ctor_get(v_toApplicative_1237_, 2);
                v_toSeqLeft_1243_ = leanh::lean_ctor_get(v_toApplicative_1237_, 3);
                v_toSeqRight_1244_ = leanh::lean_ctor_get(v_toApplicative_1237_, 4);
                v_isSharedCheck_1263_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_1237_)) as u8;
                if v_isSharedCheck_1263_ == 0 {
                    v_unused_1264_ = leanh::lean_ctor_get(v_toApplicative_1237_, 1);
                    leanh::lean_dec(v_unused_1264_);
                    v___x_1246_ = v_toApplicative_1237_;
                    v_isShared_1247_ = v_isSharedCheck_1263_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_1244_);
                    leanh::lean_inc(v_toSeqLeft_1243_);
                    leanh::lean_inc(v_toSeq_1242_);
                    leanh::lean_inc(v_toFunctor_1241_);
                    leanh::lean_dec(v_toApplicative_1237_);
                    v___x_1246_ = leanh::lean_box(0);
                    v_isShared_1247_ = v_isSharedCheck_1263_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1248_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4;
                v___f_1249_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5;
                leanh::lean_inc_ref(v_toFunctor_1241_);
                v___f_1250_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1250_, 0, v_toFunctor_1241_);
                v___f_1251_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1251_, 0, v_toFunctor_1241_);
                v___x_1252_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1252_, 0, v___f_1250_);
                leanh::lean_ctor_set(v___x_1252_, 1, v___f_1251_);
                v___f_1253_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1253_, 0, v_toSeqRight_1244_);
                v___f_1254_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1254_, 0, v_toSeqLeft_1243_);
                v___f_1255_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_1255_, 0, v_toSeq_1242_);
                if v_isShared_1247_ == 0 {
                    leanh::lean_ctor_set(v___x_1246_, 4, v___f_1253_);
                    leanh::lean_ctor_set(v___x_1246_, 3, v___f_1254_);
                    leanh::lean_ctor_set(v___x_1246_, 2, v___f_1255_);
                    leanh::lean_ctor_set(v___x_1246_, 1, v___f_1248_);
                    leanh::lean_ctor_set(v___x_1246_, 0, v___x_1252_);
                    v___x_1257_ = v___x_1246_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1252_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___f_1248_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 2, v___f_1255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 3, v___f_1254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1262_, 4, v___f_1253_);
                    v___x_1257_ = v_reuseFailAlloc_1262_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1240_ == 0 {
                    leanh::lean_ctor_set(v___x_1239_, 1, v___f_1249_);
                    leanh::lean_ctor_set(v___x_1239_, 0, v___x_1257_);
                    v___x_1259_ = v___x_1239_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1261_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1257_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___f_1249_);
                    v___x_1259_ = v_reuseFailAlloc_1261_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1260_ =
                    leanh::lean_alloc_closure(l_StateT_get as *mut core::ffi::c_void, 4, 3);
                leanh::lean_closure_set(v___x_1260_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1260_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_1260_, 2, v___x_1259_);
                return v___x_1260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0()
-> f64 {
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: f64 = 0.0;
    v___x_1267_ = leanh::lean_unsigned_to_nat(0);
    v___x_1268_ = lean_float_of_nat(v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
    mut v_cls_1270_: *mut leanh::LeanObject,
    mut v_header_1271_: *mut leanh::LeanObject,
    mut v_msgs_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: u8 = 0;
    v___x_1273_ = lean_array_get_size(v_msgs_1272_);
    v___x_1274_ = leanh::lean_unsigned_to_nat(0);
    v___x_1275_ = lean_nat_dec_eq(v___x_1273_, v___x_1274_);
    if v___x_1275_ == 0 {
        let mut v___x_1276_: u8 = 0;
        let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1278_: f64 = 0.0;
        let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1276_ = 1;
        v___x_1277_ = leanh::lean_box(0);
        v___x_1278_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
        v___x_1279_ =
            l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
        v___x_1280_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
        leanh::lean_ctor_set(v___x_1280_, 0, v_cls_1270_);
        leanh::lean_ctor_set(v___x_1280_, 1, v___x_1277_);
        leanh::lean_ctor_set(v___x_1280_, 2, v___x_1279_);
        leanh::lean_ctor_set_float(
            v___x_1280_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            v___x_1278_,
        );
        leanh::lean_ctor_set_float(
            v___x_1280_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            v___x_1278_,
        );
        leanh::lean_ctor_set_uint8(
            v___x_1280_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
            v___x_1276_,
        );
        v___x_1281_ = lean_thunk_get_own(v_header_1271_);
        v___x_1282_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1282_, 0, v___x_1280_);
        leanh::lean_ctor_set(v___x_1282_, 1, v___x_1281_);
        leanh::lean_ctor_set(v___x_1282_, 2, v_msgs_1272_);
        v___x_1283_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1283_, 0, v___x_1282_);
        return v___x_1283_;
    } else {
        let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_msgs_1272_);
        leanh::lean_dec(v_cls_1270_);
        v___x_1284_ = leanh::lean_box(0);
        return v___x_1284_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___boxed(
    mut v_cls_1285_: *mut leanh::LeanObject,
    mut v_header_1286_: *mut leanh::LeanObject,
    mut v_msgs_1287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1288_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
        v_cls_1285_,
        v_header_1286_,
        v_msgs_1287_,
    );
    leanh::lean_dec_ref(v_header_1286_);
    return v_res_1288_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(
    mut v_msgs_1289_: *mut leanh::LeanObject,
    mut v_msg_x3f_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_msg_x3f_1290_) == 1 {
        let mut v_val_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1291_ = leanh::lean_ctor_get(v_msg_x3f_1290_, 0);
        leanh::lean_inc(v_val_1291_);
        leanh::lean_dec_ref_known(v_msg_x3f_1290_, 1);
        v___x_1292_ = lean_array_push(v_msgs_1289_, v_val_1291_);
        return v___x_1292_;
    } else {
        leanh::lean_dec(v_msg_x3f_1290_);
        return v_msgs_1289_;
    }
}
pub unsafe fn l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(
    mut v_e_1295_: *mut leanh::LeanObject,
    mut v_cls_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: f64 = 0.0;
    let mut v___x_1299_: u8 = 0;
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = leanh::lean_box(0);
    v___x_1298_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_1299_ = 1;
    v___x_1300_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_1301_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
    leanh::lean_ctor_set(v___x_1301_, 0, v_cls_1296_);
    leanh::lean_ctor_set(v___x_1301_, 1, v___x_1297_);
    leanh::lean_ctor_set(v___x_1301_, 2, v___x_1300_);
    leanh::lean_ctor_set_float(
        v___x_1301_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_1298_,
    );
    leanh::lean_ctor_set_float(
        v___x_1301_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        v___x_1298_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1301_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
        v___x_1299_,
    );
    v___x_1302_ = l_Lean_MessageData_ofExpr(v_e_1295_);
    v___x_1303_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_1304_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1304_, 0, v___x_1301_);
    leanh::lean_ctor_set(v___x_1304_, 1, v___x_1302_);
    leanh::lean_ctor_set(v___x_1304_, 2, v___x_1303_);
    return v___x_1304_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1308_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1;
    v___x_1309_ = l_Lean_MessageData_ofFormat(v___x_1308_);
    return v___x_1309_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0(
    mut v_x_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1311_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2);
    return v___x_1311_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(
    mut v_s_1312_: *mut leanh::LeanObject,
    mut v___y_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1320_: u8 = 0;
    let mut v_size_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut v_x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v_fst_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v_op_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1315_ = l_Lean_instInhabitedExpr;
                if leanh::lean_obj_tag(v_s_1312_) == 0 {
                    v_vars_1316_ = leanh::lean_ctor_get(v___y_1313_, 10);
                    v_x_1317_ = leanh::lean_ctor_get(v_s_1312_, 0);
                    v_isSharedCheck_1333_ = (!leanh::lean_is_exclusive(v_s_1312_)) as u8;
                    if v_isSharedCheck_1333_ == 0 {
                        v___x_1319_ = v_s_1312_;
                        v_isShared_1320_ = v_isSharedCheck_1333_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_x_1317_);
                        leanh::lean_dec(v_s_1312_);
                        v___x_1319_ = leanh::lean_box(0);
                        v_isShared_1320_ = v_isSharedCheck_1333_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_x_1334_ = leanh::lean_ctor_get(v_s_1312_, 0);
                    leanh::lean_inc(v_x_1334_);
                    v_s_1335_ = leanh::lean_ctor_get(v_s_1312_, 1);
                    leanh::lean_inc_ref(v_s_1335_);
                    leanh::lean_dec_ref_known(v_s_1312_, 2);
                    leanh::lean_inc_ref(v___y_1313_);
                    v___x_1336_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_1335_, v___y_1313_);
                    v_a_1337_ = leanh::lean_ctor_get(v___x_1336_, 0);
                    v_isSharedCheck_1362_ = (!leanh::lean_is_exclusive(v___x_1336_)) as u8;
                    if v_isSharedCheck_1362_ == 0 {
                        v___x_1339_ = v___x_1336_;
                        v_isShared_1340_ = v_isSharedCheck_1362_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1337_);
                        leanh::lean_dec(v___x_1336_);
                        v___x_1339_ = leanh::lean_box(0);
                        v_isShared_1340_ = v_isSharedCheck_1362_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_size_1321_ = leanh::lean_ctor_get(v_vars_1316_, 2);
                v___x_1322_ = lean_nat_dec_lt(v_x_1317_, v_size_1321_);
                if v___x_1322_ == 0 {
                    leanh::lean_dec(v_x_1317_);
                    v___x_1323_ = l_outOfBounds___redArg(v___x_1315_);
                    v___x_1324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1324_, 0, v___x_1323_);
                    leanh::lean_ctor_set(v___x_1324_, 1, v___y_1313_);
                    if v_isShared_1320_ == 0 {
                        leanh::lean_ctor_set(v___x_1319_, 0, v___x_1324_);
                        v___x_1326_ = v___x_1319_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
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
                    leanh::lean_dec(v_x_1317_);
                    v___x_1329_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1329_, 0, v___x_1328_);
                    leanh::lean_ctor_set(v___x_1329_, 1, v___y_1313_);
                    if v_isShared_1320_ == 0 {
                        leanh::lean_ctor_set(v___x_1319_, 0, v___x_1329_);
                        v___x_1331_ = v___x_1319_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1332_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
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
                v_fst_1341_ = leanh::lean_ctor_get(v_a_1337_, 0);
                v_snd_1342_ = leanh::lean_ctor_get(v_a_1337_, 1);
                v_isSharedCheck_1361_ = (!leanh::lean_is_exclusive(v_a_1337_)) as u8;
                if v_isSharedCheck_1361_ == 0 {
                    v___x_1344_ = v_a_1337_;
                    v_isShared_1345_ = v_isSharedCheck_1361_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1342_);
                    leanh::lean_inc(v_fst_1341_);
                    leanh::lean_dec(v_a_1337_);
                    v___x_1344_ = leanh::lean_box(0);
                    v_isShared_1345_ = v_isSharedCheck_1361_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_op_1346_ = leanh::lean_ctor_get(v___y_1313_, 3);
                leanh::lean_inc_ref(v_op_1346_);
                v_vars_1347_ = leanh::lean_ctor_get(v___y_1313_, 10);
                leanh::lean_inc_ref(v_vars_1347_);
                leanh::lean_dec_ref(v___y_1313_);
                v_size_1357_ = leanh::lean_ctor_get(v_vars_1347_, 2);
                v___x_1358_ = lean_nat_dec_lt(v_x_1334_, v_size_1357_);
                if v___x_1358_ == 0 {
                    leanh::lean_dec_ref(v_vars_1347_);
                    leanh::lean_dec(v_x_1334_);
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
                    leanh::lean_dec(v_x_1334_);
                    leanh::lean_dec_ref(v_vars_1347_);
                    v___y_1349_ = v___x_1360_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1350_ = l_Lean_mkAppB(v_op_1346_, v___y_1349_, v_fst_1341_);
                if v_isShared_1345_ == 0 {
                    leanh::lean_ctor_set(v___x_1344_, 0, v___x_1350_);
                    v___x_1352_ = v___x_1344_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1356_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_snd_1342_);
                    v___x_1352_ = v_reuseFailAlloc_1356_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1340_ == 0 {
                    leanh::lean_ctor_set(v___x_1339_, 0, v___x_1352_);
                    v___x_1354_ = v___x_1339_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1355_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
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
    mut v_s_1363_: *mut leanh::LeanObject,
    mut v___y_1364_: *mut leanh::LeanObject,
    mut v___y_1365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1366_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_1363_, v___y_1364_);
    return v_res_1366_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(
    mut v_c_1370_: *mut leanh::LeanObject,
    mut v___y_1371_: *mut leanh::LeanObject,
    mut v___y_1372_: *mut leanh::LeanObject,
    mut v___y_1373_: *mut leanh::LeanObject,
    mut v___y_1374_: *mut leanh::LeanObject,
    mut v___y_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1385_: u8 = 0;
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v_fst_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1395_: u8 = 0;
    let mut v_type_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1377_ = leanh::lean_ctor_get(v_c_1370_, 0);
                leanh::lean_inc_ref(v_lhs_1377_);
                v_rhs_1378_ = leanh::lean_ctor_get(v_c_1370_, 1);
                leanh::lean_inc_ref(v_rhs_1378_);
                leanh::lean_dec_ref(v_c_1370_);
                leanh::lean_inc_ref(v___y_1371_);
                v___x_1379_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_1377_, v___y_1371_);
                v_a_1380_ = leanh::lean_ctor_get(v___x_1379_, 0);
                leanh::lean_inc(v_a_1380_);
                leanh::lean_dec_ref(v___x_1379_);
                v_fst_1381_ = leanh::lean_ctor_get(v_a_1380_, 0);
                v_snd_1382_ = leanh::lean_ctor_get(v_a_1380_, 1);
                v_isSharedCheck_1413_ = (!leanh::lean_is_exclusive(v_a_1380_)) as u8;
                if v_isSharedCheck_1413_ == 0 {
                    v___x_1384_ = v_a_1380_;
                    v_isShared_1385_ = v_isSharedCheck_1413_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1382_);
                    leanh::lean_inc(v_fst_1381_);
                    leanh::lean_dec(v_a_1380_);
                    v___x_1384_ = leanh::lean_box(0);
                    v_isShared_1385_ = v_isSharedCheck_1413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1386_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_1378_, v_snd_1382_);
                v_a_1387_ = leanh::lean_ctor_get(v___x_1386_, 0);
                v_isSharedCheck_1412_ = (!leanh::lean_is_exclusive(v___x_1386_)) as u8;
                if v_isSharedCheck_1412_ == 0 {
                    v___x_1389_ = v___x_1386_;
                    v_isShared_1390_ = v_isSharedCheck_1412_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1387_);
                    leanh::lean_dec(v___x_1386_);
                    v___x_1389_ = leanh::lean_box(0);
                    v_isShared_1390_ = v_isSharedCheck_1412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_1391_ = leanh::lean_ctor_get(v_a_1387_, 0);
                v_snd_1392_ = leanh::lean_ctor_get(v_a_1387_, 1);
                v_isSharedCheck_1411_ = (!leanh::lean_is_exclusive(v_a_1387_)) as u8;
                if v_isSharedCheck_1411_ == 0 {
                    v___x_1394_ = v_a_1387_;
                    v_isShared_1395_ = v_isSharedCheck_1411_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1392_);
                    leanh::lean_inc(v_fst_1391_);
                    leanh::lean_dec(v_a_1387_);
                    v___x_1394_ = leanh::lean_box(0);
                    v_isShared_1395_ = v_isSharedCheck_1411_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_type_1396_ = leanh::lean_ctor_get(v___y_1371_, 1);
                leanh::lean_inc_ref(v_type_1396_);
                v_u_1397_ = leanh::lean_ctor_get(v___y_1371_, 2);
                leanh::lean_inc(v_u_1397_);
                leanh::lean_dec_ref(v___y_1371_);
                v___x_1398_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1;
                v___x_1399_ = leanh::lean_box(0);
                if v_isShared_1385_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1384_, 1);
                    leanh::lean_ctor_set(v___x_1384_, 1, v___x_1399_);
                    leanh::lean_ctor_set(v___x_1384_, 0, v_u_1397_);
                    v___x_1401_ = v___x_1384_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_u_1397_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1399_);
                    v___x_1401_ = v_reuseFailAlloc_1410_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1402_ = l_Lean_mkConst(v___x_1398_, v___x_1401_);
                v___x_1403_ = l_Lean_mkApp3(v___x_1402_, v_type_1396_, v_fst_1381_, v_fst_1391_);
                if v_isShared_1395_ == 0 {
                    leanh::lean_ctor_set(v___x_1394_, 0, v___x_1403_);
                    v___x_1405_ = v___x_1394_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1403_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_snd_1392_);
                    v___x_1405_ = v_reuseFailAlloc_1409_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1390_ == 0 {
                    leanh::lean_ctor_set(v___x_1389_, 0, v___x_1405_);
                    v___x_1407_ = v___x_1389_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1408_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
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
    mut v_c_1414_: *mut leanh::LeanObject,
    mut v___y_1415_: *mut leanh::LeanObject,
    mut v___y_1416_: *mut leanh::LeanObject,
    mut v___y_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
    mut v___y_1419_: *mut leanh::LeanObject,
    mut v___y_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_c_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
    leanh::lean_dec(v___y_1419_);
    leanh::lean_dec_ref(v___y_1418_);
    leanh::lean_dec(v___y_1417_);
    leanh::lean_dec_ref(v___y_1416_);
    return v_res_1421_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(
    mut v_as_x27_1426_: *mut leanh::LeanObject,
    mut v_b_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
    mut v___y_1430_: *mut leanh::LeanObject,
    mut v___y_1431_: *mut leanh::LeanObject,
    mut v___y_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_1426_) == 0 {
                    v___x_1434_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1434_, 0, v_b_1427_);
                    leanh::lean_ctor_set(v___x_1434_, 1, v___y_1428_);
                    v___x_1435_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1435_, 0, v___x_1434_);
                    return v___x_1435_;
                } else {
                    v_head_1436_ = leanh::lean_ctor_get(v_as_x27_1426_, 0);
                    v_tail_1437_ = leanh::lean_ctor_get(v_as_x27_1426_, 1);
                    leanh::lean_inc(v_head_1436_);
                    v___x_1438_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_head_1436_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
                    v_a_1439_ = leanh::lean_ctor_get(v___x_1438_, 0);
                    leanh::lean_inc(v_a_1439_);
                    leanh::lean_dec_ref(v___x_1438_);
                    v_fst_1440_ = leanh::lean_ctor_get(v_a_1439_, 0);
                    leanh::lean_inc(v_fst_1440_);
                    v_snd_1441_ = leanh::lean_ctor_get(v_a_1439_, 1);
                    leanh::lean_inc(v_snd_1441_);
                    leanh::lean_dec(v_a_1439_);
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
    mut v_as_x27_1446_: *mut leanh::LeanObject,
    mut v_b_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
    mut v___y_1452_: *mut leanh::LeanObject,
    mut v___y_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1454_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_1446_, v_b_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
    leanh::lean_dec(v___y_1452_);
    leanh::lean_dec_ref(v___y_1451_);
    leanh::lean_dec(v___y_1450_);
    leanh::lean_dec_ref(v___y_1449_);
    leanh::lean_dec(v_as_x27_1446_);
    return v_res_1454_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3()
-> *mut leanh::LeanObject {
    let mut v___f_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1459_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0;
    v___x_1460_ = lean_mk_thunk(v___f_1459_);
    return v___x_1460_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(
    mut v_a_1461_: *mut leanh::LeanObject,
    mut v_a_1462_: *mut leanh::LeanObject,
    mut v_a_1463_: *mut leanh::LeanObject,
    mut v_a_1464_: *mut leanh::LeanObject,
    mut v_a_1465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_basis_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v_fst_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_a_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_basis_1467_ = leanh::lean_ctor_get(v_a_1461_, 15);
                leanh::lean_inc(v_basis_1467_);
                v_basis_1468_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
                v___x_1469_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_basis_1467_, v_basis_1468_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
                leanh::lean_dec(v_basis_1467_);
                if leanh::lean_obj_tag(v___x_1469_) == 0 {
                    v_a_1470_ = leanh::lean_ctor_get(v___x_1469_, 0);
                    v_isSharedCheck_1489_ = (!leanh::lean_is_exclusive(v___x_1469_)) as u8;
                    if v_isSharedCheck_1489_ == 0 {
                        v___x_1472_ = v___x_1469_;
                        v_isShared_1473_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1470_);
                        leanh::lean_dec(v___x_1469_);
                        v___x_1472_ = leanh::lean_box(0);
                        v_isShared_1473_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1490_ = leanh::lean_ctor_get(v___x_1469_, 0);
                    v_isSharedCheck_1497_ = (!leanh::lean_is_exclusive(v___x_1469_)) as u8;
                    if v_isSharedCheck_1497_ == 0 {
                        v___x_1492_ = v___x_1469_;
                        v_isShared_1493_ = v_isSharedCheck_1497_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1490_);
                        leanh::lean_dec(v___x_1469_);
                        v___x_1492_ = leanh::lean_box(0);
                        v_isShared_1493_ = v_isSharedCheck_1497_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1474_ = leanh::lean_ctor_get(v_a_1470_, 0);
                v_snd_1475_ = leanh::lean_ctor_get(v_a_1470_, 1);
                v_isSharedCheck_1488_ = (!leanh::lean_is_exclusive(v_a_1470_)) as u8;
                if v_isSharedCheck_1488_ == 0 {
                    v___x_1477_ = v_a_1470_;
                    v_isShared_1478_ = v_isSharedCheck_1488_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1475_);
                    leanh::lean_inc(v_fst_1474_);
                    leanh::lean_dec(v_a_1470_);
                    v___x_1477_ = leanh::lean_box(0);
                    v_isShared_1478_ = v_isSharedCheck_1488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1479_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2;
                v___x_1480_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3);
                v___x_1481_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
                        v___x_1479_,
                        v___x_1480_,
                        v_fst_1474_,
                    );
                if v_isShared_1478_ == 0 {
                    leanh::lean_ctor_set(v___x_1477_, 0, v___x_1481_);
                    v___x_1483_ = v___x_1477_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_snd_1475_);
                    v___x_1483_ = v_reuseFailAlloc_1487_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1473_ == 0 {
                    leanh::lean_ctor_set(v___x_1472_, 0, v___x_1483_);
                    v___x_1485_ = v___x_1472_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
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
                    v_reuseFailAlloc_1496_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
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
    mut v_a_1498_: *mut leanh::LeanObject,
    mut v_a_1499_: *mut leanh::LeanObject,
    mut v_a_1500_: *mut leanh::LeanObject,
    mut v_a_1501_: *mut leanh::LeanObject,
    mut v_a_1502_: *mut leanh::LeanObject,
    mut v_a_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1504_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(
        v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_,
    );
    leanh::lean_dec(v_a_1502_);
    leanh::lean_dec_ref(v_a_1501_);
    leanh::lean_dec(v_a_1500_);
    leanh::lean_dec_ref(v_a_1499_);
    return v_res_1504_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(
    mut v_as_1505_: *mut leanh::LeanObject,
    mut v_as_x27_1506_: *mut leanh::LeanObject,
    mut v_b_1507_: *mut leanh::LeanObject,
    mut v_a_1508_: *mut leanh::LeanObject,
    mut v___y_1509_: *mut leanh::LeanObject,
    mut v___y_1510_: *mut leanh::LeanObject,
    mut v___y_1511_: *mut leanh::LeanObject,
    mut v___y_1512_: *mut leanh::LeanObject,
    mut v___y_1513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1515_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_1506_, v_b_1507_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
    return v___x_1515_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___boxed(
    mut v_as_1516_: *mut leanh::LeanObject,
    mut v_as_x27_1517_: *mut leanh::LeanObject,
    mut v_b_1518_: *mut leanh::LeanObject,
    mut v_a_1519_: *mut leanh::LeanObject,
    mut v___y_1520_: *mut leanh::LeanObject,
    mut v___y_1521_: *mut leanh::LeanObject,
    mut v___y_1522_: *mut leanh::LeanObject,
    mut v___y_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
    mut v___y_1525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1526_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(v_as_1516_, v_as_x27_1517_, v_b_1518_, v_a_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
    leanh::lean_dec(v___y_1524_);
    leanh::lean_dec_ref(v___y_1523_);
    leanh::lean_dec(v___y_1522_);
    leanh::lean_dec_ref(v___y_1521_);
    leanh::lean_dec(v_as_x27_1517_);
    leanh::lean_dec(v_as_1516_);
    return v_res_1526_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(
    mut v_s_1527_: *mut leanh::LeanObject,
    mut v___y_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
    mut v___y_1530_: *mut leanh::LeanObject,
    mut v___y_1531_: *mut leanh::LeanObject,
    mut v___y_1532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_1527_, v___y_1528_);
    return v___x_1534_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___boxed(
    mut v_s_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
    mut v___y_1538_: *mut leanh::LeanObject,
    mut v___y_1539_: *mut leanh::LeanObject,
    mut v___y_1540_: *mut leanh::LeanObject,
    mut v___y_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(v_s_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
    leanh::lean_dec(v___y_1540_);
    leanh::lean_dec_ref(v___y_1539_);
    leanh::lean_dec(v___y_1538_);
    leanh::lean_dec_ref(v___y_1537_);
    return v_res_1542_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1;
    v___x_1547_ = l_Lean_MessageData_ofFormat(v___x_1546_);
    return v___x_1547_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0(
    mut v_x_1548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1549_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2);
    return v___x_1549_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(
    mut v_c_1553_: *mut leanh::LeanObject,
    mut v___y_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v_fst_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v_type_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_isSharedCheck_1592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1556_ = leanh::lean_ctor_get(v_c_1553_, 0);
                leanh::lean_inc_ref(v_lhs_1556_);
                v_rhs_1557_ = leanh::lean_ctor_get(v_c_1553_, 1);
                leanh::lean_inc_ref(v_rhs_1557_);
                leanh::lean_dec_ref(v_c_1553_);
                leanh::lean_inc_ref(v___y_1554_);
                v___x_1558_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_1556_, v___y_1554_);
                v_a_1559_ = leanh::lean_ctor_get(v___x_1558_, 0);
                leanh::lean_inc(v_a_1559_);
                leanh::lean_dec_ref(v___x_1558_);
                v_fst_1560_ = leanh::lean_ctor_get(v_a_1559_, 0);
                v_snd_1561_ = leanh::lean_ctor_get(v_a_1559_, 1);
                v_isSharedCheck_1592_ = (!leanh::lean_is_exclusive(v_a_1559_)) as u8;
                if v_isSharedCheck_1592_ == 0 {
                    v___x_1563_ = v_a_1559_;
                    v_isShared_1564_ = v_isSharedCheck_1592_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1561_);
                    leanh::lean_inc(v_fst_1560_);
                    leanh::lean_dec(v_a_1559_);
                    v___x_1563_ = leanh::lean_box(0);
                    v_isShared_1564_ = v_isSharedCheck_1592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1565_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_1557_, v_snd_1561_);
                v_a_1566_ = leanh::lean_ctor_get(v___x_1565_, 0);
                v_isSharedCheck_1591_ = (!leanh::lean_is_exclusive(v___x_1565_)) as u8;
                if v_isSharedCheck_1591_ == 0 {
                    v___x_1568_ = v___x_1565_;
                    v_isShared_1569_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1566_);
                    leanh::lean_dec(v___x_1565_);
                    v___x_1568_ = leanh::lean_box(0);
                    v_isShared_1569_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_1570_ = leanh::lean_ctor_get(v_a_1566_, 0);
                v_snd_1571_ = leanh::lean_ctor_get(v_a_1566_, 1);
                v_isSharedCheck_1590_ = (!leanh::lean_is_exclusive(v_a_1566_)) as u8;
                if v_isSharedCheck_1590_ == 0 {
                    v___x_1573_ = v_a_1566_;
                    v_isShared_1574_ = v_isSharedCheck_1590_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1571_);
                    leanh::lean_inc(v_fst_1570_);
                    leanh::lean_dec(v_a_1566_);
                    v___x_1573_ = leanh::lean_box(0);
                    v_isShared_1574_ = v_isSharedCheck_1590_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_type_1575_ = leanh::lean_ctor_get(v___y_1554_, 1);
                leanh::lean_inc_ref(v_type_1575_);
                v_u_1576_ = leanh::lean_ctor_get(v___y_1554_, 2);
                leanh::lean_inc(v_u_1576_);
                leanh::lean_dec_ref(v___y_1554_);
                v___x_1577_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1;
                v___x_1578_ = leanh::lean_box(0);
                if v_isShared_1564_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1563_, 1);
                    leanh::lean_ctor_set(v___x_1563_, 1, v___x_1578_);
                    leanh::lean_ctor_set(v___x_1563_, 0, v_u_1576_);
                    v___x_1580_ = v___x_1563_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_u_1576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1578_);
                    v___x_1580_ = v_reuseFailAlloc_1589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1581_ = l_Lean_mkConst(v___x_1577_, v___x_1580_);
                v___x_1582_ = l_Lean_mkApp3(v___x_1581_, v_type_1575_, v_fst_1560_, v_fst_1570_);
                if v_isShared_1574_ == 0 {
                    leanh::lean_ctor_set(v___x_1573_, 0, v___x_1582_);
                    v___x_1584_ = v___x_1573_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1588_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1582_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_snd_1571_);
                    v___x_1584_ = v_reuseFailAlloc_1588_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1569_ == 0 {
                    leanh::lean_ctor_set(v___x_1568_, 0, v___x_1584_);
                    v___x_1586_ = v___x_1568_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1587_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
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
    mut v_c_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1596_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_1593_, v___y_1594_);
    return v_res_1596_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(
    mut v_as_1597_: *mut leanh::LeanObject,
    mut v_sz_1598_: usize,
    mut v_i_1599_: usize,
    mut v_b_1600_: *mut leanh::LeanObject,
    mut v___y_1601_: *mut leanh::LeanObject,
    mut v___y_1602_: *mut leanh::LeanObject,
    mut v___y_1603_: *mut leanh::LeanObject,
    mut v___y_1604_: *mut leanh::LeanObject,
    mut v___y_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1618_: u8 = 0;
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: usize = 0;
    let mut v___x_1626_: usize = 0;
    let mut v_reuseFailAlloc_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut v_a_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1633_: u8 = 0;
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1607_ = lean_usize_dec_lt(v_i_1599_, v_sz_1598_);
                if v___x_1607_ == 0 {
                    v___x_1608_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1608_, 0, v_b_1600_);
                    leanh::lean_ctor_set(v___x_1608_, 1, v___y_1601_);
                    v___x_1609_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1609_, 0, v___x_1608_);
                    return v___x_1609_;
                } else {
                    v_snd_1610_ = leanh::lean_ctor_get(v_b_1600_, 1);
                    leanh::lean_inc(v_snd_1610_);
                    leanh::lean_dec_ref(v_b_1600_);
                    v_a_1611_ = lean_array_uget_borrowed(v_as_1597_, v_i_1599_);
                    leanh::lean_inc(v_a_1611_);
                    v___x_1612_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1611_, v___y_1601_);
                    if leanh::lean_obj_tag(v___x_1612_) == 0 {
                        v_a_1613_ = leanh::lean_ctor_get(v___x_1612_, 0);
                        leanh::lean_inc(v_a_1613_);
                        leanh::lean_dec_ref_known(v___x_1612_, 1);
                        v_fst_1614_ = leanh::lean_ctor_get(v_a_1613_, 0);
                        v_snd_1615_ = leanh::lean_ctor_get(v_a_1613_, 1);
                        v_isSharedCheck_1629_ = (!leanh::lean_is_exclusive(v_a_1613_)) as u8;
                        if v_isSharedCheck_1629_ == 0 {
                            v___x_1617_ = v_a_1613_;
                            v_isShared_1618_ = v_isSharedCheck_1629_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_1615_);
                            leanh::lean_inc(v_fst_1614_);
                            leanh::lean_dec(v_a_1613_);
                            v___x_1617_ = leanh::lean_box(0);
                            v_isShared_1618_ = v_isSharedCheck_1629_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_1610_);
                        v_a_1630_ = leanh::lean_ctor_get(v___x_1612_, 0);
                        v_isSharedCheck_1637_ =
                            (!leanh::lean_is_exclusive(v___x_1612_)) as u8;
                        if v_isSharedCheck_1637_ == 0 {
                            v___x_1632_ = v___x_1612_;
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1630_);
                            leanh::lean_dec(v___x_1612_);
                            v___x_1632_ = leanh::lean_box(0);
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1619_ = leanh::lean_box(0);
                v___x_1620_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1621_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1614_, v___x_1620_);
                v___x_1622_ = lean_array_push(v_snd_1610_, v___x_1621_);
                if v_isShared_1618_ == 0 {
                    leanh::lean_ctor_set(v___x_1617_, 1, v___x_1622_);
                    leanh::lean_ctor_set(v___x_1617_, 0, v___x_1619_);
                    v___x_1624_ = v___x_1617_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1628_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1622_);
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
                    v_reuseFailAlloc_1636_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
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
    mut v_as_1638_: *mut leanh::LeanObject,
    mut v_sz_1639_: *mut leanh::LeanObject,
    mut v_i_1640_: *mut leanh::LeanObject,
    mut v_b_1641_: *mut leanh::LeanObject,
    mut v___y_1642_: *mut leanh::LeanObject,
    mut v___y_1643_: *mut leanh::LeanObject,
    mut v___y_1644_: *mut leanh::LeanObject,
    mut v___y_1645_: *mut leanh::LeanObject,
    mut v___y_1646_: *mut leanh::LeanObject,
    mut v___y_1647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1648_: usize = 0;
    let mut v_i_boxed_1649_: usize = 0;
    let mut v_res_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1648_ = leanh::lean_unbox_usize(v_sz_1639_);
    leanh::lean_dec(v_sz_1639_);
    v_i_boxed_1649_ = leanh::lean_unbox_usize(v_i_1640_);
    leanh::lean_dec(v_i_1640_);
    v_res_1650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_1638_, v_sz_boxed_1648_, v_i_boxed_1649_, v_b_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
    leanh::lean_dec(v___y_1646_);
    leanh::lean_dec_ref(v___y_1645_);
    leanh::lean_dec(v___y_1644_);
    leanh::lean_dec_ref(v___y_1643_);
    leanh::lean_dec_ref(v_as_1638_);
    return v_res_1650_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(
    mut v_as_1651_: *mut leanh::LeanObject,
    mut v_sz_1652_: usize,
    mut v_i_1653_: usize,
    mut v_b_1654_: *mut leanh::LeanObject,
    mut v___y_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
    mut v___y_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: usize = 0;
    let mut v___x_1680_: usize = 0;
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut v_a_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1661_ = lean_usize_dec_lt(v_i_1653_, v_sz_1652_);
                if v___x_1661_ == 0 {
                    v___x_1662_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1662_, 0, v_b_1654_);
                    leanh::lean_ctor_set(v___x_1662_, 1, v___y_1655_);
                    v___x_1663_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1663_, 0, v___x_1662_);
                    return v___x_1663_;
                } else {
                    v_snd_1664_ = leanh::lean_ctor_get(v_b_1654_, 1);
                    leanh::lean_inc(v_snd_1664_);
                    leanh::lean_dec_ref(v_b_1654_);
                    v_a_1665_ = lean_array_uget_borrowed(v_as_1651_, v_i_1653_);
                    leanh::lean_inc(v_a_1665_);
                    v___x_1666_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1665_, v___y_1655_);
                    if leanh::lean_obj_tag(v___x_1666_) == 0 {
                        v_a_1667_ = leanh::lean_ctor_get(v___x_1666_, 0);
                        leanh::lean_inc(v_a_1667_);
                        leanh::lean_dec_ref_known(v___x_1666_, 1);
                        v_fst_1668_ = leanh::lean_ctor_get(v_a_1667_, 0);
                        v_snd_1669_ = leanh::lean_ctor_get(v_a_1667_, 1);
                        v_isSharedCheck_1683_ = (!leanh::lean_is_exclusive(v_a_1667_)) as u8;
                        if v_isSharedCheck_1683_ == 0 {
                            v___x_1671_ = v_a_1667_;
                            v_isShared_1672_ = v_isSharedCheck_1683_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_1669_);
                            leanh::lean_inc(v_fst_1668_);
                            leanh::lean_dec(v_a_1667_);
                            v___x_1671_ = leanh::lean_box(0);
                            v_isShared_1672_ = v_isSharedCheck_1683_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_1664_);
                        v_a_1684_ = leanh::lean_ctor_get(v___x_1666_, 0);
                        v_isSharedCheck_1691_ =
                            (!leanh::lean_is_exclusive(v___x_1666_)) as u8;
                        if v_isSharedCheck_1691_ == 0 {
                            v___x_1686_ = v___x_1666_;
                            v_isShared_1687_ = v_isSharedCheck_1691_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1684_);
                            leanh::lean_dec(v___x_1666_);
                            v___x_1686_ = leanh::lean_box(0);
                            v_isShared_1687_ = v_isSharedCheck_1691_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1673_ = leanh::lean_box(0);
                v___x_1674_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1675_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1668_, v___x_1674_);
                v___x_1676_ = lean_array_push(v_snd_1664_, v___x_1675_);
                if v_isShared_1672_ == 0 {
                    leanh::lean_ctor_set(v___x_1671_, 1, v___x_1676_);
                    leanh::lean_ctor_set(v___x_1671_, 0, v___x_1673_);
                    v___x_1678_ = v___x_1671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1673_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1676_);
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
                    v_reuseFailAlloc_1690_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
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
    mut v_as_1692_: *mut leanh::LeanObject,
    mut v_sz_1693_: *mut leanh::LeanObject,
    mut v_i_1694_: *mut leanh::LeanObject,
    mut v_b_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
    mut v___y_1700_: *mut leanh::LeanObject,
    mut v___y_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1702_: usize = 0;
    let mut v_i_boxed_1703_: usize = 0;
    let mut v_res_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1702_ = leanh::lean_unbox_usize(v_sz_1693_);
    leanh::lean_dec(v_sz_1693_);
    v_i_boxed_1703_ = leanh::lean_unbox_usize(v_i_1694_);
    leanh::lean_dec(v_i_1694_);
    v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_as_1692_, v_sz_boxed_1702_, v_i_boxed_1703_, v_b_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
    leanh::lean_dec(v___y_1700_);
    leanh::lean_dec_ref(v___y_1699_);
    leanh::lean_dec(v___y_1698_);
    leanh::lean_dec_ref(v___y_1697_);
    leanh::lean_dec_ref(v_as_1692_);
    return v_res_1704_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(
    mut v_as_1705_: *mut leanh::LeanObject,
    mut v_sz_1706_: usize,
    mut v_i_1707_: usize,
    mut v_b_1708_: *mut leanh::LeanObject,
    mut v___y_1709_: *mut leanh::LeanObject,
    mut v___y_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
    mut v___y_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: usize = 0;
    let mut v___x_1734_: usize = 0;
    let mut v_reuseFailAlloc_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_a_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1715_ = lean_usize_dec_lt(v_i_1707_, v_sz_1706_);
                if v___x_1715_ == 0 {
                    v___x_1716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1716_, 0, v_b_1708_);
                    leanh::lean_ctor_set(v___x_1716_, 1, v___y_1709_);
                    v___x_1717_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1717_, 0, v___x_1716_);
                    return v___x_1717_;
                } else {
                    v_snd_1718_ = leanh::lean_ctor_get(v_b_1708_, 1);
                    leanh::lean_inc(v_snd_1718_);
                    leanh::lean_dec_ref(v_b_1708_);
                    v_a_1719_ = lean_array_uget_borrowed(v_as_1705_, v_i_1707_);
                    leanh::lean_inc(v_a_1719_);
                    v___x_1720_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1719_, v___y_1709_);
                    if leanh::lean_obj_tag(v___x_1720_) == 0 {
                        v_a_1721_ = leanh::lean_ctor_get(v___x_1720_, 0);
                        leanh::lean_inc(v_a_1721_);
                        leanh::lean_dec_ref_known(v___x_1720_, 1);
                        v_fst_1722_ = leanh::lean_ctor_get(v_a_1721_, 0);
                        v_snd_1723_ = leanh::lean_ctor_get(v_a_1721_, 1);
                        v_isSharedCheck_1737_ = (!leanh::lean_is_exclusive(v_a_1721_)) as u8;
                        if v_isSharedCheck_1737_ == 0 {
                            v___x_1725_ = v_a_1721_;
                            v_isShared_1726_ = v_isSharedCheck_1737_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_1723_);
                            leanh::lean_inc(v_fst_1722_);
                            leanh::lean_dec(v_a_1721_);
                            v___x_1725_ = leanh::lean_box(0);
                            v_isShared_1726_ = v_isSharedCheck_1737_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_1718_);
                        v_a_1738_ = leanh::lean_ctor_get(v___x_1720_, 0);
                        v_isSharedCheck_1745_ =
                            (!leanh::lean_is_exclusive(v___x_1720_)) as u8;
                        if v_isSharedCheck_1745_ == 0 {
                            v___x_1740_ = v___x_1720_;
                            v_isShared_1741_ = v_isSharedCheck_1745_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1738_);
                            leanh::lean_dec(v___x_1720_);
                            v___x_1740_ = leanh::lean_box(0);
                            v_isShared_1741_ = v_isSharedCheck_1745_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1727_ = leanh::lean_box(0);
                v___x_1728_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1729_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1722_, v___x_1728_);
                v___x_1730_ = lean_array_push(v_snd_1718_, v___x_1729_);
                if v_isShared_1726_ == 0 {
                    leanh::lean_ctor_set(v___x_1725_, 1, v___x_1730_);
                    leanh::lean_ctor_set(v___x_1725_, 0, v___x_1727_);
                    v___x_1732_ = v___x_1725_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1730_);
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
                    v_reuseFailAlloc_1744_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
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
    mut v_as_1746_: *mut leanh::LeanObject,
    mut v_sz_1747_: *mut leanh::LeanObject,
    mut v_i_1748_: *mut leanh::LeanObject,
    mut v_b_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
    mut v___y_1753_: *mut leanh::LeanObject,
    mut v___y_1754_: *mut leanh::LeanObject,
    mut v___y_1755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1756_: usize = 0;
    let mut v_i_boxed_1757_: usize = 0;
    let mut v_res_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1756_ = leanh::lean_unbox_usize(v_sz_1747_);
    leanh::lean_dec(v_sz_1747_);
    v_i_boxed_1757_ = leanh::lean_unbox_usize(v_i_1748_);
    leanh::lean_dec(v_i_1748_);
    v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_1746_, v_sz_boxed_1756_, v_i_boxed_1757_, v_b_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
    leanh::lean_dec(v___y_1754_);
    leanh::lean_dec_ref(v___y_1753_);
    leanh::lean_dec(v___y_1752_);
    leanh::lean_dec_ref(v___y_1751_);
    leanh::lean_dec_ref(v_as_1746_);
    return v_res_1758_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(
    mut v_as_1759_: *mut leanh::LeanObject,
    mut v_sz_1760_: usize,
    mut v_i_1761_: usize,
    mut v_b_1762_: *mut leanh::LeanObject,
    mut v___y_1763_: *mut leanh::LeanObject,
    mut v___y_1764_: *mut leanh::LeanObject,
    mut v___y_1765_: *mut leanh::LeanObject,
    mut v___y_1766_: *mut leanh::LeanObject,
    mut v___y_1767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: usize = 0;
    let mut v___x_1788_: usize = 0;
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v_a_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1769_ = lean_usize_dec_lt(v_i_1761_, v_sz_1760_);
                if v___x_1769_ == 0 {
                    v___x_1770_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1770_, 0, v_b_1762_);
                    leanh::lean_ctor_set(v___x_1770_, 1, v___y_1763_);
                    v___x_1771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1771_, 0, v___x_1770_);
                    return v___x_1771_;
                } else {
                    v_snd_1772_ = leanh::lean_ctor_get(v_b_1762_, 1);
                    leanh::lean_inc(v_snd_1772_);
                    leanh::lean_dec_ref(v_b_1762_);
                    v_a_1773_ = lean_array_uget_borrowed(v_as_1759_, v_i_1761_);
                    leanh::lean_inc(v_a_1773_);
                    v___x_1774_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1773_, v___y_1763_);
                    if leanh::lean_obj_tag(v___x_1774_) == 0 {
                        v_a_1775_ = leanh::lean_ctor_get(v___x_1774_, 0);
                        leanh::lean_inc(v_a_1775_);
                        leanh::lean_dec_ref_known(v___x_1774_, 1);
                        v_fst_1776_ = leanh::lean_ctor_get(v_a_1775_, 0);
                        v_snd_1777_ = leanh::lean_ctor_get(v_a_1775_, 1);
                        v_isSharedCheck_1791_ = (!leanh::lean_is_exclusive(v_a_1775_)) as u8;
                        if v_isSharedCheck_1791_ == 0 {
                            v___x_1779_ = v_a_1775_;
                            v_isShared_1780_ = v_isSharedCheck_1791_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_1777_);
                            leanh::lean_inc(v_fst_1776_);
                            leanh::lean_dec(v_a_1775_);
                            v___x_1779_ = leanh::lean_box(0);
                            v_isShared_1780_ = v_isSharedCheck_1791_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_1772_);
                        v_a_1792_ = leanh::lean_ctor_get(v___x_1774_, 0);
                        v_isSharedCheck_1799_ =
                            (!leanh::lean_is_exclusive(v___x_1774_)) as u8;
                        if v_isSharedCheck_1799_ == 0 {
                            v___x_1794_ = v___x_1774_;
                            v_isShared_1795_ = v_isSharedCheck_1799_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1792_);
                            leanh::lean_dec(v___x_1774_);
                            v___x_1794_ = leanh::lean_box(0);
                            v_isShared_1795_ = v_isSharedCheck_1799_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1781_ = leanh::lean_box(0);
                v___x_1782_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1783_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1776_, v___x_1782_);
                v___x_1784_ = lean_array_push(v_snd_1772_, v___x_1783_);
                if v_isShared_1780_ == 0 {
                    leanh::lean_ctor_set(v___x_1779_, 1, v___x_1784_);
                    leanh::lean_ctor_set(v___x_1779_, 0, v___x_1781_);
                    v___x_1786_ = v___x_1779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1784_);
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
                    v_reuseFailAlloc_1798_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
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
    mut v_as_1800_: *mut leanh::LeanObject,
    mut v_sz_1801_: *mut leanh::LeanObject,
    mut v_i_1802_: *mut leanh::LeanObject,
    mut v_b_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
    mut v___y_1805_: *mut leanh::LeanObject,
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
    mut v___y_1808_: *mut leanh::LeanObject,
    mut v___y_1809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1810_: usize = 0;
    let mut v_i_boxed_1811_: usize = 0;
    let mut v_res_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1810_ = leanh::lean_unbox_usize(v_sz_1801_);
    leanh::lean_dec(v_sz_1801_);
    v_i_boxed_1811_ = leanh::lean_unbox_usize(v_i_1802_);
    leanh::lean_dec(v_i_1802_);
    v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_as_1800_, v_sz_boxed_1810_, v_i_boxed_1811_, v_b_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
    leanh::lean_dec(v___y_1808_);
    leanh::lean_dec_ref(v___y_1807_);
    leanh::lean_dec(v___y_1806_);
    leanh::lean_dec_ref(v___y_1805_);
    leanh::lean_dec_ref(v_as_1800_);
    return v_res_1812_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(
    mut v_init_1813_: *mut leanh::LeanObject,
    mut v_n_1814_: *mut leanh::LeanObject,
    mut v_b_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
    mut v___y_1818_: *mut leanh::LeanObject,
    mut v___y_1819_: *mut leanh::LeanObject,
    mut v___y_1820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1825_: usize = 0;
    let mut v___x_1826_: usize = 0;
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v_fst_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1838_: u8 = 0;
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v_unused_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v_snd_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1859_: u8 = 0;
    let mut v_unused_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_a_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_vs_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1874_: usize = 0;
    let mut v___x_1875_: usize = 0;
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v_fst_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1887_: u8 = 0;
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut v_unused_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1899_: u8 = 0;
    let mut v_snd_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut v_unused_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_a_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_1814_) == 0 {
                    v_cs_1822_ = leanh::lean_ctor_get(v_n_1814_, 0);
                    v___x_1823_ = leanh::lean_box(0);
                    v___x_1824_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1824_, 0, v___x_1823_);
                    leanh::lean_ctor_set(v___x_1824_, 1, v_b_1815_);
                    v_sz_1825_ = lean_array_size(v_cs_1822_);
                    v___x_1826_ = 0usize;
                    v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_1813_, v_cs_1822_, v_sz_1825_, v___x_1826_, v___x_1824_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
                    if leanh::lean_obj_tag(v___x_1827_) == 0 {
                        v_a_1828_ = leanh::lean_ctor_get(v___x_1827_, 0);
                        v_isSharedCheck_1862_ =
                            (!leanh::lean_is_exclusive(v___x_1827_)) as u8;
                        if v_isSharedCheck_1862_ == 0 {
                            v___x_1830_ = v___x_1827_;
                            v_isShared_1831_ = v_isSharedCheck_1862_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1828_);
                            leanh::lean_dec(v___x_1827_);
                            v___x_1830_ = leanh::lean_box(0);
                            v_isShared_1831_ = v_isSharedCheck_1862_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1863_ = leanh::lean_ctor_get(v___x_1827_, 0);
                        v_isSharedCheck_1870_ =
                            (!leanh::lean_is_exclusive(v___x_1827_)) as u8;
                        if v_isSharedCheck_1870_ == 0 {
                            v___x_1865_ = v___x_1827_;
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1863_);
                            leanh::lean_dec(v___x_1827_);
                            v___x_1865_ = leanh::lean_box(0);
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_vs_1871_ = leanh::lean_ctor_get(v_n_1814_, 0);
                    v___x_1872_ = leanh::lean_box(0);
                    v___x_1873_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                    leanh::lean_ctor_set(v___x_1873_, 1, v_b_1815_);
                    v_sz_1874_ = lean_array_size(v_vs_1871_);
                    v___x_1875_ = 0usize;
                    v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_vs_1871_, v_sz_1874_, v___x_1875_, v___x_1873_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
                    if leanh::lean_obj_tag(v___x_1876_) == 0 {
                        v_a_1877_ = leanh::lean_ctor_get(v___x_1876_, 0);
                        v_isSharedCheck_1911_ =
                            (!leanh::lean_is_exclusive(v___x_1876_)) as u8;
                        if v_isSharedCheck_1911_ == 0 {
                            v___x_1879_ = v___x_1876_;
                            v_isShared_1880_ = v_isSharedCheck_1911_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1877_);
                            leanh::lean_dec(v___x_1876_);
                            v___x_1879_ = leanh::lean_box(0);
                            v_isShared_1880_ = v_isSharedCheck_1911_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_a_1912_ = leanh::lean_ctor_get(v___x_1876_, 0);
                        v_isSharedCheck_1919_ =
                            (!leanh::lean_is_exclusive(v___x_1876_)) as u8;
                        if v_isSharedCheck_1919_ == 0 {
                            v___x_1914_ = v___x_1876_;
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1912_);
                            leanh::lean_dec(v___x_1876_);
                            v___x_1914_ = leanh::lean_box(0);
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1832_ = leanh::lean_ctor_get(v_a_1828_, 0);
                leanh::lean_inc(v_fst_1832_);
                v_fst_1833_ = leanh::lean_ctor_get(v_fst_1832_, 0);
                if leanh::lean_obj_tag(v_fst_1833_) == 0 {
                    v_snd_1834_ = leanh::lean_ctor_get(v_a_1828_, 1);
                    leanh::lean_inc(v_snd_1834_);
                    leanh::lean_dec(v_a_1828_);
                    v_snd_1835_ = leanh::lean_ctor_get(v_fst_1832_, 1);
                    v_isSharedCheck_1846_ = (!leanh::lean_is_exclusive(v_fst_1832_)) as u8;
                    if v_isSharedCheck_1846_ == 0 {
                        v_unused_1847_ = leanh::lean_ctor_get(v_fst_1832_, 0);
                        leanh::lean_dec(v_unused_1847_);
                        v___x_1837_ = v_fst_1832_;
                        v_isShared_1838_ = v_isSharedCheck_1846_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1835_);
                        leanh::lean_dec(v_fst_1832_);
                        v___x_1837_ = leanh::lean_box(0);
                        v_isShared_1838_ = v_isSharedCheck_1846_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_1833_);
                    v_isSharedCheck_1859_ = (!leanh::lean_is_exclusive(v_fst_1832_)) as u8;
                    if v_isSharedCheck_1859_ == 0 {
                        v_unused_1860_ = leanh::lean_ctor_get(v_fst_1832_, 1);
                        leanh::lean_dec(v_unused_1860_);
                        v_unused_1861_ = leanh::lean_ctor_get(v_fst_1832_, 0);
                        leanh::lean_dec(v_unused_1861_);
                        v___x_1849_ = v_fst_1832_;
                        v_isShared_1850_ = v_isSharedCheck_1859_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_1832_);
                        v___x_1849_ = leanh::lean_box(0);
                        v_isShared_1850_ = v_isSharedCheck_1859_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1839_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1839_, 0, v_snd_1835_);
                if v_isShared_1838_ == 0 {
                    leanh::lean_ctor_set(v___x_1837_, 1, v_snd_1834_);
                    leanh::lean_ctor_set(v___x_1837_, 0, v___x_1839_);
                    v___x_1841_ = v___x_1837_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_snd_1834_);
                    v___x_1841_ = v_reuseFailAlloc_1845_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1831_ == 0 {
                    leanh::lean_ctor_set(v___x_1830_, 0, v___x_1841_);
                    v___x_1843_ = v___x_1830_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1844_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
                    v___x_1843_ = v_reuseFailAlloc_1844_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1843_;
            }
            5 => {
                v_snd_1851_ = leanh::lean_ctor_get(v_a_1828_, 1);
                leanh::lean_inc(v_snd_1851_);
                leanh::lean_dec(v_a_1828_);
                v_val_1852_ = leanh::lean_ctor_get(v_fst_1833_, 0);
                leanh::lean_inc(v_val_1852_);
                leanh::lean_dec_ref_known(v_fst_1833_, 1);
                if v_isShared_1850_ == 0 {
                    leanh::lean_ctor_set(v___x_1849_, 1, v_snd_1851_);
                    leanh::lean_ctor_set(v___x_1849_, 0, v_val_1852_);
                    v___x_1854_ = v___x_1849_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_val_1852_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_snd_1851_);
                    v___x_1854_ = v_reuseFailAlloc_1858_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1831_ == 0 {
                    leanh::lean_ctor_set(v___x_1830_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1830_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
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
                    v_reuseFailAlloc_1869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
                    v___x_1868_ = v_reuseFailAlloc_1869_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1868_;
            }
            10 => {
                v_fst_1881_ = leanh::lean_ctor_get(v_a_1877_, 0);
                leanh::lean_inc(v_fst_1881_);
                v_fst_1882_ = leanh::lean_ctor_get(v_fst_1881_, 0);
                if leanh::lean_obj_tag(v_fst_1882_) == 0 {
                    v_snd_1883_ = leanh::lean_ctor_get(v_a_1877_, 1);
                    leanh::lean_inc(v_snd_1883_);
                    leanh::lean_dec(v_a_1877_);
                    v_snd_1884_ = leanh::lean_ctor_get(v_fst_1881_, 1);
                    v_isSharedCheck_1895_ = (!leanh::lean_is_exclusive(v_fst_1881_)) as u8;
                    if v_isSharedCheck_1895_ == 0 {
                        v_unused_1896_ = leanh::lean_ctor_get(v_fst_1881_, 0);
                        leanh::lean_dec(v_unused_1896_);
                        v___x_1886_ = v_fst_1881_;
                        v_isShared_1887_ = v_isSharedCheck_1895_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1884_);
                        leanh::lean_dec(v_fst_1881_);
                        v___x_1886_ = leanh::lean_box(0);
                        v_isShared_1887_ = v_isSharedCheck_1895_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_1882_);
                    v_isSharedCheck_1908_ = (!leanh::lean_is_exclusive(v_fst_1881_)) as u8;
                    if v_isSharedCheck_1908_ == 0 {
                        v_unused_1909_ = leanh::lean_ctor_get(v_fst_1881_, 1);
                        leanh::lean_dec(v_unused_1909_);
                        v_unused_1910_ = leanh::lean_ctor_get(v_fst_1881_, 0);
                        leanh::lean_dec(v_unused_1910_);
                        v___x_1898_ = v_fst_1881_;
                        v_isShared_1899_ = v_isSharedCheck_1908_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_1881_);
                        v___x_1898_ = leanh::lean_box(0);
                        v_isShared_1899_ = v_isSharedCheck_1908_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v___x_1888_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1888_, 0, v_snd_1884_);
                if v_isShared_1887_ == 0 {
                    leanh::lean_ctor_set(v___x_1886_, 1, v_snd_1883_);
                    leanh::lean_ctor_set(v___x_1886_, 0, v___x_1888_);
                    v___x_1890_ = v___x_1886_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1894_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_snd_1883_);
                    v___x_1890_ = v_reuseFailAlloc_1894_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1880_ == 0 {
                    leanh::lean_ctor_set(v___x_1879_, 0, v___x_1890_);
                    v___x_1892_ = v___x_1879_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1893_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
                    v___x_1892_ = v_reuseFailAlloc_1893_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1892_;
            }
            14 => {
                v_snd_1900_ = leanh::lean_ctor_get(v_a_1877_, 1);
                leanh::lean_inc(v_snd_1900_);
                leanh::lean_dec(v_a_1877_);
                v_val_1901_ = leanh::lean_ctor_get(v_fst_1882_, 0);
                leanh::lean_inc(v_val_1901_);
                leanh::lean_dec_ref_known(v_fst_1882_, 1);
                if v_isShared_1899_ == 0 {
                    leanh::lean_ctor_set(v___x_1898_, 1, v_snd_1900_);
                    leanh::lean_ctor_set(v___x_1898_, 0, v_val_1901_);
                    v___x_1903_ = v___x_1898_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_val_1901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_snd_1900_);
                    v___x_1903_ = v_reuseFailAlloc_1907_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1880_ == 0 {
                    leanh::lean_ctor_set(v___x_1879_, 0, v___x_1903_);
                    v___x_1905_ = v___x_1879_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
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
                    v_reuseFailAlloc_1918_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
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
    mut v_init_1920_: *mut leanh::LeanObject,
    mut v_as_1921_: *mut leanh::LeanObject,
    mut v_sz_1922_: usize,
    mut v_i_1923_: usize,
    mut v_b_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
    mut v___y_1927_: *mut leanh::LeanObject,
    mut v___y_1928_: *mut leanh::LeanObject,
    mut v___y_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1931_: u8 = 0;
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v_a_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1943_: u8 = 0;
    let mut v_fst_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v_unused_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v_a_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: usize = 0;
    let mut v___x_1970_: usize = 0;
    let mut v_reuseFailAlloc_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut v_unused_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut v_a_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_isSharedCheck_1984_: u8 = 0;
    let mut v_unused_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1931_ = lean_usize_dec_lt(v_i_1923_, v_sz_1922_);
                if v___x_1931_ == 0 {
                    v___x_1932_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1932_, 0, v_b_1924_);
                    leanh::lean_ctor_set(v___x_1932_, 1, v___y_1925_);
                    v___x_1933_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1933_, 0, v___x_1932_);
                    return v___x_1933_;
                } else {
                    v_snd_1934_ = leanh::lean_ctor_get(v_b_1924_, 1);
                    v_isSharedCheck_1984_ = (!leanh::lean_is_exclusive(v_b_1924_)) as u8;
                    if v_isSharedCheck_1984_ == 0 {
                        v_unused_1985_ = leanh::lean_ctor_get(v_b_1924_, 0);
                        leanh::lean_dec(v_unused_1985_);
                        v___x_1936_ = v_b_1924_;
                        v_isShared_1937_ = v_isSharedCheck_1984_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1934_);
                        leanh::lean_dec(v_b_1924_);
                        v___x_1936_ = leanh::lean_box(0);
                        v_isShared_1937_ = v_isSharedCheck_1984_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1938_ = lean_array_uget_borrowed(v_as_1921_, v_i_1923_);
                leanh::lean_inc(v_snd_1934_);
                v___x_1939_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_1920_, v_a_1938_, v_snd_1934_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
                if leanh::lean_obj_tag(v___x_1939_) == 0 {
                    v_a_1940_ = leanh::lean_ctor_get(v___x_1939_, 0);
                    v_isSharedCheck_1975_ = (!leanh::lean_is_exclusive(v___x_1939_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1942_ = v___x_1939_;
                        v_isShared_1943_ = v_isSharedCheck_1975_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1940_);
                        leanh::lean_dec(v___x_1939_);
                        v___x_1942_ = leanh::lean_box(0);
                        v_isShared_1943_ = v_isSharedCheck_1975_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1936_);
                    leanh::lean_dec(v_snd_1934_);
                    v_a_1976_ = leanh::lean_ctor_get(v___x_1939_, 0);
                    v_isSharedCheck_1983_ = (!leanh::lean_is_exclusive(v___x_1939_)) as u8;
                    if v_isSharedCheck_1983_ == 0 {
                        v___x_1978_ = v___x_1939_;
                        v_isShared_1979_ = v_isSharedCheck_1983_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1976_);
                        leanh::lean_dec(v___x_1939_);
                        v___x_1978_ = leanh::lean_box(0);
                        v_isShared_1979_ = v_isSharedCheck_1983_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1944_ = leanh::lean_ctor_get(v_a_1940_, 0);
                leanh::lean_inc(v_fst_1944_);
                if leanh::lean_obj_tag(v_fst_1944_) == 0 {
                    v_snd_1945_ = leanh::lean_ctor_get(v_a_1940_, 1);
                    v_isSharedCheck_1959_ = (!leanh::lean_is_exclusive(v_a_1940_)) as u8;
                    if v_isSharedCheck_1959_ == 0 {
                        v_unused_1960_ = leanh::lean_ctor_get(v_a_1940_, 0);
                        leanh::lean_dec(v_unused_1960_);
                        v___x_1947_ = v_a_1940_;
                        v_isShared_1948_ = v_isSharedCheck_1959_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1945_);
                        leanh::lean_dec(v_a_1940_);
                        v___x_1947_ = leanh::lean_box(0);
                        v_isShared_1948_ = v_isSharedCheck_1959_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1942_);
                    leanh::lean_del_object(v___x_1936_);
                    leanh::lean_dec(v_snd_1934_);
                    v_snd_1961_ = leanh::lean_ctor_get(v_a_1940_, 1);
                    v_isSharedCheck_1973_ = (!leanh::lean_is_exclusive(v_a_1940_)) as u8;
                    if v_isSharedCheck_1973_ == 0 {
                        v_unused_1974_ = leanh::lean_ctor_get(v_a_1940_, 0);
                        leanh::lean_dec(v_unused_1974_);
                        v___x_1963_ = v_a_1940_;
                        v_isShared_1964_ = v_isSharedCheck_1973_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1961_);
                        leanh::lean_dec(v_a_1940_);
                        v___x_1963_ = leanh::lean_box(0);
                        v_isShared_1964_ = v_isSharedCheck_1973_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1949_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1949_, 0, v_fst_1944_);
                if v_isShared_1948_ == 0 {
                    leanh::lean_ctor_set(v___x_1947_, 1, v_snd_1934_);
                    leanh::lean_ctor_set(v___x_1947_, 0, v___x_1949_);
                    v___x_1951_ = v___x_1947_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_snd_1934_);
                    v___x_1951_ = v_reuseFailAlloc_1958_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1937_ == 0 {
                    leanh::lean_ctor_set(v___x_1936_, 1, v_snd_1945_);
                    leanh::lean_ctor_set(v___x_1936_, 0, v___x_1951_);
                    v___x_1953_ = v___x_1936_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1957_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1951_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_snd_1945_);
                    v___x_1953_ = v_reuseFailAlloc_1957_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1943_ == 0 {
                    leanh::lean_ctor_set(v___x_1942_, 0, v___x_1953_);
                    v___x_1955_ = v___x_1942_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1956_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
                    v___x_1955_ = v_reuseFailAlloc_1956_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1955_;
            }
            7 => {
                v_a_1965_ = leanh::lean_ctor_get(v_fst_1944_, 0);
                leanh::lean_inc(v_a_1965_);
                leanh::lean_dec_ref_known(v_fst_1944_, 1);
                v___x_1966_ = leanh::lean_box(0);
                if v_isShared_1964_ == 0 {
                    leanh::lean_ctor_set(v___x_1963_, 1, v_a_1965_);
                    leanh::lean_ctor_set(v___x_1963_, 0, v___x_1966_);
                    v___x_1968_ = v___x_1963_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1966_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_a_1965_);
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
                    v_reuseFailAlloc_1982_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
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
    mut v_init_1986_: *mut leanh::LeanObject,
    mut v_as_1987_: *mut leanh::LeanObject,
    mut v_sz_1988_: *mut leanh::LeanObject,
    mut v_i_1989_: *mut leanh::LeanObject,
    mut v_b_1990_: *mut leanh::LeanObject,
    mut v___y_1991_: *mut leanh::LeanObject,
    mut v___y_1992_: *mut leanh::LeanObject,
    mut v___y_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
    mut v___y_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1997_: usize = 0;
    let mut v_i_boxed_1998_: usize = 0;
    let mut v_res_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1997_ = leanh::lean_unbox_usize(v_sz_1988_);
    leanh::lean_dec(v_sz_1988_);
    v_i_boxed_1998_ = leanh::lean_unbox_usize(v_i_1989_);
    leanh::lean_dec(v_i_1989_);
    v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_1986_, v_as_1987_, v_sz_boxed_1997_, v_i_boxed_1998_, v_b_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
    leanh::lean_dec(v___y_1995_);
    leanh::lean_dec_ref(v___y_1994_);
    leanh::lean_dec(v___y_1993_);
    leanh::lean_dec_ref(v___y_1992_);
    leanh::lean_dec_ref(v_as_1987_);
    leanh::lean_dec_ref(v_init_1986_);
    return v_res_1999_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1___boxed(
    mut v_init_2000_: *mut leanh::LeanObject,
    mut v_n_2001_: *mut leanh::LeanObject,
    mut v_b_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
    mut v___y_2006_: *mut leanh::LeanObject,
    mut v___y_2007_: *mut leanh::LeanObject,
    mut v___y_2008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_2000_, v_n_2001_, v_b_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
    leanh::lean_dec(v___y_2007_);
    leanh::lean_dec_ref(v___y_2006_);
    leanh::lean_dec(v___y_2005_);
    leanh::lean_dec_ref(v___y_2004_);
    leanh::lean_dec_ref(v_n_2001_);
    leanh::lean_dec_ref(v_init_2000_);
    return v_res_2009_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(
    mut v_t_2010_: *mut leanh::LeanObject,
    mut v_init_2011_: *mut leanh::LeanObject,
    mut v___y_2012_: *mut leanh::LeanObject,
    mut v___y_2013_: *mut leanh::LeanObject,
    mut v___y_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2033_: u8 = 0;
    let mut v_a_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2038_: usize = 0;
    let mut v___x_2039_: usize = 0;
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2044_: u8 = 0;
    let mut v_fst_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_unused_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2062_: u8 = 0;
    let mut v_a_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2066_: u8 = 0;
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_reuseFailAlloc_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v_unused_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2023_ = leanh::lean_ctor_get(v_t_2010_, 0);
                v_tail_2024_ = leanh::lean_ctor_get(v_t_2010_, 1);
                leanh::lean_inc_ref(v_init_2011_);
                v___x_2025_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_2011_, v_root_2023_, v_init_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
                leanh::lean_dec_ref(v_init_2011_);
                if leanh::lean_obj_tag(v___x_2025_) == 0 {
                    v_a_2026_ = leanh::lean_ctor_get(v___x_2025_, 0);
                    leanh::lean_inc(v_a_2026_);
                    leanh::lean_dec_ref_known(v___x_2025_, 1);
                    v_fst_2027_ = leanh::lean_ctor_get(v_a_2026_, 0);
                    leanh::lean_inc(v_fst_2027_);
                    if leanh::lean_obj_tag(v_fst_2027_) == 0 {
                        v_snd_2028_ = leanh::lean_ctor_get(v_a_2026_, 1);
                        leanh::lean_inc(v_snd_2028_);
                        leanh::lean_dec(v_a_2026_);
                        v_a_2029_ = leanh::lean_ctor_get(v_fst_2027_, 0);
                        leanh::lean_inc(v_a_2029_);
                        leanh::lean_dec_ref_known(v_fst_2027_, 1);
                        v_b_2019_ = v_a_2029_;
                        v___y_2020_ = v_snd_2028_;
                        state = 1;
                        continue;
                    } else {
                        v_snd_2030_ = leanh::lean_ctor_get(v_a_2026_, 1);
                        v_isSharedCheck_2072_ = (!leanh::lean_is_exclusive(v_a_2026_)) as u8;
                        if v_isSharedCheck_2072_ == 0 {
                            v_unused_2073_ = leanh::lean_ctor_get(v_a_2026_, 0);
                            leanh::lean_dec(v_unused_2073_);
                            v___x_2032_ = v_a_2026_;
                            v_isShared_2033_ = v_isSharedCheck_2072_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_2030_);
                            leanh::lean_dec(v_a_2026_);
                            v___x_2032_ = leanh::lean_box(0);
                            v_isShared_2033_ = v_isSharedCheck_2072_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_a_2074_ = leanh::lean_ctor_get(v___x_2025_, 0);
                    v_isSharedCheck_2081_ = (!leanh::lean_is_exclusive(v___x_2025_)) as u8;
                    if v_isSharedCheck_2081_ == 0 {
                        v___x_2076_ = v___x_2025_;
                        v_isShared_2077_ = v_isSharedCheck_2081_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2074_);
                        leanh::lean_dec(v___x_2025_);
                        v___x_2076_ = leanh::lean_box(0);
                        v_isShared_2077_ = v_isSharedCheck_2081_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2021_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2021_, 0, v_b_2019_);
                leanh::lean_ctor_set(v___x_2021_, 1, v___y_2020_);
                v___x_2022_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2022_, 0, v___x_2021_);
                return v___x_2022_;
            }
            2 => {
                v_a_2034_ = leanh::lean_ctor_get(v_fst_2027_, 0);
                leanh::lean_inc(v_a_2034_);
                leanh::lean_dec_ref_known(v_fst_2027_, 1);
                v___x_2035_ = leanh::lean_box(0);
                if v_isShared_2033_ == 0 {
                    leanh::lean_ctor_set(v___x_2032_, 1, v_a_2034_);
                    leanh::lean_ctor_set(v___x_2032_, 0, v___x_2035_);
                    v___x_2037_ = v___x_2032_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2071_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_a_2034_);
                    v___x_2037_ = v_reuseFailAlloc_2071_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_sz_2038_ = lean_array_size(v_tail_2024_);
                v___x_2039_ = 0usize;
                v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_tail_2024_, v_sz_2038_, v___x_2039_, v___x_2037_, v_snd_2030_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
                if leanh::lean_obj_tag(v___x_2040_) == 0 {
                    v_a_2041_ = leanh::lean_ctor_get(v___x_2040_, 0);
                    v_isSharedCheck_2062_ = (!leanh::lean_is_exclusive(v___x_2040_)) as u8;
                    if v_isSharedCheck_2062_ == 0 {
                        v___x_2043_ = v___x_2040_;
                        v_isShared_2044_ = v_isSharedCheck_2062_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2041_);
                        leanh::lean_dec(v___x_2040_);
                        v___x_2043_ = leanh::lean_box(0);
                        v_isShared_2044_ = v_isSharedCheck_2062_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2063_ = leanh::lean_ctor_get(v___x_2040_, 0);
                    v_isSharedCheck_2070_ = (!leanh::lean_is_exclusive(v___x_2040_)) as u8;
                    if v_isSharedCheck_2070_ == 0 {
                        v___x_2065_ = v___x_2040_;
                        v_isShared_2066_ = v_isSharedCheck_2070_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2063_);
                        leanh::lean_dec(v___x_2040_);
                        v___x_2065_ = leanh::lean_box(0);
                        v_isShared_2066_ = v_isSharedCheck_2070_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2045_ = leanh::lean_ctor_get(v_a_2041_, 0);
                leanh::lean_inc(v_fst_2045_);
                v_fst_2046_ = leanh::lean_ctor_get(v_fst_2045_, 0);
                if leanh::lean_obj_tag(v_fst_2046_) == 0 {
                    v_snd_2047_ = leanh::lean_ctor_get(v_a_2041_, 1);
                    leanh::lean_inc(v_snd_2047_);
                    leanh::lean_dec(v_a_2041_);
                    v_snd_2048_ = leanh::lean_ctor_get(v_fst_2045_, 1);
                    v_isSharedCheck_2058_ = (!leanh::lean_is_exclusive(v_fst_2045_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v_unused_2059_ = leanh::lean_ctor_get(v_fst_2045_, 0);
                        leanh::lean_dec(v_unused_2059_);
                        v___x_2050_ = v_fst_2045_;
                        v_isShared_2051_ = v_isSharedCheck_2058_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2048_);
                        leanh::lean_dec(v_fst_2045_);
                        v___x_2050_ = leanh::lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2058_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2046_);
                    leanh::lean_dec(v_fst_2045_);
                    leanh::lean_del_object(v___x_2043_);
                    v_snd_2060_ = leanh::lean_ctor_get(v_a_2041_, 1);
                    leanh::lean_inc(v_snd_2060_);
                    leanh::lean_dec(v_a_2041_);
                    v_val_2061_ = leanh::lean_ctor_get(v_fst_2046_, 0);
                    leanh::lean_inc(v_val_2061_);
                    leanh::lean_dec_ref_known(v_fst_2046_, 1);
                    v_b_2019_ = v_val_2061_;
                    v___y_2020_ = v_snd_2060_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_2051_ == 0 {
                    leanh::lean_ctor_set(v___x_2050_, 1, v_snd_2047_);
                    leanh::lean_ctor_set(v___x_2050_, 0, v_snd_2048_);
                    v___x_2053_ = v___x_2050_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_snd_2048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_snd_2047_);
                    v___x_2053_ = v_reuseFailAlloc_2057_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2044_ == 0 {
                    leanh::lean_ctor_set(v___x_2043_, 0, v___x_2053_);
                    v___x_2055_ = v___x_2043_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2056_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
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
                    v_reuseFailAlloc_2069_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
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
                    v_reuseFailAlloc_2080_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
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
    mut v_t_2082_: *mut leanh::LeanObject,
    mut v_init_2083_: *mut leanh::LeanObject,
    mut v___y_2084_: *mut leanh::LeanObject,
    mut v___y_2085_: *mut leanh::LeanObject,
    mut v___y_2086_: *mut leanh::LeanObject,
    mut v___y_2087_: *mut leanh::LeanObject,
    mut v___y_2088_: *mut leanh::LeanObject,
    mut v___y_2089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_t_2082_, v_init_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
    leanh::lean_dec(v___y_2088_);
    leanh::lean_dec_ref(v___y_2087_);
    leanh::lean_dec(v___y_2086_);
    leanh::lean_dec_ref(v___y_2085_);
    leanh::lean_dec_ref(v_t_2082_);
    return v_res_2090_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3()
-> *mut leanh::LeanObject {
    let mut v___f_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2095_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0;
    v___x_2096_ = lean_mk_thunk(v___f_2095_);
    return v___x_2096_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(
    mut v_a_2097_: *mut leanh::LeanObject,
    mut v_a_2098_: *mut leanh::LeanObject,
    mut v_a_2099_: *mut leanh::LeanObject,
    mut v_a_2100_: *mut leanh::LeanObject,
    mut v_a_2101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_diseqs_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v_fst_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut v_a_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2129_: u8 = 0;
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_diseqs_2103_ = leanh::lean_ctor_get(v_a_2097_, 16);
                leanh::lean_inc_ref(v_diseqs_2103_);
                v_diseqs_2104_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
                v___x_2105_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_diseqs_2103_, v_diseqs_2104_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
                leanh::lean_dec_ref(v_diseqs_2103_);
                if leanh::lean_obj_tag(v___x_2105_) == 0 {
                    v_a_2106_ = leanh::lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2125_ = (!leanh::lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2125_ == 0 {
                        v___x_2108_ = v___x_2105_;
                        v_isShared_2109_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2106_);
                        leanh::lean_dec(v___x_2105_);
                        v___x_2108_ = leanh::lean_box(0);
                        v_isShared_2109_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2126_ = leanh::lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2133_ = (!leanh::lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2133_ == 0 {
                        v___x_2128_ = v___x_2105_;
                        v_isShared_2129_ = v_isSharedCheck_2133_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2126_);
                        leanh::lean_dec(v___x_2105_);
                        v___x_2128_ = leanh::lean_box(0);
                        v_isShared_2129_ = v_isSharedCheck_2133_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2110_ = leanh::lean_ctor_get(v_a_2106_, 0);
                v_snd_2111_ = leanh::lean_ctor_get(v_a_2106_, 1);
                v_isSharedCheck_2124_ = (!leanh::lean_is_exclusive(v_a_2106_)) as u8;
                if v_isSharedCheck_2124_ == 0 {
                    v___x_2113_ = v_a_2106_;
                    v_isShared_2114_ = v_isSharedCheck_2124_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2111_);
                    leanh::lean_inc(v_fst_2110_);
                    leanh::lean_dec(v_a_2106_);
                    v___x_2113_ = leanh::lean_box(0);
                    v_isShared_2114_ = v_isSharedCheck_2124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2115_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2;
                v___x_2116_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3);
                v___x_2117_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
                        v___x_2115_,
                        v___x_2116_,
                        v_fst_2110_,
                    );
                if v_isShared_2114_ == 0 {
                    leanh::lean_ctor_set(v___x_2113_, 0, v___x_2117_);
                    v___x_2119_ = v___x_2113_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2117_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_snd_2111_);
                    v___x_2119_ = v_reuseFailAlloc_2123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2109_ == 0 {
                    leanh::lean_ctor_set(v___x_2108_, 0, v___x_2119_);
                    v___x_2121_ = v___x_2108_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2122_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
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
                    v_reuseFailAlloc_2132_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
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
    mut v_a_2134_: *mut leanh::LeanObject,
    mut v_a_2135_: *mut leanh::LeanObject,
    mut v_a_2136_: *mut leanh::LeanObject,
    mut v_a_2137_: *mut leanh::LeanObject,
    mut v_a_2138_: *mut leanh::LeanObject,
    mut v_a_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(
        v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_,
    );
    leanh::lean_dec(v_a_2138_);
    leanh::lean_dec_ref(v_a_2137_);
    leanh::lean_dec(v_a_2136_);
    leanh::lean_dec_ref(v_a_2135_);
    return v_res_2140_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(
    mut v_c_2141_: *mut leanh::LeanObject,
    mut v___y_2142_: *mut leanh::LeanObject,
    mut v___y_2143_: *mut leanh::LeanObject,
    mut v___y_2144_: *mut leanh::LeanObject,
    mut v___y_2145_: *mut leanh::LeanObject,
    mut v___y_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2148_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_2141_, v___y_2142_);
    return v___x_2148_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___boxed(
    mut v_c_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
    mut v___y_2153_: *mut leanh::LeanObject,
    mut v___y_2154_: *mut leanh::LeanObject,
    mut v___y_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(v_c_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
    leanh::lean_dec(v___y_2154_);
    leanh::lean_dec_ref(v___y_2153_);
    leanh::lean_dec(v___y_2152_);
    leanh::lean_dec_ref(v___y_2151_);
    return v_res_2156_;
}
pub unsafe fn l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(
    mut v_e_2157_: *mut leanh::LeanObject,
    mut v_cls_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: f64 = 0.0;
    let mut v___x_2161_: u8 = 0;
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = leanh::lean_box(0);
    v___x_2160_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_2161_ = 1;
    v___x_2162_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_2163_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
    leanh::lean_ctor_set(v___x_2163_, 0, v_cls_2158_);
    leanh::lean_ctor_set(v___x_2163_, 1, v___x_2159_);
    leanh::lean_ctor_set(v___x_2163_, 2, v___x_2162_);
    leanh::lean_ctor_set_float(
        v___x_2163_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2160_,
    );
    leanh::lean_ctor_set_float(
        v___x_2163_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        v___x_2160_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2163_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
        v___x_2161_,
    );
    v___x_2164_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_2165_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2165_, 0, v___x_2163_);
    leanh::lean_ctor_set(v___x_2165_, 1, v_e_2157_);
    leanh::lean_ctor_set(v___x_2165_, 2, v___x_2164_);
    return v___x_2165_;
}
pub unsafe fn l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(
    mut v_e_2166_: *mut leanh::LeanObject,
    mut v_cls_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: f64 = 0.0;
    let mut v___x_2170_: u8 = 0;
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2168_ = leanh::lean_box(0);
    v___x_2169_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_2170_ = 1;
    v___x_2171_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_2172_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
    leanh::lean_ctor_set(v___x_2172_, 0, v_cls_2167_);
    leanh::lean_ctor_set(v___x_2172_, 1, v___x_2168_);
    leanh::lean_ctor_set(v___x_2172_, 2, v___x_2171_);
    leanh::lean_ctor_set_float(
        v___x_2172_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2169_,
    );
    leanh::lean_ctor_set_float(
        v___x_2172_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        v___x_2169_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2172_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
        v___x_2170_,
    );
    v___x_2173_ = l_Lean_stringToMessageData(v_e_2166_);
    v___x_2174_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_2175_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2175_, 0, v___x_2172_);
    leanh::lean_ctor_set(v___x_2175_, 1, v___x_2173_);
    leanh::lean_ctor_set(v___x_2175_, 2, v___x_2174_);
    return v___x_2175_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2177_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0;
    v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
    return v___x_2178_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2;
    v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0(
    mut v___y_2182_: *mut leanh::LeanObject,
    mut v_x_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_op_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_op_2184_ = leanh::lean_ctor_get(v___y_2182_, 3);
    leanh::lean_inc_ref(v_op_2184_);
    leanh::lean_dec_ref(v___y_2182_);
    v___x_2185_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1);
    v___x_2186_ = l_Lean_MessageData_ofExpr(v_op_2184_);
    v___x_2187_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2187_, 0, v___x_2185_);
    leanh::lean_ctor_set(v___x_2187_, 1, v___x_2186_);
    v___x_2188_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
    v___x_2189_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2189_, 0, v___x_2187_);
    leanh::lean_ctor_set(v___x_2189_, 1, v___x_2188_);
    return v___x_2189_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2193_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1;
    v___x_2194_ = l_Lean_MessageData_ofFormat(v___x_2193_);
    return v___x_2194_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1(
    mut v_x_2195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2);
    return v___x_2196_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5()
-> *mut leanh::LeanObject {
    let mut v___f_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2204_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2;
    v___x_2205_ = lean_mk_thunk(v___f_2204_);
    return v___x_2205_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2207_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6;
    v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
    return v___x_2208_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2210_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
    v___x_2211_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8;
    v___x_2212_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_2211_, v___x_2210_);
    return v___x_2212_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2214_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
    v___x_2215_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10;
    v___x_2216_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_2215_, v___x_2214_);
    return v___x_2216_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11);
    v_msgs_2218_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_2219_ = lean_array_push(v_msgs_2218_, v___x_2217_);
    return v___x_2219_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(
    mut v_a_2220_: *mut leanh::LeanObject,
    mut v_a_2221_: *mut leanh::LeanObject,
    mut v_a_2222_: *mut leanh::LeanObject,
    mut v_a_2223_: *mut leanh::LeanObject,
    mut v_a_2224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_msgs_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: u8 = 0;
    let mut v_neutral_x3f_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idempotentInst_x3f_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commInst_x3f_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idempotentInst_x3f_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2235_) == 0 {
                    v_a_2236_ = leanh::lean_ctor_get(v___x_2235_, 0);
                    leanh::lean_inc(v_a_2236_);
                    leanh::lean_dec_ref_known(v___x_2235_, 1);
                    v_fst_2237_ = leanh::lean_ctor_get(v_a_2236_, 0);
                    v_snd_2238_ = leanh::lean_ctor_get(v_a_2236_, 1);
                    v_isSharedCheck_2296_ = (!leanh::lean_is_exclusive(v_a_2236_)) as u8;
                    if v_isSharedCheck_2296_ == 0 {
                        v___x_2240_ = v_a_2236_;
                        v_isShared_2241_ = v_isSharedCheck_2296_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2238_);
                        leanh::lean_inc(v_fst_2237_);
                        leanh::lean_dec(v_a_2236_);
                        v___x_2240_ = leanh::lean_box(0);
                        v_isShared_2241_ = v_isSharedCheck_2296_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2235_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_2228_);
                v___f_2229_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_2229_, 0, v___y_2228_);
                v___x_2230_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1;
                v___x_2231_ = lean_mk_thunk(v___f_2229_);
                v___x_2232_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
                        v___x_2230_,
                        v___x_2231_,
                        v_msgs_2227_,
                    );
                leanh::lean_dec_ref(v___x_2231_);
                v___x_2233_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2233_, 0, v___x_2232_);
                leanh::lean_ctor_set(v___x_2233_, 1, v___y_2228_);
                v___x_2234_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2234_, 0, v___x_2233_);
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
                if leanh::lean_obj_tag(v___x_2242_) == 0 {
                    v_a_2243_ = leanh::lean_ctor_get(v___x_2242_, 0);
                    leanh::lean_inc(v_a_2243_);
                    leanh::lean_dec_ref_known(v___x_2242_, 1);
                    v_fst_2244_ = leanh::lean_ctor_get(v_a_2243_, 0);
                    v_snd_2245_ = leanh::lean_ctor_get(v_a_2243_, 1);
                    v_isSharedCheck_2295_ = (!leanh::lean_is_exclusive(v_a_2243_)) as u8;
                    if v_isSharedCheck_2295_ == 0 {
                        v___x_2247_ = v_a_2243_;
                        v_isShared_2248_ = v_isSharedCheck_2295_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2245_);
                        leanh::lean_inc(v_fst_2244_);
                        leanh::lean_dec(v_a_2243_);
                        v___x_2247_ = leanh::lean_box(0);
                        v_isShared_2248_ = v_isSharedCheck_2295_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2240_);
                    leanh::lean_dec(v_fst_2237_);
                    return v___x_2242_;
                }
            }
            3 => {
                v___x_2249_ = leanh::lean_unsigned_to_nat(0);
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
                    v_neutral_x3f_2255_ = leanh::lean_ctor_get(v_snd_2245_, 4);
                    leanh::lean_inc(v_neutral_x3f_2255_);
                    v_idempotentInst_x3f_2256_ = leanh::lean_ctor_get(v_snd_2245_, 6);
                    leanh::lean_inc(v_idempotentInst_x3f_2256_);
                    v_commInst_x3f_2257_ = leanh::lean_ctor_get(v_snd_2245_, 7);
                    if leanh::lean_obj_tag(v_commInst_x3f_2257_) == 0 {
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
                    leanh::lean_del_object(v___x_2247_);
                    leanh::lean_del_object(v___x_2240_);
                    v_msgs_2227_ = v___x_2252_;
                    v___y_2228_ = v_snd_2245_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_2261_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4;
                v___x_2262_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5);
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
                if leanh::lean_obj_tag(v_neutral_x3f_2268_) == 1 {
                    v_val_2269_ = leanh::lean_ctor_get(v_neutral_x3f_2268_, 0);
                    leanh::lean_inc(v_val_2269_);
                    leanh::lean_dec_ref_known(v_neutral_x3f_2268_, 1);
                    v___x_2270_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7);
                    v___x_2271_ = l_Lean_MessageData_ofExpr(v_val_2269_);
                    if v_isShared_2248_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2247_, 7);
                        leanh::lean_ctor_set(v___x_2247_, 1, v___x_2271_);
                        leanh::lean_ctor_set(v___x_2247_, 0, v___x_2270_);
                        v___x_2273_ = v___x_2247_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2281_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2270_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2271_);
                        v___x_2273_ = v_reuseFailAlloc_2281_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_neutral_x3f_2268_);
                    leanh::lean_del_object(v___x_2247_);
                    leanh::lean_del_object(v___x_2240_);
                    v_info_2259_ = v_info_2266_;
                    v___y_2260_ = v___y_2267_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_2274_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
                if v_isShared_2241_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2240_, 7);
                    leanh::lean_ctor_set(v___x_2240_, 1, v___x_2274_);
                    leanh::lean_ctor_set(v___x_2240_, 0, v___x_2273_);
                    v___x_2276_ = v___x_2240_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2280_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2274_);
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
                v_neutral_x3f_2285_ = leanh::lean_ctor_get(v___y_2283_, 4);
                leanh::lean_inc(v_neutral_x3f_2285_);
                v___x_2286_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9);
                v___x_2287_ = lean_array_push(v___y_2284_, v___x_2286_);
                v_info_2266_ = v___x_2287_;
                v___y_2267_ = v___y_2283_;
                v_neutral_x3f_2268_ = v_neutral_x3f_2285_;
                state = 5;
                continue;
            }
            9 => {
                if leanh::lean_obj_tag(v_idempotentInst_x3f_2292_) == 0 {
                    if v___x_2254_ == 0 {
                        v_info_2266_ = v_info_2289_;
                        v___y_2267_ = v___y_2290_;
                        v_neutral_x3f_2268_ = v_neutral_x3f_2291_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_neutral_x3f_2291_);
                        v___y_2283_ = v___y_2290_;
                        v___y_2284_ = v_info_2289_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_idempotentInst_x3f_2292_, 1);
                    leanh::lean_dec(v_neutral_x3f_2291_);
                    v___y_2283_ = v___y_2290_;
                    v___y_2284_ = v_info_2289_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_2294_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12);
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
    mut v_a_2297_: *mut leanh::LeanObject,
    mut v_a_2298_: *mut leanh::LeanObject,
    mut v_a_2299_: *mut leanh::LeanObject,
    mut v_a_2300_: *mut leanh::LeanObject,
    mut v_a_2301_: *mut leanh::LeanObject,
    mut v_a_2302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2303_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(
        v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_,
    );
    leanh::lean_dec(v_a_2301_);
    leanh::lean_dec_ref(v_a_2300_);
    leanh::lean_dec(v_a_2299_);
    leanh::lean_dec_ref(v_a_2298_);
    return v_res_2303_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(
    mut v_as_2304_: *mut leanh::LeanObject,
    mut v_sz_2305_: usize,
    mut v_i_2306_: usize,
    mut v_b_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: usize = 0;
    let mut v___x_2316_: usize = 0;
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2318_ = lean_usize_dec_lt(v_i_2306_, v_sz_2305_);
                if v___x_2318_ == 0 {
                    v___x_2319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2319_, 0, v_b_2307_);
                    return v___x_2319_;
                } else {
                    v_a_2320_ = lean_array_uget_borrowed(v_as_2304_, v_i_2306_);
                    leanh::lean_inc(v_a_2320_);
                    v___x_2321_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(
                            v_a_2320_,
                            v___y_2308_,
                            v___y_2309_,
                            v___y_2310_,
                            v___y_2311_,
                        );
                    if leanh::lean_obj_tag(v___x_2321_) == 0 {
                        v_a_2322_ = leanh::lean_ctor_get(v___x_2321_, 0);
                        leanh::lean_inc(v_a_2322_);
                        leanh::lean_dec_ref_known(v___x_2321_, 1);
                        v_fst_2323_ = leanh::lean_ctor_get(v_a_2322_, 0);
                        leanh::lean_inc(v_fst_2323_);
                        leanh::lean_dec(v_a_2322_);
                        if leanh::lean_obj_tag(v_fst_2323_) == 1 {
                            v_val_2324_ = leanh::lean_ctor_get(v_fst_2323_, 0);
                            leanh::lean_inc(v_val_2324_);
                            leanh::lean_dec_ref_known(v_fst_2323_, 1);
                            v___x_2325_ = lean_array_push(v_b_2307_, v_val_2324_);
                            v_a_2314_ = v___x_2325_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_fst_2323_);
                            v_a_2314_ = v_b_2307_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_2307_);
                        v_a_2326_ = leanh::lean_ctor_get(v___x_2321_, 0);
                        v_isSharedCheck_2333_ =
                            (!leanh::lean_is_exclusive(v___x_2321_)) as u8;
                        if v_isSharedCheck_2333_ == 0 {
                            v___x_2328_ = v___x_2321_;
                            v_isShared_2329_ = v_isSharedCheck_2333_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2326_);
                            leanh::lean_dec(v___x_2321_);
                            v___x_2328_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2332_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
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
    mut v_as_2334_: *mut leanh::LeanObject,
    mut v_sz_2335_: *mut leanh::LeanObject,
    mut v_i_2336_: *mut leanh::LeanObject,
    mut v_b_2337_: *mut leanh::LeanObject,
    mut v___y_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2343_: usize = 0;
    let mut v_i_boxed_2344_: usize = 0;
    let mut v_res_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2343_ = leanh::lean_unbox_usize(v_sz_2335_);
    leanh::lean_dec(v_sz_2335_);
    v_i_boxed_2344_ = leanh::lean_unbox_usize(v_i_2336_);
    leanh::lean_dec(v_i_2336_);
    v_res_2345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_as_2334_, v_sz_boxed_2343_, v_i_boxed_2344_, v_b_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
    leanh::lean_dec(v___y_2341_);
    leanh::lean_dec_ref(v___y_2340_);
    leanh::lean_dec(v___y_2339_);
    leanh::lean_dec_ref(v___y_2338_);
    leanh::lean_dec_ref(v_as_2334_);
    return v_res_2345_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: f64 = 0.0;
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2346_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_2347_ = 1;
    v___x_2348_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_2349_ = leanh::lean_box(0);
    v___x_2350_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1;
    v___x_2351_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
    leanh::lean_ctor_set(v___x_2351_, 0, v___x_2350_);
    leanh::lean_ctor_set(v___x_2351_, 1, v___x_2349_);
    leanh::lean_ctor_set(v___x_2351_, 2, v___x_2346_);
    leanh::lean_ctor_set_float(
        v___x_2351_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2348_,
    );
    leanh::lean_ctor_set_float(
        v___x_2351_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
        v___x_2348_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2351_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
        v___x_2347_,
    );
    return v___x_2351_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Lean_Meta_Grind_AC_pp_x3f___closed__2;
    v___x_2356_ = l_Lean_MessageData_ofFormat(v___x_2355_);
    return v___x_2356_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_pp_x3f(
    mut v_goal_2357_: *mut leanh::LeanObject,
    mut v_a_2358_: *mut leanh::LeanObject,
    mut v_a_2359_: *mut leanh::LeanObject,
    mut v_a_2360_: *mut leanh::LeanObject,
    mut v_a_2361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_structs_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2369_: usize = 0;
    let mut v___x_2370_: usize = 0;
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut v_a_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2404_: u8 = 0;
    let mut v_a_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v_ref_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2363_ = l_Lean_Meta_Grind_AC_acExt;
                v___x_2364_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2363_, v_goal_2357_);
                if leanh::lean_obj_tag(v___x_2364_) == 0 {
                    v_a_2365_ = leanh::lean_ctor_get(v___x_2364_, 0);
                    leanh::lean_inc(v_a_2365_);
                    leanh::lean_dec_ref_known(v___x_2364_, 1);
                    v_structs_2366_ = leanh::lean_ctor_get(v_a_2365_, 0);
                    leanh::lean_inc_ref(v_structs_2366_);
                    leanh::lean_dec(v_a_2365_);
                    v___x_2367_ = leanh::lean_unsigned_to_nat(0);
                    v_msgs_2368_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
                    v_sz_2369_ = lean_array_size(v_structs_2366_);
                    v___x_2370_ = 0usize;
                    v___x_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_structs_2366_, v_sz_2369_, v___x_2370_, v_msgs_2368_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
                    leanh::lean_dec_ref(v_structs_2366_);
                    if leanh::lean_obj_tag(v___x_2371_) == 0 {
                        v_a_2372_ = leanh::lean_ctor_get(v___x_2371_, 0);
                        v_isSharedCheck_2396_ =
                            (!leanh::lean_is_exclusive(v___x_2371_)) as u8;
                        if v_isSharedCheck_2396_ == 0 {
                            v___x_2374_ = v___x_2371_;
                            v_isShared_2375_ = v_isSharedCheck_2396_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2372_);
                            leanh::lean_dec(v___x_2371_);
                            v___x_2374_ = leanh::lean_box(0);
                            v_isShared_2375_ = v_isSharedCheck_2396_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2397_ = leanh::lean_ctor_get(v___x_2371_, 0);
                        v_isSharedCheck_2404_ =
                            (!leanh::lean_is_exclusive(v___x_2371_)) as u8;
                        if v_isSharedCheck_2404_ == 0 {
                            v___x_2399_ = v___x_2371_;
                            v_isShared_2400_ = v_isSharedCheck_2404_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2397_);
                            leanh::lean_dec(v___x_2371_);
                            v___x_2399_ = leanh::lean_box(0);
                            v_isShared_2400_ = v_isSharedCheck_2404_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_2405_ = leanh::lean_ctor_get(v___x_2364_, 0);
                    v_isSharedCheck_2417_ = (!leanh::lean_is_exclusive(v___x_2364_)) as u8;
                    if v_isSharedCheck_2417_ == 0 {
                        v___x_2407_ = v___x_2364_;
                        v_isShared_2408_ = v_isSharedCheck_2417_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2405_);
                        leanh::lean_dec(v___x_2364_);
                        v___x_2407_ = leanh::lean_box(0);
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
                    v___x_2378_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2379_ = lean_nat_dec_eq(v___x_2376_, v___x_2378_);
                    if v___x_2379_ == 0 {
                        v___x_2380_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__0_once),
                            _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0,
                        );
                        v___x_2381_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__3_once),
                            _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3,
                        );
                        v___x_2382_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_2382_, 0, v___x_2380_);
                        leanh::lean_ctor_set(v___x_2382_, 1, v___x_2381_);
                        leanh::lean_ctor_set(v___x_2382_, 2, v_a_2372_);
                        v___x_2383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2383_, 0, v___x_2382_);
                        if v_isShared_2375_ == 0 {
                            leanh::lean_ctor_set(v___x_2374_, 0, v___x_2383_);
                            v___x_2385_ = v___x_2374_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2386_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
                            v___x_2385_ = v_reuseFailAlloc_2386_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2387_ = lean_array_fget(v_a_2372_, v___x_2367_);
                        leanh::lean_dec(v_a_2372_);
                        v___x_2388_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2388_, 0, v___x_2387_);
                        if v_isShared_2375_ == 0 {
                            leanh::lean_ctor_set(v___x_2374_, 0, v___x_2388_);
                            v___x_2390_ = v___x_2374_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2391_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
                            v___x_2390_ = v_reuseFailAlloc_2391_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2372_);
                    v___x_2392_ = leanh::lean_box(0);
                    if v_isShared_2375_ == 0 {
                        leanh::lean_ctor_set(v___x_2374_, 0, v___x_2392_);
                        v___x_2394_ = v___x_2374_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2395_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
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
                    v_reuseFailAlloc_2403_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
                    v___x_2402_ = v_reuseFailAlloc_2403_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2402_;
            }
            7 => {
                v_ref_2409_ = leanh::lean_ctor_get(v_a_2360_, 5);
                v___x_2410_ = lean_io_error_to_string(v_a_2405_);
                v___x_2411_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2411_, 0, v___x_2410_);
                v___x_2412_ = l_Lean_MessageData_ofFormat(v___x_2411_);
                leanh::lean_inc(v_ref_2409_);
                v___x_2413_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2413_, 0, v_ref_2409_);
                leanh::lean_ctor_set(v___x_2413_, 1, v___x_2412_);
                if v_isShared_2408_ == 0 {
                    leanh::lean_ctor_set(v___x_2407_, 0, v___x_2413_);
                    v___x_2415_ = v___x_2407_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2416_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
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
    mut v_goal_2418_: *mut leanh::LeanObject,
    mut v_a_2419_: *mut leanh::LeanObject,
    mut v_a_2420_: *mut leanh::LeanObject,
    mut v_a_2421_: *mut leanh::LeanObject,
    mut v_a_2422_: *mut leanh::LeanObject,
    mut v_a_2423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ =
        l_Lean_Meta_Grind_AC_pp_x3f(v_goal_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
    leanh::lean_dec(v_a_2422_);
    leanh::lean_dec_ref(v_a_2421_);
    leanh::lean_dec(v_a_2420_);
    leanh::lean_dec_ref(v_a_2419_);
    leanh::lean_dec_ref(v_goal_2418_);
    return v_res_2424_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM =
        _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_PP(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_PP(
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
    res = initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
}