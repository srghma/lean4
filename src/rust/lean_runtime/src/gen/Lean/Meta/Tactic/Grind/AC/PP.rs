// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.PP
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.AC.DenoteExpr Init.Omega
use crate::r#gen::Init::Control::State::l_StateT_get;
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_str___override,
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
use crate::lean_imports_rs::Init::Core::{lean_mk_thunk, lean_thunk_get_own};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5_value) as *mut LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0:
    f64 = 0.0;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1_value
) as *mut LeanObject;
pub static l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [66, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__0_value) as *mut LeanObject,13286986945483979944 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 97, 115, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__1_value) as *mut LeanObject,6004542540932731919 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [68, 105, 115, 101, 113, 117, 97, 108, 105, 116, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [78, 101, 0]};
static mut l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__0_value) as *mut LeanObject,6695605208187598753 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 105, 115, 101, 113, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__1_value) as *mut LeanObject,12150963035389937170 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [79, 112, 101, 114, 97, 116, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [80, 114, 111, 112, 101, 114, 116, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 115, 115, 111, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__0_value) as *mut LeanObject,12101614322480916425 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [112, 114, 111, 112, 101, 114, 116, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__3_value) as *mut LeanObject,4640836329272094479 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 100, 101, 110, 116, 105, 116, 121, 58, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 100, 101, 109, 112, 111, 116, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 109, 109, 117, 116, 97, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_AC_pp_x3f___closed__2_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_AC_pp_x3f___closed__1_value) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_pp_x3f___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_AC_pp_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0()
-> *mut LeanObject {
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    v___x_1213_ = l_instMonadEIO(lean_box(0));
    return v___x_1213_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1()
-> *mut LeanObject {
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    v___x_1214_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__0);
    v___x_1215_ = l_StateRefT_x27_instMonad___redArg(v___x_1214_);
    return v___x_1215_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM()
-> *mut LeanObject {
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v_toFunctor_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1247_: u8 = 0;
    let mut v___f_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1263_: u8 = 0;
    let mut v_unused_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut v_unused_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1220_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__1);
                v_toApplicative_1221_ = lean_ctor_get(v___x_1220_, 0);
                v_toFunctor_1222_ = lean_ctor_get(v_toApplicative_1221_, 0);
                v_toSeq_1223_ = lean_ctor_get(v_toApplicative_1221_, 2);
                v_toSeqLeft_1224_ = lean_ctor_get(v_toApplicative_1221_, 3);
                v_toSeqRight_1225_ = lean_ctor_get(v_toApplicative_1221_, 4);
                v___f_1226_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__2;
                v___f_1227_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__3;
                lean_inc_ref_n(v_toFunctor_1222_, 2);
                v___f_1228_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1228_, 0, v_toFunctor_1222_);
                v___f_1229_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1229_, 0, v_toFunctor_1222_);
                v___x_1230_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1230_, 0, v___f_1228_);
                lean_ctor_set(v___x_1230_, 1, v___f_1229_);
                lean_inc(v_toSeqRight_1225_);
                v___f_1231_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1231_, 0, v_toSeqRight_1225_);
                lean_inc(v_toSeqLeft_1224_);
                v___f_1232_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1232_, 0, v_toSeqLeft_1224_);
                lean_inc(v_toSeq_1223_);
                v___f_1233_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1233_, 0, v_toSeq_1223_);
                v___x_1234_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1234_, 0, v___x_1230_);
                lean_ctor_set(v___x_1234_, 1, v___f_1226_);
                lean_ctor_set(v___x_1234_, 2, v___f_1233_);
                lean_ctor_set(v___x_1234_, 3, v___f_1232_);
                lean_ctor_set(v___x_1234_, 4, v___f_1231_);
                v___x_1235_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1235_, 0, v___x_1234_);
                lean_ctor_set(v___x_1235_, 1, v___f_1227_);
                v___x_1236_ = l_StateRefT_x27_instMonad___redArg(v___x_1235_);
                v_toApplicative_1237_ = lean_ctor_get(v___x_1236_, 0);
                v_isSharedCheck_1265_ = (!lean_is_exclusive(v___x_1236_)) as u8;
                if v_isSharedCheck_1265_ == 0 {
                    v_unused_1266_ = lean_ctor_get(v___x_1236_, 1);
                    lean_dec(v_unused_1266_);
                    v___x_1239_ = v___x_1236_;
                    v_isShared_1240_ = v_isSharedCheck_1265_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_1237_);
                    lean_dec(v___x_1236_);
                    v___x_1239_ = lean_box(0);
                    v_isShared_1240_ = v_isSharedCheck_1265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_1241_ = lean_ctor_get(v_toApplicative_1237_, 0);
                v_toSeq_1242_ = lean_ctor_get(v_toApplicative_1237_, 2);
                v_toSeqLeft_1243_ = lean_ctor_get(v_toApplicative_1237_, 3);
                v_toSeqRight_1244_ = lean_ctor_get(v_toApplicative_1237_, 4);
                v_isSharedCheck_1263_ = (!lean_is_exclusive(v_toApplicative_1237_)) as u8;
                if v_isSharedCheck_1263_ == 0 {
                    v_unused_1264_ = lean_ctor_get(v_toApplicative_1237_, 1);
                    lean_dec(v_unused_1264_);
                    v___x_1246_ = v_toApplicative_1237_;
                    v_isShared_1247_ = v_isSharedCheck_1263_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_1244_);
                    lean_inc(v_toSeqLeft_1243_);
                    lean_inc(v_toSeq_1242_);
                    lean_inc(v_toFunctor_1241_);
                    lean_dec(v_toApplicative_1237_);
                    v___x_1246_ = lean_box(0);
                    v_isShared_1247_ = v_isSharedCheck_1263_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_1248_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__4;
                v___f_1249_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM___closed__5;
                lean_inc_ref(v_toFunctor_1241_);
                v___f_1250_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1250_, 0, v_toFunctor_1241_);
                v___f_1251_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1251_, 0, v_toFunctor_1241_);
                v___x_1252_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1252_, 0, v___f_1250_);
                lean_ctor_set(v___x_1252_, 1, v___f_1251_);
                v___f_1253_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1253_, 0, v_toSeqRight_1244_);
                v___f_1254_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1254_, 0, v_toSeqLeft_1243_);
                v___f_1255_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_1255_, 0, v_toSeq_1242_);
                if v_isShared_1247_ == 0 {
                    lean_ctor_set(v___x_1246_, 4, v___f_1253_);
                    lean_ctor_set(v___x_1246_, 3, v___f_1254_);
                    lean_ctor_set(v___x_1246_, 2, v___f_1255_);
                    lean_ctor_set(v___x_1246_, 1, v___f_1248_);
                    lean_ctor_set(v___x_1246_, 0, v___x_1252_);
                    v___x_1257_ = v___x_1246_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1252_);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___f_1248_);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 2, v___f_1255_);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 3, v___f_1254_);
                    lean_ctor_set(v_reuseFailAlloc_1262_, 4, v___f_1253_);
                    v___x_1257_ = v_reuseFailAlloc_1262_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1240_ == 0 {
                    lean_ctor_set(v___x_1239_, 1, v___f_1249_);
                    lean_ctor_set(v___x_1239_, 0, v___x_1257_);
                    v___x_1259_ = v___x_1239_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1257_);
                    lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___f_1249_);
                    v___x_1259_ = v_reuseFailAlloc_1261_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1260_ = lean_alloc_closure(l_StateT_get as *mut core::ffi::c_void, 4, 3);
                lean_closure_set(v___x_1260_, 0, lean_box(0));
                lean_closure_set(v___x_1260_, 1, lean_box(0));
                lean_closure_set(v___x_1260_, 2, v___x_1259_);
                return v___x_1260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0()
-> f64 {
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: f64 = 0.0;
    v___x_1267_ = lean_unsigned_to_nat(0);
    v___x_1268_ = lean_float_of_nat(v___x_1267_);
    return v___x_1268_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
    mut v_cls_1270_: *mut LeanObject,
    mut v_header_1271_: *mut LeanObject,
    mut v_msgs_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: u8 = 0;
    v___x_1273_ = lean_array_get_size(v_msgs_1272_);
    v___x_1274_ = lean_unsigned_to_nat(0);
    v___x_1275_ = lean_nat_dec_eq(v___x_1273_, v___x_1274_);
    if v___x_1275_ == 0 {
        let mut v___x_1276_: u8 = 0;
        let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1278_: f64 = 0.0;
        let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
        v___x_1276_ = 1;
        v___x_1277_ = lean_box(0);
        v___x_1278_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
        v___x_1279_ =
            l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
        v___x_1280_ = lean_alloc_ctor(0, 3, (17) as u32);
        lean_ctor_set(v___x_1280_, 0, v_cls_1270_);
        lean_ctor_set(v___x_1280_, 1, v___x_1277_);
        lean_ctor_set(v___x_1280_, 2, v___x_1279_);
        lean_ctor_set_float(
            v___x_1280_,
            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            v___x_1278_,
        );
        lean_ctor_set_float(
            v___x_1280_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
            v___x_1278_,
        );
        lean_ctor_set_uint8(
            v___x_1280_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
            v___x_1276_,
        );
        v___x_1281_ = lean_thunk_get_own(v_header_1271_);
        v___x_1282_ = lean_alloc_ctor(9, 3, (0) as u32);
        lean_ctor_set(v___x_1282_, 0, v___x_1280_);
        lean_ctor_set(v___x_1282_, 1, v___x_1281_);
        lean_ctor_set(v___x_1282_, 2, v_msgs_1272_);
        v___x_1283_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1283_, 0, v___x_1282_);
        return v___x_1283_;
    } else {
        let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_msgs_1272_);
        lean_dec(v_cls_1270_);
        v___x_1284_ = lean_box(0);
        return v___x_1284_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___boxed(
    mut v_cls_1285_: *mut LeanObject,
    mut v_header_1286_: *mut LeanObject,
    mut v_msgs_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1288_: *mut LeanObject = core::ptr::null_mut();
    v_res_1288_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
        v_cls_1285_,
        v_header_1286_,
        v_msgs_1287_,
    );
    lean_dec_ref(v_header_1286_);
    return v_res_1288_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_push(
    mut v_msgs_1289_: *mut LeanObject,
    mut v_msg_x3f_1290_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_msg_x3f_1290_) == 1 {
        let mut v_val_1291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
        v_val_1291_ = lean_ctor_get(v_msg_x3f_1290_, 0);
        lean_inc(v_val_1291_);
        lean_dec_ref_known(v_msg_x3f_1290_, 1);
        v___x_1292_ = lean_array_push(v_msgs_1289_, v_val_1291_);
        return v___x_1292_;
    } else {
        lean_dec(v_msg_x3f_1290_);
        return v_msgs_1289_;
    }
}
pub unsafe fn l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(
    mut v_e_1295_: *mut LeanObject,
    mut v_cls_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: f64 = 0.0;
    let mut v___x_1299_: u8 = 0;
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    v___x_1297_ = lean_box(0);
    v___x_1298_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_1299_ = 1;
    v___x_1300_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_1301_ = lean_alloc_ctor(0, 3, (17) as u32);
    lean_ctor_set(v___x_1301_, 0, v_cls_1296_);
    lean_ctor_set(v___x_1301_, 1, v___x_1297_);
    lean_ctor_set(v___x_1301_, 2, v___x_1300_);
    lean_ctor_set_float(
        v___x_1301_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_1298_,
    );
    lean_ctor_set_float(
        v___x_1301_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        v___x_1298_,
    );
    lean_ctor_set_uint8(
        v___x_1301_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
        v___x_1299_,
    );
    v___x_1302_ = l_Lean_MessageData_ofExpr(v_e_1295_);
    v___x_1303_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_1304_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_1304_, 0, v___x_1301_);
    lean_ctor_set(v___x_1304_, 1, v___x_1302_);
    lean_ctor_set(v___x_1304_, 2, v___x_1303_);
    return v___x_1304_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    v___x_1308_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__1;
    v___x_1309_ = l_Lean_MessageData_ofFormat(v___x_1308_);
    return v___x_1309_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0(
    mut v_x_1310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    v___x_1311_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___lam__0___closed__2);
    return v___x_1311_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(
    mut v_s_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1320_: u8 = 0;
    let mut v_size_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut v_x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v_fst_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v_op_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1315_ = l_Lean_instInhabitedExpr;
                if lean_obj_tag(v_s_1312_) == 0 {
                    v_vars_1316_ = lean_ctor_get(v___y_1313_, 10);
                    v_x_1317_ = lean_ctor_get(v_s_1312_, 0);
                    v_isSharedCheck_1333_ = (!lean_is_exclusive(v_s_1312_)) as u8;
                    if v_isSharedCheck_1333_ == 0 {
                        v___x_1319_ = v_s_1312_;
                        v_isShared_1320_ = v_isSharedCheck_1333_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_x_1317_);
                        lean_dec(v_s_1312_);
                        v___x_1319_ = lean_box(0);
                        v_isShared_1320_ = v_isSharedCheck_1333_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_x_1334_ = lean_ctor_get(v_s_1312_, 0);
                    lean_inc(v_x_1334_);
                    v_s_1335_ = lean_ctor_get(v_s_1312_, 1);
                    lean_inc_ref(v_s_1335_);
                    lean_dec_ref_known(v_s_1312_, 2);
                    lean_inc_ref(v___y_1313_);
                    v___x_1336_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_1335_, v___y_1313_);
                    v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
                    v_isSharedCheck_1362_ = (!lean_is_exclusive(v___x_1336_)) as u8;
                    if v_isSharedCheck_1362_ == 0 {
                        v___x_1339_ = v___x_1336_;
                        v_isShared_1340_ = v_isSharedCheck_1362_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1337_);
                        lean_dec(v___x_1336_);
                        v___x_1339_ = lean_box(0);
                        v_isShared_1340_ = v_isSharedCheck_1362_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_size_1321_ = lean_ctor_get(v_vars_1316_, 2);
                v___x_1322_ = lean_nat_dec_lt(v_x_1317_, v_size_1321_);
                if v___x_1322_ == 0 {
                    lean_dec(v_x_1317_);
                    v___x_1323_ = l_outOfBounds___redArg(v___x_1315_);
                    v___x_1324_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1324_, 0, v___x_1323_);
                    lean_ctor_set(v___x_1324_, 1, v___y_1313_);
                    if v_isShared_1320_ == 0 {
                        lean_ctor_set(v___x_1319_, 0, v___x_1324_);
                        v___x_1326_ = v___x_1319_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
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
                    lean_dec(v_x_1317_);
                    v___x_1329_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1329_, 0, v___x_1328_);
                    lean_ctor_set(v___x_1329_, 1, v___y_1313_);
                    if v_isShared_1320_ == 0 {
                        lean_ctor_set(v___x_1319_, 0, v___x_1329_);
                        v___x_1331_ = v___x_1319_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
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
                v_fst_1341_ = lean_ctor_get(v_a_1337_, 0);
                v_snd_1342_ = lean_ctor_get(v_a_1337_, 1);
                v_isSharedCheck_1361_ = (!lean_is_exclusive(v_a_1337_)) as u8;
                if v_isSharedCheck_1361_ == 0 {
                    v___x_1344_ = v_a_1337_;
                    v_isShared_1345_ = v_isSharedCheck_1361_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_1342_);
                    lean_inc(v_fst_1341_);
                    lean_dec(v_a_1337_);
                    v___x_1344_ = lean_box(0);
                    v_isShared_1345_ = v_isSharedCheck_1361_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_op_1346_ = lean_ctor_get(v___y_1313_, 3);
                lean_inc_ref(v_op_1346_);
                v_vars_1347_ = lean_ctor_get(v___y_1313_, 10);
                lean_inc_ref(v_vars_1347_);
                lean_dec_ref(v___y_1313_);
                v_size_1357_ = lean_ctor_get(v_vars_1347_, 2);
                v___x_1358_ = lean_nat_dec_lt(v_x_1334_, v_size_1357_);
                if v___x_1358_ == 0 {
                    lean_dec_ref(v_vars_1347_);
                    lean_dec(v_x_1334_);
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
                    lean_dec(v_x_1334_);
                    lean_dec_ref(v_vars_1347_);
                    v___y_1349_ = v___x_1360_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1350_ = l_Lean_mkAppB(v_op_1346_, v___y_1349_, v_fst_1341_);
                if v_isShared_1345_ == 0 {
                    lean_ctor_set(v___x_1344_, 0, v___x_1350_);
                    v___x_1352_ = v___x_1344_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1350_);
                    lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_snd_1342_);
                    v___x_1352_ = v_reuseFailAlloc_1356_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_1340_ == 0 {
                    lean_ctor_set(v___x_1339_, 0, v___x_1352_);
                    v___x_1354_ = v___x_1339_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
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
    mut v_s_1363_: *mut LeanObject,
    mut v___y_1364_: *mut LeanObject,
    mut v___y_1365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1366_: *mut LeanObject = core::ptr::null_mut();
    v_res_1366_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_1363_, v___y_1364_);
    return v_res_1366_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(
    mut v_c_1370_: *mut LeanObject,
    mut v___y_1371_: *mut LeanObject,
    mut v___y_1372_: *mut LeanObject,
    mut v___y_1373_: *mut LeanObject,
    mut v___y_1374_: *mut LeanObject,
    mut v___y_1375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1385_: u8 = 0;
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v_fst_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1395_: u8 = 0;
    let mut v_type_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v_isSharedCheck_1413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1377_ = lean_ctor_get(v_c_1370_, 0);
                lean_inc_ref(v_lhs_1377_);
                v_rhs_1378_ = lean_ctor_get(v_c_1370_, 1);
                lean_inc_ref(v_rhs_1378_);
                lean_dec_ref(v_c_1370_);
                lean_inc_ref(v___y_1371_);
                v___x_1379_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_1377_, v___y_1371_);
                v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
                lean_inc(v_a_1380_);
                lean_dec_ref(v___x_1379_);
                v_fst_1381_ = lean_ctor_get(v_a_1380_, 0);
                v_snd_1382_ = lean_ctor_get(v_a_1380_, 1);
                v_isSharedCheck_1413_ = (!lean_is_exclusive(v_a_1380_)) as u8;
                if v_isSharedCheck_1413_ == 0 {
                    v___x_1384_ = v_a_1380_;
                    v_isShared_1385_ = v_isSharedCheck_1413_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1382_);
                    lean_inc(v_fst_1381_);
                    lean_dec(v_a_1380_);
                    v___x_1384_ = lean_box(0);
                    v_isShared_1385_ = v_isSharedCheck_1413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1386_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_1378_, v_snd_1382_);
                v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
                v_isSharedCheck_1412_ = (!lean_is_exclusive(v___x_1386_)) as u8;
                if v_isSharedCheck_1412_ == 0 {
                    v___x_1389_ = v___x_1386_;
                    v_isShared_1390_ = v_isSharedCheck_1412_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_1387_);
                    lean_dec(v___x_1386_);
                    v___x_1389_ = lean_box(0);
                    v_isShared_1390_ = v_isSharedCheck_1412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_1391_ = lean_ctor_get(v_a_1387_, 0);
                v_snd_1392_ = lean_ctor_get(v_a_1387_, 1);
                v_isSharedCheck_1411_ = (!lean_is_exclusive(v_a_1387_)) as u8;
                if v_isSharedCheck_1411_ == 0 {
                    v___x_1394_ = v_a_1387_;
                    v_isShared_1395_ = v_isSharedCheck_1411_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_1392_);
                    lean_inc(v_fst_1391_);
                    lean_dec(v_a_1387_);
                    v___x_1394_ = lean_box(0);
                    v_isShared_1395_ = v_isSharedCheck_1411_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_type_1396_ = lean_ctor_get(v___y_1371_, 1);
                lean_inc_ref(v_type_1396_);
                v_u_1397_ = lean_ctor_get(v___y_1371_, 2);
                lean_inc(v_u_1397_);
                lean_dec_ref(v___y_1371_);
                v___x_1398_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0___closed__1;
                v___x_1399_ = lean_box(0);
                if v_isShared_1385_ == 0 {
                    lean_ctor_set_tag(v___x_1384_, 1);
                    lean_ctor_set(v___x_1384_, 1, v___x_1399_);
                    lean_ctor_set(v___x_1384_, 0, v_u_1397_);
                    v___x_1401_ = v___x_1384_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_u_1397_);
                    lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___x_1399_);
                    v___x_1401_ = v_reuseFailAlloc_1410_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1402_ = l_Lean_mkConst(v___x_1398_, v___x_1401_);
                v___x_1403_ = l_Lean_mkApp3(v___x_1402_, v_type_1396_, v_fst_1381_, v_fst_1391_);
                if v_isShared_1395_ == 0 {
                    lean_ctor_set(v___x_1394_, 0, v___x_1403_);
                    v___x_1405_ = v___x_1394_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1403_);
                    lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_snd_1392_);
                    v___x_1405_ = v_reuseFailAlloc_1409_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1390_ == 0 {
                    lean_ctor_set(v___x_1389_, 0, v___x_1405_);
                    v___x_1407_ = v___x_1389_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
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
    mut v_c_1414_: *mut LeanObject,
    mut v___y_1415_: *mut LeanObject,
    mut v___y_1416_: *mut LeanObject,
    mut v___y_1417_: *mut LeanObject,
    mut v___y_1418_: *mut LeanObject,
    mut v___y_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1421_: *mut LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_c_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
    lean_dec(v___y_1419_);
    lean_dec_ref(v___y_1418_);
    lean_dec(v___y_1417_);
    lean_dec_ref(v___y_1416_);
    return v_res_1421_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(
    mut v_as_x27_1426_: *mut LeanObject,
    mut v_b_1427_: *mut LeanObject,
    mut v___y_1428_: *mut LeanObject,
    mut v___y_1429_: *mut LeanObject,
    mut v___y_1430_: *mut LeanObject,
    mut v___y_1431_: *mut LeanObject,
    mut v___y_1432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_1426_) == 0 {
                    v___x_1434_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1434_, 0, v_b_1427_);
                    lean_ctor_set(v___x_1434_, 1, v___y_1428_);
                    v___x_1435_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1435_, 0, v___x_1434_);
                    return v___x_1435_;
                } else {
                    v_head_1436_ = lean_ctor_get(v_as_x27_1426_, 0);
                    v_tail_1437_ = lean_ctor_get(v_as_x27_1426_, 1);
                    lean_inc(v_head_1436_);
                    v___x_1438_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0(v_head_1436_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
                    v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
                    lean_inc(v_a_1439_);
                    lean_dec_ref(v___x_1438_);
                    v_fst_1440_ = lean_ctor_get(v_a_1439_, 0);
                    lean_inc(v_fst_1440_);
                    v_snd_1441_ = lean_ctor_get(v_a_1439_, 1);
                    lean_inc(v_snd_1441_);
                    lean_dec(v_a_1439_);
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
    mut v_as_x27_1446_: *mut LeanObject,
    mut v_b_1447_: *mut LeanObject,
    mut v___y_1448_: *mut LeanObject,
    mut v___y_1449_: *mut LeanObject,
    mut v___y_1450_: *mut LeanObject,
    mut v___y_1451_: *mut LeanObject,
    mut v___y_1452_: *mut LeanObject,
    mut v___y_1453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1454_: *mut LeanObject = core::ptr::null_mut();
    v_res_1454_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_1446_, v_b_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
    lean_dec(v___y_1452_);
    lean_dec_ref(v___y_1451_);
    lean_dec(v___y_1450_);
    lean_dec_ref(v___y_1449_);
    lean_dec(v_as_x27_1446_);
    return v_res_1454_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3()
-> *mut LeanObject {
    let mut v___f_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    v___f_1459_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__0;
    v___x_1460_ = lean_mk_thunk(v___f_1459_);
    return v___x_1460_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(
    mut v_a_1461_: *mut LeanObject,
    mut v_a_1462_: *mut LeanObject,
    mut v_a_1463_: *mut LeanObject,
    mut v_a_1464_: *mut LeanObject,
    mut v_a_1465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_basis_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v_fst_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_a_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_basis_1467_ = lean_ctor_get(v_a_1461_, 15);
                lean_inc(v_basis_1467_);
                v_basis_1468_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
                v___x_1469_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_basis_1467_, v_basis_1468_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
                lean_dec(v_basis_1467_);
                if lean_obj_tag(v___x_1469_) == 0 {
                    v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
                    v_isSharedCheck_1489_ = (!lean_is_exclusive(v___x_1469_)) as u8;
                    if v_isSharedCheck_1489_ == 0 {
                        v___x_1472_ = v___x_1469_;
                        v_isShared_1473_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1470_);
                        lean_dec(v___x_1469_);
                        v___x_1472_ = lean_box(0);
                        v_isShared_1473_ = v_isSharedCheck_1489_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1490_ = lean_ctor_get(v___x_1469_, 0);
                    v_isSharedCheck_1497_ = (!lean_is_exclusive(v___x_1469_)) as u8;
                    if v_isSharedCheck_1497_ == 0 {
                        v___x_1492_ = v___x_1469_;
                        v_isShared_1493_ = v_isSharedCheck_1497_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1490_);
                        lean_dec(v___x_1469_);
                        v___x_1492_ = lean_box(0);
                        v_isShared_1493_ = v_isSharedCheck_1497_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1474_ = lean_ctor_get(v_a_1470_, 0);
                v_snd_1475_ = lean_ctor_get(v_a_1470_, 1);
                v_isSharedCheck_1488_ = (!lean_is_exclusive(v_a_1470_)) as u8;
                if v_isSharedCheck_1488_ == 0 {
                    v___x_1477_ = v_a_1470_;
                    v_isShared_1478_ = v_isSharedCheck_1488_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1475_);
                    lean_inc(v_fst_1474_);
                    lean_dec(v_a_1470_);
                    v___x_1477_ = lean_box(0);
                    v_isShared_1478_ = v_isSharedCheck_1488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1479_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__2;
                v___x_1480_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f___closed__3);
                v___x_1481_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
                        v___x_1479_,
                        v___x_1480_,
                        v_fst_1474_,
                    );
                if v_isShared_1478_ == 0 {
                    lean_ctor_set(v___x_1477_, 0, v___x_1481_);
                    v___x_1483_ = v___x_1477_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1481_);
                    lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_snd_1475_);
                    v___x_1483_ = v_reuseFailAlloc_1487_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1473_ == 0 {
                    lean_ctor_set(v___x_1472_, 0, v___x_1483_);
                    v___x_1485_ = v___x_1472_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
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
                    v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
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
    mut v_a_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
    mut v_a_1501_: *mut LeanObject,
    mut v_a_1502_: *mut LeanObject,
    mut v_a_1503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1504_: *mut LeanObject = core::ptr::null_mut();
    v_res_1504_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f(
        v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_,
    );
    lean_dec(v_a_1502_);
    lean_dec_ref(v_a_1501_);
    lean_dec(v_a_1500_);
    lean_dec_ref(v_a_1499_);
    return v_res_1504_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(
    mut v_as_1505_: *mut LeanObject,
    mut v_as_x27_1506_: *mut LeanObject,
    mut v_b_1507_: *mut LeanObject,
    mut v_a_1508_: *mut LeanObject,
    mut v___y_1509_: *mut LeanObject,
    mut v___y_1510_: *mut LeanObject,
    mut v___y_1511_: *mut LeanObject,
    mut v___y_1512_: *mut LeanObject,
    mut v___y_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    v___x_1515_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg(v_as_x27_1506_, v_b_1507_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
    return v___x_1515_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___boxed(
    mut v_as_1516_: *mut LeanObject,
    mut v_as_x27_1517_: *mut LeanObject,
    mut v_b_1518_: *mut LeanObject,
    mut v_a_1519_: *mut LeanObject,
    mut v___y_1520_: *mut LeanObject,
    mut v___y_1521_: *mut LeanObject,
    mut v___y_1522_: *mut LeanObject,
    mut v___y_1523_: *mut LeanObject,
    mut v___y_1524_: *mut LeanObject,
    mut v___y_1525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1526_: *mut LeanObject = core::ptr::null_mut();
    v_res_1526_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2(v_as_1516_, v_as_x27_1517_, v_b_1518_, v_a_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
    lean_dec(v___y_1524_);
    lean_dec_ref(v___y_1523_);
    lean_dec(v___y_1522_);
    lean_dec_ref(v___y_1521_);
    lean_dec(v_as_x27_1517_);
    lean_dec(v_as_1516_);
    return v_res_1526_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(
    mut v_s_1527_: *mut LeanObject,
    mut v___y_1528_: *mut LeanObject,
    mut v___y_1529_: *mut LeanObject,
    mut v___y_1530_: *mut LeanObject,
    mut v___y_1531_: *mut LeanObject,
    mut v___y_1532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    v___x_1534_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_s_1527_, v___y_1528_);
    return v___x_1534_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___boxed(
    mut v_s_1535_: *mut LeanObject,
    mut v___y_1536_: *mut LeanObject,
    mut v___y_1537_: *mut LeanObject,
    mut v___y_1538_: *mut LeanObject,
    mut v___y_1539_: *mut LeanObject,
    mut v___y_1540_: *mut LeanObject,
    mut v___y_1541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1542_: *mut LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0(v_s_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
    lean_dec(v___y_1540_);
    lean_dec_ref(v___y_1539_);
    lean_dec(v___y_1538_);
    lean_dec_ref(v___y_1537_);
    return v_res_1542_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    v___x_1546_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__1;
    v___x_1547_ = l_Lean_MessageData_ofFormat(v___x_1546_);
    return v___x_1547_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0(
    mut v_x_1548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    v___x_1549_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___lam__0___closed__2);
    return v___x_1549_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(
    mut v_c_1553_: *mut LeanObject,
    mut v___y_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1564_: u8 = 0;
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1569_: u8 = 0;
    let mut v_fst_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1574_: u8 = 0;
    let mut v_type_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_isSharedCheck_1591_: u8 = 0;
    let mut v_isSharedCheck_1592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_1556_ = lean_ctor_get(v_c_1553_, 0);
                lean_inc_ref(v_lhs_1556_);
                v_rhs_1557_ = lean_ctor_get(v_c_1553_, 1);
                lean_inc_ref(v_rhs_1557_);
                lean_dec_ref(v_c_1553_);
                lean_inc_ref(v___y_1554_);
                v___x_1558_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_lhs_1556_, v___y_1554_);
                v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
                lean_inc(v_a_1559_);
                lean_dec_ref(v___x_1558_);
                v_fst_1560_ = lean_ctor_get(v_a_1559_, 0);
                v_snd_1561_ = lean_ctor_get(v_a_1559_, 1);
                v_isSharedCheck_1592_ = (!lean_is_exclusive(v_a_1559_)) as u8;
                if v_isSharedCheck_1592_ == 0 {
                    v___x_1563_ = v_a_1559_;
                    v_isShared_1564_ = v_isSharedCheck_1592_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1561_);
                    lean_inc(v_fst_1560_);
                    lean_dec(v_a_1559_);
                    v___x_1563_ = lean_box(0);
                    v_isShared_1564_ = v_isSharedCheck_1592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1565_ = l_Lean_Grind_AC_Seq_denoteExpr___at___00Lean_Meta_Grind_AC_EqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__0_spec__0___redArg(v_rhs_1557_, v_snd_1561_);
                v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
                v_isSharedCheck_1591_ = (!lean_is_exclusive(v___x_1565_)) as u8;
                if v_isSharedCheck_1591_ == 0 {
                    v___x_1568_ = v___x_1565_;
                    v_isShared_1569_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_1566_);
                    lean_dec(v___x_1565_);
                    v___x_1568_ = lean_box(0);
                    v_isShared_1569_ = v_isSharedCheck_1591_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_1570_ = lean_ctor_get(v_a_1566_, 0);
                v_snd_1571_ = lean_ctor_get(v_a_1566_, 1);
                v_isSharedCheck_1590_ = (!lean_is_exclusive(v_a_1566_)) as u8;
                if v_isSharedCheck_1590_ == 0 {
                    v___x_1573_ = v_a_1566_;
                    v_isShared_1574_ = v_isSharedCheck_1590_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_1571_);
                    lean_inc(v_fst_1570_);
                    lean_dec(v_a_1566_);
                    v___x_1573_ = lean_box(0);
                    v_isShared_1574_ = v_isSharedCheck_1590_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_type_1575_ = lean_ctor_get(v___y_1554_, 1);
                lean_inc_ref(v_type_1575_);
                v_u_1576_ = lean_ctor_get(v___y_1554_, 2);
                lean_inc(v_u_1576_);
                lean_dec_ref(v___y_1554_);
                v___x_1577_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg___closed__1;
                v___x_1578_ = lean_box(0);
                if v_isShared_1564_ == 0 {
                    lean_ctor_set_tag(v___x_1563_, 1);
                    lean_ctor_set(v___x_1563_, 1, v___x_1578_);
                    lean_ctor_set(v___x_1563_, 0, v_u_1576_);
                    v___x_1580_ = v___x_1563_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_u_1576_);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1578_);
                    v___x_1580_ = v_reuseFailAlloc_1589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1581_ = l_Lean_mkConst(v___x_1577_, v___x_1580_);
                v___x_1582_ = l_Lean_mkApp3(v___x_1581_, v_type_1575_, v_fst_1560_, v_fst_1570_);
                if v_isShared_1574_ == 0 {
                    lean_ctor_set(v___x_1573_, 0, v___x_1582_);
                    v___x_1584_ = v___x_1573_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1582_);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_snd_1571_);
                    v___x_1584_ = v_reuseFailAlloc_1588_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1569_ == 0 {
                    lean_ctor_set(v___x_1568_, 0, v___x_1584_);
                    v___x_1586_ = v___x_1568_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
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
    mut v_c_1593_: *mut LeanObject,
    mut v___y_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1596_: *mut LeanObject = core::ptr::null_mut();
    v_res_1596_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_1593_, v___y_1594_);
    return v_res_1596_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(
    mut v_as_1597_: *mut LeanObject,
    mut v_sz_1598_: usize,
    mut v_i_1599_: usize,
    mut v_b_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1618_: u8 = 0;
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: usize = 0;
    let mut v___x_1626_: usize = 0;
    let mut v_reuseFailAlloc_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut v_a_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1633_: u8 = 0;
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1607_ = lean_usize_dec_lt(v_i_1599_, v_sz_1598_);
                if v___x_1607_ == 0 {
                    v___x_1608_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1608_, 0, v_b_1600_);
                    lean_ctor_set(v___x_1608_, 1, v___y_1601_);
                    v___x_1609_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1609_, 0, v___x_1608_);
                    return v___x_1609_;
                } else {
                    v_snd_1610_ = lean_ctor_get(v_b_1600_, 1);
                    lean_inc(v_snd_1610_);
                    lean_dec_ref(v_b_1600_);
                    v_a_1611_ = lean_array_uget_borrowed(v_as_1597_, v_i_1599_);
                    lean_inc(v_a_1611_);
                    v___x_1612_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1611_, v___y_1601_);
                    if lean_obj_tag(v___x_1612_) == 0 {
                        v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
                        lean_inc(v_a_1613_);
                        lean_dec_ref_known(v___x_1612_, 1);
                        v_fst_1614_ = lean_ctor_get(v_a_1613_, 0);
                        v_snd_1615_ = lean_ctor_get(v_a_1613_, 1);
                        v_isSharedCheck_1629_ = (!lean_is_exclusive(v_a_1613_)) as u8;
                        if v_isSharedCheck_1629_ == 0 {
                            v___x_1617_ = v_a_1613_;
                            v_isShared_1618_ = v_isSharedCheck_1629_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_1615_);
                            lean_inc(v_fst_1614_);
                            lean_dec(v_a_1613_);
                            v___x_1617_ = lean_box(0);
                            v_isShared_1618_ = v_isSharedCheck_1629_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_1610_);
                        v_a_1630_ = lean_ctor_get(v___x_1612_, 0);
                        v_isSharedCheck_1637_ = (!lean_is_exclusive(v___x_1612_)) as u8;
                        if v_isSharedCheck_1637_ == 0 {
                            v___x_1632_ = v___x_1612_;
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1630_);
                            lean_dec(v___x_1612_);
                            v___x_1632_ = lean_box(0);
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1619_ = lean_box(0);
                v___x_1620_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1621_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1614_, v___x_1620_);
                v___x_1622_ = lean_array_push(v_snd_1610_, v___x_1621_);
                if v_isShared_1618_ == 0 {
                    lean_ctor_set(v___x_1617_, 1, v___x_1622_);
                    lean_ctor_set(v___x_1617_, 0, v___x_1619_);
                    v___x_1624_ = v___x_1617_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1619_);
                    lean_ctor_set(v_reuseFailAlloc_1628_, 1, v___x_1622_);
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
                    v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
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
    mut v_as_1638_: *mut LeanObject,
    mut v_sz_1639_: *mut LeanObject,
    mut v_i_1640_: *mut LeanObject,
    mut v_b_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
    mut v___y_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
    mut v___y_1645_: *mut LeanObject,
    mut v___y_1646_: *mut LeanObject,
    mut v___y_1647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1648_: usize = 0;
    let mut v_i_boxed_1649_: usize = 0;
    let mut v_res_1650_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1648_ = lean_unbox_usize(v_sz_1639_);
    lean_dec(v_sz_1639_);
    v_i_boxed_1649_ = lean_unbox_usize(v_i_1640_);
    lean_dec(v_i_1640_);
    v_res_1650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2_spec__5(v_as_1638_, v_sz_boxed_1648_, v_i_boxed_1649_, v_b_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
    lean_dec(v___y_1646_);
    lean_dec_ref(v___y_1645_);
    lean_dec(v___y_1644_);
    lean_dec_ref(v___y_1643_);
    lean_dec_ref(v_as_1638_);
    return v_res_1650_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(
    mut v_as_1651_: *mut LeanObject,
    mut v_sz_1652_: usize,
    mut v_i_1653_: usize,
    mut v_b_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
    mut v___y_1659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: usize = 0;
    let mut v___x_1680_: usize = 0;
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut v_a_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1687_: u8 = 0;
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1661_ = lean_usize_dec_lt(v_i_1653_, v_sz_1652_);
                if v___x_1661_ == 0 {
                    v___x_1662_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1662_, 0, v_b_1654_);
                    lean_ctor_set(v___x_1662_, 1, v___y_1655_);
                    v___x_1663_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1663_, 0, v___x_1662_);
                    return v___x_1663_;
                } else {
                    v_snd_1664_ = lean_ctor_get(v_b_1654_, 1);
                    lean_inc(v_snd_1664_);
                    lean_dec_ref(v_b_1654_);
                    v_a_1665_ = lean_array_uget_borrowed(v_as_1651_, v_i_1653_);
                    lean_inc(v_a_1665_);
                    v___x_1666_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1665_, v___y_1655_);
                    if lean_obj_tag(v___x_1666_) == 0 {
                        v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
                        lean_inc(v_a_1667_);
                        lean_dec_ref_known(v___x_1666_, 1);
                        v_fst_1668_ = lean_ctor_get(v_a_1667_, 0);
                        v_snd_1669_ = lean_ctor_get(v_a_1667_, 1);
                        v_isSharedCheck_1683_ = (!lean_is_exclusive(v_a_1667_)) as u8;
                        if v_isSharedCheck_1683_ == 0 {
                            v___x_1671_ = v_a_1667_;
                            v_isShared_1672_ = v_isSharedCheck_1683_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_1669_);
                            lean_inc(v_fst_1668_);
                            lean_dec(v_a_1667_);
                            v___x_1671_ = lean_box(0);
                            v_isShared_1672_ = v_isSharedCheck_1683_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_1664_);
                        v_a_1684_ = lean_ctor_get(v___x_1666_, 0);
                        v_isSharedCheck_1691_ = (!lean_is_exclusive(v___x_1666_)) as u8;
                        if v_isSharedCheck_1691_ == 0 {
                            v___x_1686_ = v___x_1666_;
                            v_isShared_1687_ = v_isSharedCheck_1691_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1684_);
                            lean_dec(v___x_1666_);
                            v___x_1686_ = lean_box(0);
                            v_isShared_1687_ = v_isSharedCheck_1691_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1673_ = lean_box(0);
                v___x_1674_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1675_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1668_, v___x_1674_);
                v___x_1676_ = lean_array_push(v_snd_1664_, v___x_1675_);
                if v_isShared_1672_ == 0 {
                    lean_ctor_set(v___x_1671_, 1, v___x_1676_);
                    lean_ctor_set(v___x_1671_, 0, v___x_1673_);
                    v___x_1678_ = v___x_1671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1673_);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1676_);
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
                    v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
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
    mut v_as_1692_: *mut LeanObject,
    mut v_sz_1693_: *mut LeanObject,
    mut v_i_1694_: *mut LeanObject,
    mut v_b_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1702_: usize = 0;
    let mut v_i_boxed_1703_: usize = 0;
    let mut v_res_1704_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1702_ = lean_unbox_usize(v_sz_1693_);
    lean_dec(v_sz_1693_);
    v_i_boxed_1703_ = lean_unbox_usize(v_i_1694_);
    lean_dec(v_i_1694_);
    v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_as_1692_, v_sz_boxed_1702_, v_i_boxed_1703_, v_b_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
    lean_dec(v___y_1700_);
    lean_dec_ref(v___y_1699_);
    lean_dec(v___y_1698_);
    lean_dec_ref(v___y_1697_);
    lean_dec_ref(v_as_1692_);
    return v_res_1704_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(
    mut v_as_1705_: *mut LeanObject,
    mut v_sz_1706_: usize,
    mut v_i_1707_: usize,
    mut v_b_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
    mut v___y_1710_: *mut LeanObject,
    mut v___y_1711_: *mut LeanObject,
    mut v___y_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: usize = 0;
    let mut v___x_1734_: usize = 0;
    let mut v_reuseFailAlloc_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_a_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1715_ = lean_usize_dec_lt(v_i_1707_, v_sz_1706_);
                if v___x_1715_ == 0 {
                    v___x_1716_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1716_, 0, v_b_1708_);
                    lean_ctor_set(v___x_1716_, 1, v___y_1709_);
                    v___x_1717_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1717_, 0, v___x_1716_);
                    return v___x_1717_;
                } else {
                    v_snd_1718_ = lean_ctor_get(v_b_1708_, 1);
                    lean_inc(v_snd_1718_);
                    lean_dec_ref(v_b_1708_);
                    v_a_1719_ = lean_array_uget_borrowed(v_as_1705_, v_i_1707_);
                    lean_inc(v_a_1719_);
                    v___x_1720_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1719_, v___y_1709_);
                    if lean_obj_tag(v___x_1720_) == 0 {
                        v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
                        lean_inc(v_a_1721_);
                        lean_dec_ref_known(v___x_1720_, 1);
                        v_fst_1722_ = lean_ctor_get(v_a_1721_, 0);
                        v_snd_1723_ = lean_ctor_get(v_a_1721_, 1);
                        v_isSharedCheck_1737_ = (!lean_is_exclusive(v_a_1721_)) as u8;
                        if v_isSharedCheck_1737_ == 0 {
                            v___x_1725_ = v_a_1721_;
                            v_isShared_1726_ = v_isSharedCheck_1737_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_1723_);
                            lean_inc(v_fst_1722_);
                            lean_dec(v_a_1721_);
                            v___x_1725_ = lean_box(0);
                            v_isShared_1726_ = v_isSharedCheck_1737_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_1718_);
                        v_a_1738_ = lean_ctor_get(v___x_1720_, 0);
                        v_isSharedCheck_1745_ = (!lean_is_exclusive(v___x_1720_)) as u8;
                        if v_isSharedCheck_1745_ == 0 {
                            v___x_1740_ = v___x_1720_;
                            v_isShared_1741_ = v_isSharedCheck_1745_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1738_);
                            lean_dec(v___x_1720_);
                            v___x_1740_ = lean_box(0);
                            v_isShared_1741_ = v_isSharedCheck_1745_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1727_ = lean_box(0);
                v___x_1728_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1729_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1722_, v___x_1728_);
                v___x_1730_ = lean_array_push(v_snd_1718_, v___x_1729_);
                if v_isShared_1726_ == 0 {
                    lean_ctor_set(v___x_1725_, 1, v___x_1730_);
                    lean_ctor_set(v___x_1725_, 0, v___x_1727_);
                    v___x_1732_ = v___x_1725_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1727_);
                    lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1730_);
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
                    v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
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
    mut v_as_1746_: *mut LeanObject,
    mut v_sz_1747_: *mut LeanObject,
    mut v_i_1748_: *mut LeanObject,
    mut v_b_1749_: *mut LeanObject,
    mut v___y_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
    mut v___y_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
    mut v___y_1754_: *mut LeanObject,
    mut v___y_1755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1756_: usize = 0;
    let mut v_i_boxed_1757_: usize = 0;
    let mut v_res_1758_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1756_ = lean_unbox_usize(v_sz_1747_);
    lean_dec(v_sz_1747_);
    v_i_boxed_1757_ = lean_unbox_usize(v_i_1748_);
    lean_dec(v_i_1748_);
    v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3_spec__4(v_as_1746_, v_sz_boxed_1756_, v_i_boxed_1757_, v_b_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
    lean_dec(v___y_1754_);
    lean_dec_ref(v___y_1753_);
    lean_dec(v___y_1752_);
    lean_dec_ref(v___y_1751_);
    lean_dec_ref(v_as_1746_);
    return v_res_1758_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(
    mut v_as_1759_: *mut LeanObject,
    mut v_sz_1760_: usize,
    mut v_i_1761_: usize,
    mut v_b_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
    mut v___y_1764_: *mut LeanObject,
    mut v___y_1765_: *mut LeanObject,
    mut v___y_1766_: *mut LeanObject,
    mut v___y_1767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: usize = 0;
    let mut v___x_1788_: usize = 0;
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v_a_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1769_ = lean_usize_dec_lt(v_i_1761_, v_sz_1760_);
                if v___x_1769_ == 0 {
                    v___x_1770_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1770_, 0, v_b_1762_);
                    lean_ctor_set(v___x_1770_, 1, v___y_1763_);
                    v___x_1771_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1771_, 0, v___x_1770_);
                    return v___x_1771_;
                } else {
                    v_snd_1772_ = lean_ctor_get(v_b_1762_, 1);
                    lean_inc(v_snd_1772_);
                    lean_dec_ref(v_b_1762_);
                    v_a_1773_ = lean_array_uget_borrowed(v_as_1759_, v_i_1761_);
                    lean_inc(v_a_1773_);
                    v___x_1774_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_a_1773_, v___y_1763_);
                    if lean_obj_tag(v___x_1774_) == 0 {
                        v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
                        lean_inc(v_a_1775_);
                        lean_dec_ref_known(v___x_1774_, 1);
                        v_fst_1776_ = lean_ctor_get(v_a_1775_, 0);
                        v_snd_1777_ = lean_ctor_get(v_a_1775_, 1);
                        v_isSharedCheck_1791_ = (!lean_is_exclusive(v_a_1775_)) as u8;
                        if v_isSharedCheck_1791_ == 0 {
                            v___x_1779_ = v_a_1775_;
                            v_isShared_1780_ = v_isSharedCheck_1791_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_1777_);
                            lean_inc(v_fst_1776_);
                            lean_dec(v_a_1775_);
                            v___x_1779_ = lean_box(0);
                            v_isShared_1780_ = v_isSharedCheck_1791_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_1772_);
                        v_a_1792_ = lean_ctor_get(v___x_1774_, 0);
                        v_isSharedCheck_1799_ = (!lean_is_exclusive(v___x_1774_)) as u8;
                        if v_isSharedCheck_1799_ == 0 {
                            v___x_1794_ = v___x_1774_;
                            v_isShared_1795_ = v_isSharedCheck_1799_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1792_);
                            lean_dec(v___x_1774_);
                            v___x_1794_ = lean_box(0);
                            v_isShared_1795_ = v_isSharedCheck_1799_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1781_ = lean_box(0);
                v___x_1782_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
                v___x_1783_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1(v_fst_1776_, v___x_1782_);
                v___x_1784_ = lean_array_push(v_snd_1772_, v___x_1783_);
                if v_isShared_1780_ == 0 {
                    lean_ctor_set(v___x_1779_, 1, v___x_1784_);
                    lean_ctor_set(v___x_1779_, 0, v___x_1781_);
                    v___x_1786_ = v___x_1779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1781_);
                    lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1784_);
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
                    v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
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
    mut v_as_1800_: *mut LeanObject,
    mut v_sz_1801_: *mut LeanObject,
    mut v_i_1802_: *mut LeanObject,
    mut v_b_1803_: *mut LeanObject,
    mut v___y_1804_: *mut LeanObject,
    mut v___y_1805_: *mut LeanObject,
    mut v___y_1806_: *mut LeanObject,
    mut v___y_1807_: *mut LeanObject,
    mut v___y_1808_: *mut LeanObject,
    mut v___y_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1810_: usize = 0;
    let mut v_i_boxed_1811_: usize = 0;
    let mut v_res_1812_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1810_ = lean_unbox_usize(v_sz_1801_);
    lean_dec(v_sz_1801_);
    v_i_boxed_1811_ = lean_unbox_usize(v_i_1802_);
    lean_dec(v_i_1802_);
    v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_as_1800_, v_sz_boxed_1810_, v_i_boxed_1811_, v_b_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
    lean_dec(v___y_1808_);
    lean_dec_ref(v___y_1807_);
    lean_dec(v___y_1806_);
    lean_dec_ref(v___y_1805_);
    lean_dec_ref(v_as_1800_);
    return v_res_1812_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(
    mut v_init_1813_: *mut LeanObject,
    mut v_n_1814_: *mut LeanObject,
    mut v_b_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1825_: usize = 0;
    let mut v___x_1826_: usize = 0;
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v_fst_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1838_: u8 = 0;
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v_unused_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v_snd_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1859_: u8 = 0;
    let mut v_unused_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_a_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_vs_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1874_: usize = 0;
    let mut v___x_1875_: usize = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v_fst_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1887_: u8 = 0;
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut v_unused_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1899_: u8 = 0;
    let mut v_snd_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1908_: u8 = 0;
    let mut v_unused_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_a_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_1814_) == 0 {
                    v_cs_1822_ = lean_ctor_get(v_n_1814_, 0);
                    v___x_1823_ = lean_box(0);
                    v___x_1824_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1824_, 0, v___x_1823_);
                    lean_ctor_set(v___x_1824_, 1, v_b_1815_);
                    v_sz_1825_ = lean_array_size(v_cs_1822_);
                    v___x_1826_ = 0usize;
                    v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_1813_, v_cs_1822_, v_sz_1825_, v___x_1826_, v___x_1824_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
                    if lean_obj_tag(v___x_1827_) == 0 {
                        v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
                        v_isSharedCheck_1862_ = (!lean_is_exclusive(v___x_1827_)) as u8;
                        if v_isSharedCheck_1862_ == 0 {
                            v___x_1830_ = v___x_1827_;
                            v_isShared_1831_ = v_isSharedCheck_1862_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1828_);
                            lean_dec(v___x_1827_);
                            v___x_1830_ = lean_box(0);
                            v_isShared_1831_ = v_isSharedCheck_1862_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1863_ = lean_ctor_get(v___x_1827_, 0);
                        v_isSharedCheck_1870_ = (!lean_is_exclusive(v___x_1827_)) as u8;
                        if v_isSharedCheck_1870_ == 0 {
                            v___x_1865_ = v___x_1827_;
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1863_);
                            lean_dec(v___x_1827_);
                            v___x_1865_ = lean_box(0);
                            v_isShared_1866_ = v_isSharedCheck_1870_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_vs_1871_ = lean_ctor_get(v_n_1814_, 0);
                    v___x_1872_ = lean_box(0);
                    v___x_1873_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                    lean_ctor_set(v___x_1873_, 1, v_b_1815_);
                    v_sz_1874_ = lean_array_size(v_vs_1871_);
                    v___x_1875_ = 0usize;
                    v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__3(v_vs_1871_, v_sz_1874_, v___x_1875_, v___x_1873_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
                    if lean_obj_tag(v___x_1876_) == 0 {
                        v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
                        v_isSharedCheck_1911_ = (!lean_is_exclusive(v___x_1876_)) as u8;
                        if v_isSharedCheck_1911_ == 0 {
                            v___x_1879_ = v___x_1876_;
                            v_isShared_1880_ = v_isSharedCheck_1911_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1877_);
                            lean_dec(v___x_1876_);
                            v___x_1879_ = lean_box(0);
                            v_isShared_1880_ = v_isSharedCheck_1911_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_a_1912_ = lean_ctor_get(v___x_1876_, 0);
                        v_isSharedCheck_1919_ = (!lean_is_exclusive(v___x_1876_)) as u8;
                        if v_isSharedCheck_1919_ == 0 {
                            v___x_1914_ = v___x_1876_;
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_1912_);
                            lean_dec(v___x_1876_);
                            v___x_1914_ = lean_box(0);
                            v_isShared_1915_ = v_isSharedCheck_1919_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1832_ = lean_ctor_get(v_a_1828_, 0);
                lean_inc(v_fst_1832_);
                v_fst_1833_ = lean_ctor_get(v_fst_1832_, 0);
                if lean_obj_tag(v_fst_1833_) == 0 {
                    v_snd_1834_ = lean_ctor_get(v_a_1828_, 1);
                    lean_inc(v_snd_1834_);
                    lean_dec(v_a_1828_);
                    v_snd_1835_ = lean_ctor_get(v_fst_1832_, 1);
                    v_isSharedCheck_1846_ = (!lean_is_exclusive(v_fst_1832_)) as u8;
                    if v_isSharedCheck_1846_ == 0 {
                        v_unused_1847_ = lean_ctor_get(v_fst_1832_, 0);
                        lean_dec(v_unused_1847_);
                        v___x_1837_ = v_fst_1832_;
                        v_isShared_1838_ = v_isSharedCheck_1846_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_1835_);
                        lean_dec(v_fst_1832_);
                        v___x_1837_ = lean_box(0);
                        v_isShared_1838_ = v_isSharedCheck_1846_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_1833_);
                    v_isSharedCheck_1859_ = (!lean_is_exclusive(v_fst_1832_)) as u8;
                    if v_isSharedCheck_1859_ == 0 {
                        v_unused_1860_ = lean_ctor_get(v_fst_1832_, 1);
                        lean_dec(v_unused_1860_);
                        v_unused_1861_ = lean_ctor_get(v_fst_1832_, 0);
                        lean_dec(v_unused_1861_);
                        v___x_1849_ = v_fst_1832_;
                        v_isShared_1850_ = v_isSharedCheck_1859_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_fst_1832_);
                        v___x_1849_ = lean_box(0);
                        v_isShared_1850_ = v_isSharedCheck_1859_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1839_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1839_, 0, v_snd_1835_);
                if v_isShared_1838_ == 0 {
                    lean_ctor_set(v___x_1837_, 1, v_snd_1834_);
                    lean_ctor_set(v___x_1837_, 0, v___x_1839_);
                    v___x_1841_ = v___x_1837_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1839_);
                    lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_snd_1834_);
                    v___x_1841_ = v_reuseFailAlloc_1845_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1831_ == 0 {
                    lean_ctor_set(v___x_1830_, 0, v___x_1841_);
                    v___x_1843_ = v___x_1830_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
                    v___x_1843_ = v_reuseFailAlloc_1844_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1843_;
            }
            5 => {
                v_snd_1851_ = lean_ctor_get(v_a_1828_, 1);
                lean_inc(v_snd_1851_);
                lean_dec(v_a_1828_);
                v_val_1852_ = lean_ctor_get(v_fst_1833_, 0);
                lean_inc(v_val_1852_);
                lean_dec_ref_known(v_fst_1833_, 1);
                if v_isShared_1850_ == 0 {
                    lean_ctor_set(v___x_1849_, 1, v_snd_1851_);
                    lean_ctor_set(v___x_1849_, 0, v_val_1852_);
                    v___x_1854_ = v___x_1849_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_val_1852_);
                    lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_snd_1851_);
                    v___x_1854_ = v_reuseFailAlloc_1858_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1831_ == 0 {
                    lean_ctor_set(v___x_1830_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1830_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
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
                    v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
                    v___x_1868_ = v_reuseFailAlloc_1869_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1868_;
            }
            10 => {
                v_fst_1881_ = lean_ctor_get(v_a_1877_, 0);
                lean_inc(v_fst_1881_);
                v_fst_1882_ = lean_ctor_get(v_fst_1881_, 0);
                if lean_obj_tag(v_fst_1882_) == 0 {
                    v_snd_1883_ = lean_ctor_get(v_a_1877_, 1);
                    lean_inc(v_snd_1883_);
                    lean_dec(v_a_1877_);
                    v_snd_1884_ = lean_ctor_get(v_fst_1881_, 1);
                    v_isSharedCheck_1895_ = (!lean_is_exclusive(v_fst_1881_)) as u8;
                    if v_isSharedCheck_1895_ == 0 {
                        v_unused_1896_ = lean_ctor_get(v_fst_1881_, 0);
                        lean_dec(v_unused_1896_);
                        v___x_1886_ = v_fst_1881_;
                        v_isShared_1887_ = v_isSharedCheck_1895_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_snd_1884_);
                        lean_dec(v_fst_1881_);
                        v___x_1886_ = lean_box(0);
                        v_isShared_1887_ = v_isSharedCheck_1895_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_1882_);
                    v_isSharedCheck_1908_ = (!lean_is_exclusive(v_fst_1881_)) as u8;
                    if v_isSharedCheck_1908_ == 0 {
                        v_unused_1909_ = lean_ctor_get(v_fst_1881_, 1);
                        lean_dec(v_unused_1909_);
                        v_unused_1910_ = lean_ctor_get(v_fst_1881_, 0);
                        lean_dec(v_unused_1910_);
                        v___x_1898_ = v_fst_1881_;
                        v_isShared_1899_ = v_isSharedCheck_1908_;
                        state = 14;
                        continue;
                    } else {
                        lean_dec(v_fst_1881_);
                        v___x_1898_ = lean_box(0);
                        v_isShared_1899_ = v_isSharedCheck_1908_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v___x_1888_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1888_, 0, v_snd_1884_);
                if v_isShared_1887_ == 0 {
                    lean_ctor_set(v___x_1886_, 1, v_snd_1883_);
                    lean_ctor_set(v___x_1886_, 0, v___x_1888_);
                    v___x_1890_ = v___x_1886_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1888_);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_snd_1883_);
                    v___x_1890_ = v_reuseFailAlloc_1894_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_1880_ == 0 {
                    lean_ctor_set(v___x_1879_, 0, v___x_1890_);
                    v___x_1892_ = v___x_1879_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1893_, 0, v___x_1890_);
                    v___x_1892_ = v_reuseFailAlloc_1893_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1892_;
            }
            14 => {
                v_snd_1900_ = lean_ctor_get(v_a_1877_, 1);
                lean_inc(v_snd_1900_);
                lean_dec(v_a_1877_);
                v_val_1901_ = lean_ctor_get(v_fst_1882_, 0);
                lean_inc(v_val_1901_);
                lean_dec_ref_known(v_fst_1882_, 1);
                if v_isShared_1899_ == 0 {
                    lean_ctor_set(v___x_1898_, 1, v_snd_1900_);
                    lean_ctor_set(v___x_1898_, 0, v_val_1901_);
                    v___x_1903_ = v___x_1898_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_val_1901_);
                    lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_snd_1900_);
                    v___x_1903_ = v_reuseFailAlloc_1907_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1880_ == 0 {
                    lean_ctor_set(v___x_1879_, 0, v___x_1903_);
                    v___x_1905_ = v___x_1879_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1903_);
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
                    v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
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
    mut v_init_1920_: *mut LeanObject,
    mut v_as_1921_: *mut LeanObject,
    mut v_sz_1922_: usize,
    mut v_i_1923_: usize,
    mut v_b_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
    mut v___y_1927_: *mut LeanObject,
    mut v___y_1928_: *mut LeanObject,
    mut v___y_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1931_: u8 = 0;
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v_a_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1943_: u8 = 0;
    let mut v_fst_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v_unused_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1964_: u8 = 0;
    let mut v_a_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: usize = 0;
    let mut v___x_1970_: usize = 0;
    let mut v_reuseFailAlloc_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1973_: u8 = 0;
    let mut v_unused_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut v_a_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1979_: u8 = 0;
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_isSharedCheck_1984_: u8 = 0;
    let mut v_unused_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1931_ = lean_usize_dec_lt(v_i_1923_, v_sz_1922_);
                if v___x_1931_ == 0 {
                    v___x_1932_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1932_, 0, v_b_1924_);
                    lean_ctor_set(v___x_1932_, 1, v___y_1925_);
                    v___x_1933_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1933_, 0, v___x_1932_);
                    return v___x_1933_;
                } else {
                    v_snd_1934_ = lean_ctor_get(v_b_1924_, 1);
                    v_isSharedCheck_1984_ = (!lean_is_exclusive(v_b_1924_)) as u8;
                    if v_isSharedCheck_1984_ == 0 {
                        v_unused_1985_ = lean_ctor_get(v_b_1924_, 0);
                        lean_dec(v_unused_1985_);
                        v___x_1936_ = v_b_1924_;
                        v_isShared_1937_ = v_isSharedCheck_1984_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1934_);
                        lean_dec(v_b_1924_);
                        v___x_1936_ = lean_box(0);
                        v_isShared_1937_ = v_isSharedCheck_1984_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1938_ = lean_array_uget_borrowed(v_as_1921_, v_i_1923_);
                lean_inc(v_snd_1934_);
                v___x_1939_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_1920_, v_a_1938_, v_snd_1934_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
                if lean_obj_tag(v___x_1939_) == 0 {
                    v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
                    v_isSharedCheck_1975_ = (!lean_is_exclusive(v___x_1939_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1942_ = v___x_1939_;
                        v_isShared_1943_ = v_isSharedCheck_1975_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1940_);
                        lean_dec(v___x_1939_);
                        v___x_1942_ = lean_box(0);
                        v_isShared_1943_ = v_isSharedCheck_1975_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1936_);
                    lean_dec(v_snd_1934_);
                    v_a_1976_ = lean_ctor_get(v___x_1939_, 0);
                    v_isSharedCheck_1983_ = (!lean_is_exclusive(v___x_1939_)) as u8;
                    if v_isSharedCheck_1983_ == 0 {
                        v___x_1978_ = v___x_1939_;
                        v_isShared_1979_ = v_isSharedCheck_1983_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1976_);
                        lean_dec(v___x_1939_);
                        v___x_1978_ = lean_box(0);
                        v_isShared_1979_ = v_isSharedCheck_1983_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1944_ = lean_ctor_get(v_a_1940_, 0);
                lean_inc(v_fst_1944_);
                if lean_obj_tag(v_fst_1944_) == 0 {
                    v_snd_1945_ = lean_ctor_get(v_a_1940_, 1);
                    v_isSharedCheck_1959_ = (!lean_is_exclusive(v_a_1940_)) as u8;
                    if v_isSharedCheck_1959_ == 0 {
                        v_unused_1960_ = lean_ctor_get(v_a_1940_, 0);
                        lean_dec(v_unused_1960_);
                        v___x_1947_ = v_a_1940_;
                        v_isShared_1948_ = v_isSharedCheck_1959_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_1945_);
                        lean_dec(v_a_1940_);
                        v___x_1947_ = lean_box(0);
                        v_isShared_1948_ = v_isSharedCheck_1959_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1942_);
                    lean_del_object(v___x_1936_);
                    lean_dec(v_snd_1934_);
                    v_snd_1961_ = lean_ctor_get(v_a_1940_, 1);
                    v_isSharedCheck_1973_ = (!lean_is_exclusive(v_a_1940_)) as u8;
                    if v_isSharedCheck_1973_ == 0 {
                        v_unused_1974_ = lean_ctor_get(v_a_1940_, 0);
                        lean_dec(v_unused_1974_);
                        v___x_1963_ = v_a_1940_;
                        v_isShared_1964_ = v_isSharedCheck_1973_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_snd_1961_);
                        lean_dec(v_a_1940_);
                        v___x_1963_ = lean_box(0);
                        v_isShared_1964_ = v_isSharedCheck_1973_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1949_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1949_, 0, v_fst_1944_);
                if v_isShared_1948_ == 0 {
                    lean_ctor_set(v___x_1947_, 1, v_snd_1934_);
                    lean_ctor_set(v___x_1947_, 0, v___x_1949_);
                    v___x_1951_ = v___x_1947_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1949_);
                    lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_snd_1934_);
                    v___x_1951_ = v_reuseFailAlloc_1958_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1937_ == 0 {
                    lean_ctor_set(v___x_1936_, 1, v_snd_1945_);
                    lean_ctor_set(v___x_1936_, 0, v___x_1951_);
                    v___x_1953_ = v___x_1936_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1951_);
                    lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_snd_1945_);
                    v___x_1953_ = v_reuseFailAlloc_1957_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1943_ == 0 {
                    lean_ctor_set(v___x_1942_, 0, v___x_1953_);
                    v___x_1955_ = v___x_1942_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
                    v___x_1955_ = v_reuseFailAlloc_1956_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1955_;
            }
            7 => {
                v_a_1965_ = lean_ctor_get(v_fst_1944_, 0);
                lean_inc(v_a_1965_);
                lean_dec_ref_known(v_fst_1944_, 1);
                v___x_1966_ = lean_box(0);
                if v_isShared_1964_ == 0 {
                    lean_ctor_set(v___x_1963_, 1, v_a_1965_);
                    lean_ctor_set(v___x_1963_, 0, v___x_1966_);
                    v___x_1968_ = v___x_1963_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1966_);
                    lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_a_1965_);
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
                    v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
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
    mut v_init_1986_: *mut LeanObject,
    mut v_as_1987_: *mut LeanObject,
    mut v_sz_1988_: *mut LeanObject,
    mut v_i_1989_: *mut LeanObject,
    mut v_b_1990_: *mut LeanObject,
    mut v___y_1991_: *mut LeanObject,
    mut v___y_1992_: *mut LeanObject,
    mut v___y_1993_: *mut LeanObject,
    mut v___y_1994_: *mut LeanObject,
    mut v___y_1995_: *mut LeanObject,
    mut v___y_1996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1997_: usize = 0;
    let mut v_i_boxed_1998_: usize = 0;
    let mut v_res_1999_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1997_ = lean_unbox_usize(v_sz_1988_);
    lean_dec(v_sz_1988_);
    v_i_boxed_1998_ = lean_unbox_usize(v_i_1989_);
    lean_dec(v_i_1989_);
    v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1_spec__2(v_init_1986_, v_as_1987_, v_sz_boxed_1997_, v_i_boxed_1998_, v_b_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
    lean_dec(v___y_1995_);
    lean_dec_ref(v___y_1994_);
    lean_dec(v___y_1993_);
    lean_dec_ref(v___y_1992_);
    lean_dec_ref(v_as_1987_);
    lean_dec_ref(v_init_1986_);
    return v_res_1999_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1___boxed(
    mut v_init_2000_: *mut LeanObject,
    mut v_n_2001_: *mut LeanObject,
    mut v_b_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2009_: *mut LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_2000_, v_n_2001_, v_b_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
    lean_dec(v___y_2007_);
    lean_dec_ref(v___y_2006_);
    lean_dec(v___y_2005_);
    lean_dec_ref(v___y_2004_);
    lean_dec_ref(v_n_2001_);
    lean_dec_ref(v_init_2000_);
    return v_res_2009_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(
    mut v_t_2010_: *mut LeanObject,
    mut v_init_2011_: *mut LeanObject,
    mut v___y_2012_: *mut LeanObject,
    mut v___y_2013_: *mut LeanObject,
    mut v___y_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_root_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2033_: u8 = 0;
    let mut v_a_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2038_: usize = 0;
    let mut v___x_2039_: usize = 0;
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2044_: u8 = 0;
    let mut v_fst_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_unused_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2062_: u8 = 0;
    let mut v_a_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2066_: u8 = 0;
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_reuseFailAlloc_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v_unused_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2081_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2023_ = lean_ctor_get(v_t_2010_, 0);
                v_tail_2024_ = lean_ctor_get(v_t_2010_, 1);
                lean_inc_ref(v_init_2011_);
                v___x_2025_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__1(v_init_2011_, v_root_2023_, v_init_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
                lean_dec_ref(v_init_2011_);
                if lean_obj_tag(v___x_2025_) == 0 {
                    v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
                    lean_inc(v_a_2026_);
                    lean_dec_ref_known(v___x_2025_, 1);
                    v_fst_2027_ = lean_ctor_get(v_a_2026_, 0);
                    lean_inc(v_fst_2027_);
                    if lean_obj_tag(v_fst_2027_) == 0 {
                        v_snd_2028_ = lean_ctor_get(v_a_2026_, 1);
                        lean_inc(v_snd_2028_);
                        lean_dec(v_a_2026_);
                        v_a_2029_ = lean_ctor_get(v_fst_2027_, 0);
                        lean_inc(v_a_2029_);
                        lean_dec_ref_known(v_fst_2027_, 1);
                        v_b_2019_ = v_a_2029_;
                        v___y_2020_ = v_snd_2028_;
                        state = 1;
                        continue;
                    } else {
                        v_snd_2030_ = lean_ctor_get(v_a_2026_, 1);
                        v_isSharedCheck_2072_ = (!lean_is_exclusive(v_a_2026_)) as u8;
                        if v_isSharedCheck_2072_ == 0 {
                            v_unused_2073_ = lean_ctor_get(v_a_2026_, 0);
                            lean_dec(v_unused_2073_);
                            v___x_2032_ = v_a_2026_;
                            v_isShared_2033_ = v_isSharedCheck_2072_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_2030_);
                            lean_dec(v_a_2026_);
                            v___x_2032_ = lean_box(0);
                            v_isShared_2033_ = v_isSharedCheck_2072_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_a_2074_ = lean_ctor_get(v___x_2025_, 0);
                    v_isSharedCheck_2081_ = (!lean_is_exclusive(v___x_2025_)) as u8;
                    if v_isSharedCheck_2081_ == 0 {
                        v___x_2076_ = v___x_2025_;
                        v_isShared_2077_ = v_isSharedCheck_2081_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2074_);
                        lean_dec(v___x_2025_);
                        v___x_2076_ = lean_box(0);
                        v_isShared_2077_ = v_isSharedCheck_2081_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2021_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2021_, 0, v_b_2019_);
                lean_ctor_set(v___x_2021_, 1, v___y_2020_);
                v___x_2022_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2022_, 0, v___x_2021_);
                return v___x_2022_;
            }
            2 => {
                v_a_2034_ = lean_ctor_get(v_fst_2027_, 0);
                lean_inc(v_a_2034_);
                lean_dec_ref_known(v_fst_2027_, 1);
                v___x_2035_ = lean_box(0);
                if v_isShared_2033_ == 0 {
                    lean_ctor_set(v___x_2032_, 1, v_a_2034_);
                    lean_ctor_set(v___x_2032_, 0, v___x_2035_);
                    v___x_2037_ = v___x_2032_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2035_);
                    lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_a_2034_);
                    v___x_2037_ = v_reuseFailAlloc_2071_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_sz_2038_ = lean_array_size(v_tail_2024_);
                v___x_2039_ = 0usize;
                v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1_spec__2(v_tail_2024_, v_sz_2038_, v___x_2039_, v___x_2037_, v_snd_2030_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
                if lean_obj_tag(v___x_2040_) == 0 {
                    v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
                    v_isSharedCheck_2062_ = (!lean_is_exclusive(v___x_2040_)) as u8;
                    if v_isSharedCheck_2062_ == 0 {
                        v___x_2043_ = v___x_2040_;
                        v_isShared_2044_ = v_isSharedCheck_2062_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2041_);
                        lean_dec(v___x_2040_);
                        v___x_2043_ = lean_box(0);
                        v_isShared_2044_ = v_isSharedCheck_2062_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2063_ = lean_ctor_get(v___x_2040_, 0);
                    v_isSharedCheck_2070_ = (!lean_is_exclusive(v___x_2040_)) as u8;
                    if v_isSharedCheck_2070_ == 0 {
                        v___x_2065_ = v___x_2040_;
                        v_isShared_2066_ = v_isSharedCheck_2070_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2063_);
                        lean_dec(v___x_2040_);
                        v___x_2065_ = lean_box(0);
                        v_isShared_2066_ = v_isSharedCheck_2070_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_2045_ = lean_ctor_get(v_a_2041_, 0);
                lean_inc(v_fst_2045_);
                v_fst_2046_ = lean_ctor_get(v_fst_2045_, 0);
                if lean_obj_tag(v_fst_2046_) == 0 {
                    v_snd_2047_ = lean_ctor_get(v_a_2041_, 1);
                    lean_inc(v_snd_2047_);
                    lean_dec(v_a_2041_);
                    v_snd_2048_ = lean_ctor_get(v_fst_2045_, 1);
                    v_isSharedCheck_2058_ = (!lean_is_exclusive(v_fst_2045_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v_unused_2059_ = lean_ctor_get(v_fst_2045_, 0);
                        lean_dec(v_unused_2059_);
                        v___x_2050_ = v_fst_2045_;
                        v_isShared_2051_ = v_isSharedCheck_2058_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_2048_);
                        lean_dec(v_fst_2045_);
                        v___x_2050_ = lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2058_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2046_);
                    lean_dec(v_fst_2045_);
                    lean_del_object(v___x_2043_);
                    v_snd_2060_ = lean_ctor_get(v_a_2041_, 1);
                    lean_inc(v_snd_2060_);
                    lean_dec(v_a_2041_);
                    v_val_2061_ = lean_ctor_get(v_fst_2046_, 0);
                    lean_inc(v_val_2061_);
                    lean_dec_ref_known(v_fst_2046_, 1);
                    v_b_2019_ = v_val_2061_;
                    v___y_2020_ = v_snd_2060_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_2051_ == 0 {
                    lean_ctor_set(v___x_2050_, 1, v_snd_2047_);
                    lean_ctor_set(v___x_2050_, 0, v_snd_2048_);
                    v___x_2053_ = v___x_2050_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_snd_2048_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_snd_2047_);
                    v___x_2053_ = v_reuseFailAlloc_2057_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2044_ == 0 {
                    lean_ctor_set(v___x_2043_, 0, v___x_2053_);
                    v___x_2055_ = v___x_2043_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
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
                    v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
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
                    v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
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
    mut v_t_2082_: *mut LeanObject,
    mut v_init_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
    mut v___y_2086_: *mut LeanObject,
    mut v___y_2087_: *mut LeanObject,
    mut v___y_2088_: *mut LeanObject,
    mut v___y_2089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2090_: *mut LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_t_2082_, v_init_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
    lean_dec(v___y_2088_);
    lean_dec_ref(v___y_2087_);
    lean_dec(v___y_2086_);
    lean_dec_ref(v___y_2085_);
    lean_dec_ref(v_t_2082_);
    return v_res_2090_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3()
-> *mut LeanObject {
    let mut v___f_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    v___f_2095_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__0;
    v___x_2096_ = lean_mk_thunk(v___f_2095_);
    return v___x_2096_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(
    mut v_a_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_a_2099_: *mut LeanObject,
    mut v_a_2100_: *mut LeanObject,
    mut v_a_2101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_diseqs_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v_fst_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut v_a_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2129_: u8 = 0;
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_diseqs_2103_ = lean_ctor_get(v_a_2097_, 16);
                lean_inc_ref(v_diseqs_2103_);
                v_diseqs_2104_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
                v___x_2105_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__1(v_diseqs_2103_, v_diseqs_2104_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
                lean_dec_ref(v_diseqs_2103_);
                if lean_obj_tag(v___x_2105_) == 0 {
                    v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2125_ = (!lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2125_ == 0 {
                        v___x_2108_ = v___x_2105_;
                        v_isShared_2109_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2106_);
                        lean_dec(v___x_2105_);
                        v___x_2108_ = lean_box(0);
                        v_isShared_2109_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2126_ = lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2133_ = (!lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2133_ == 0 {
                        v___x_2128_ = v___x_2105_;
                        v_isShared_2129_ = v_isSharedCheck_2133_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2126_);
                        lean_dec(v___x_2105_);
                        v___x_2128_ = lean_box(0);
                        v_isShared_2129_ = v_isSharedCheck_2133_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2110_ = lean_ctor_get(v_a_2106_, 0);
                v_snd_2111_ = lean_ctor_get(v_a_2106_, 1);
                v_isSharedCheck_2124_ = (!lean_is_exclusive(v_a_2106_)) as u8;
                if v_isSharedCheck_2124_ == 0 {
                    v___x_2113_ = v_a_2106_;
                    v_isShared_2114_ = v_isSharedCheck_2124_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2111_);
                    lean_inc(v_fst_2110_);
                    lean_dec(v_a_2106_);
                    v___x_2113_ = lean_box(0);
                    v_isShared_2114_ = v_isSharedCheck_2124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2115_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__2;
                v___x_2116_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f___closed__3);
                v___x_2117_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
                        v___x_2115_,
                        v___x_2116_,
                        v_fst_2110_,
                    );
                if v_isShared_2114_ == 0 {
                    lean_ctor_set(v___x_2113_, 0, v___x_2117_);
                    v___x_2119_ = v___x_2113_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2117_);
                    lean_ctor_set(v_reuseFailAlloc_2123_, 1, v_snd_2111_);
                    v___x_2119_ = v_reuseFailAlloc_2123_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2109_ == 0 {
                    lean_ctor_set(v___x_2108_, 0, v___x_2119_);
                    v___x_2121_ = v___x_2108_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
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
                    v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
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
    mut v_a_2134_: *mut LeanObject,
    mut v_a_2135_: *mut LeanObject,
    mut v_a_2136_: *mut LeanObject,
    mut v_a_2137_: *mut LeanObject,
    mut v_a_2138_: *mut LeanObject,
    mut v_a_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2140_: *mut LeanObject = core::ptr::null_mut();
    v_res_2140_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f(
        v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_,
    );
    lean_dec(v_a_2138_);
    lean_dec_ref(v_a_2137_);
    lean_dec(v_a_2136_);
    lean_dec_ref(v_a_2135_);
    return v_res_2140_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(
    mut v_c_2141_: *mut LeanObject,
    mut v___y_2142_: *mut LeanObject,
    mut v___y_2143_: *mut LeanObject,
    mut v___y_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    v___x_2148_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___redArg(v_c_2141_, v___y_2142_);
    return v___x_2148_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0___boxed(
    mut v_c_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2156_: *mut LeanObject = core::ptr::null_mut();
    v_res_2156_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppDiseqs_x3f_spec__0(v_c_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
    lean_dec(v___y_2154_);
    lean_dec_ref(v___y_2153_);
    lean_dec(v___y_2152_);
    lean_dec_ref(v___y_2151_);
    return v_res_2156_;
}
pub unsafe fn l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__0(
    mut v_e_2157_: *mut LeanObject,
    mut v_cls_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: f64 = 0.0;
    let mut v___x_2161_: u8 = 0;
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    v___x_2159_ = lean_box(0);
    v___x_2160_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_2161_ = 1;
    v___x_2162_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_2163_ = lean_alloc_ctor(0, 3, (17) as u32);
    lean_ctor_set(v___x_2163_, 0, v_cls_2158_);
    lean_ctor_set(v___x_2163_, 1, v___x_2159_);
    lean_ctor_set(v___x_2163_, 2, v___x_2162_);
    lean_ctor_set_float(
        v___x_2163_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2160_,
    );
    lean_ctor_set_float(
        v___x_2163_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        v___x_2160_,
    );
    lean_ctor_set_uint8(
        v___x_2163_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
        v___x_2161_,
    );
    v___x_2164_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_2165_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_2165_, 0, v___x_2163_);
    lean_ctor_set(v___x_2165_, 1, v_e_2157_);
    lean_ctor_set(v___x_2165_, 2, v___x_2164_);
    return v___x_2165_;
}
pub unsafe fn l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(
    mut v_e_2166_: *mut LeanObject,
    mut v_cls_2167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: f64 = 0.0;
    let mut v___x_2170_: u8 = 0;
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    v___x_2168_ = lean_box(0);
    v___x_2169_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_2170_ = 1;
    v___x_2171_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_2172_ = lean_alloc_ctor(0, 3, (17) as u32);
    lean_ctor_set(v___x_2172_, 0, v_cls_2167_);
    lean_ctor_set(v___x_2172_, 1, v___x_2168_);
    lean_ctor_set(v___x_2172_, 2, v___x_2171_);
    lean_ctor_set_float(
        v___x_2172_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2169_,
    );
    lean_ctor_set_float(
        v___x_2172_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        v___x_2169_,
    );
    lean_ctor_set_uint8(
        v___x_2172_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
        v___x_2170_,
    );
    v___x_2173_ = l_Lean_stringToMessageData(v_e_2166_);
    v___x_2174_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_2175_ = lean_alloc_ctor(9, 3, (0) as u32);
    lean_ctor_set(v___x_2175_, 0, v___x_2172_);
    lean_ctor_set(v___x_2175_, 1, v___x_2173_);
    lean_ctor_set(v___x_2175_, 2, v___x_2174_);
    return v___x_2175_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    v___x_2177_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__0;
    v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
    return v___x_2178_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    v___x_2180_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__2;
    v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0(
    mut v___y_2182_: *mut LeanObject,
    mut v_x_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_op_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    v_op_2184_ = lean_ctor_get(v___y_2182_, 3);
    lean_inc_ref(v_op_2184_);
    lean_dec_ref(v___y_2182_);
    v___x_2185_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__1);
    v___x_2186_ = l_Lean_MessageData_ofExpr(v_op_2184_);
    v___x_2187_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2187_, 0, v___x_2185_);
    lean_ctor_set(v___x_2187_, 1, v___x_2186_);
    v___x_2188_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
    v___x_2189_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2189_, 0, v___x_2187_);
    lean_ctor_set(v___x_2189_, 1, v___x_2188_);
    return v___x_2189_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2()
-> *mut LeanObject {
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    v___x_2193_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__1;
    v___x_2194_ = l_Lean_MessageData_ofFormat(v___x_2193_);
    return v___x_2194_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1(
    mut v_x_2195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    v___x_2196_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__1___closed__2);
    return v___x_2196_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5()
-> *mut LeanObject {
    let mut v___f_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    v___f_2204_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__2;
    v___x_2205_ = lean_mk_thunk(v___f_2204_);
    return v___x_2205_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7()
-> *mut LeanObject {
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    v___x_2207_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__6;
    v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
    return v___x_2208_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9()
-> *mut LeanObject {
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    v___x_2210_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
    v___x_2211_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__8;
    v___x_2212_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_2211_, v___x_2210_);
    return v___x_2212_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11()
-> *mut LeanObject {
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    v___x_2214_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__2___redArg___closed__1;
    v___x_2215_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__10;
    v___x_2216_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f_spec__1(v___x_2215_, v___x_2214_);
    return v___x_2216_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12()
-> *mut LeanObject {
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgs_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    v___x_2217_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__11);
    v_msgs_2218_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
    v___x_2219_ = lean_array_push(v_msgs_2218_, v___x_2217_);
    return v___x_2219_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(
    mut v_a_2220_: *mut LeanObject,
    mut v_a_2221_: *mut LeanObject,
    mut v_a_2222_: *mut LeanObject,
    mut v_a_2223_: *mut LeanObject,
    mut v_a_2224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_msgs_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2241_: u8 = 0;
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgs_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: u8 = 0;
    let mut v_neutral_x3f_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idempotentInst_x3f_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commInst_x3f_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idempotentInst_x3f_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2235_) == 0 {
                    v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
                    lean_inc(v_a_2236_);
                    lean_dec_ref_known(v___x_2235_, 1);
                    v_fst_2237_ = lean_ctor_get(v_a_2236_, 0);
                    v_snd_2238_ = lean_ctor_get(v_a_2236_, 1);
                    v_isSharedCheck_2296_ = (!lean_is_exclusive(v_a_2236_)) as u8;
                    if v_isSharedCheck_2296_ == 0 {
                        v___x_2240_ = v_a_2236_;
                        v_isShared_2241_ = v_isSharedCheck_2296_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_2238_);
                        lean_inc(v_fst_2237_);
                        lean_dec(v_a_2236_);
                        v___x_2240_ = lean_box(0);
                        v_isShared_2241_ = v_isSharedCheck_2296_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2235_;
                }
            }
            1 => {
                lean_inc_ref(v___y_2228_);
                v___f_2229_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_2229_, 0, v___y_2228_);
                v___x_2230_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1;
                v___x_2231_ = lean_mk_thunk(v___f_2229_);
                v___x_2232_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption(
                        v___x_2230_,
                        v___x_2231_,
                        v_msgs_2227_,
                    );
                lean_dec_ref(v___x_2231_);
                v___x_2233_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2233_, 0, v___x_2232_);
                lean_ctor_set(v___x_2233_, 1, v___y_2228_);
                v___x_2234_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2234_, 0, v___x_2233_);
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
                if lean_obj_tag(v___x_2242_) == 0 {
                    v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
                    lean_inc(v_a_2243_);
                    lean_dec_ref_known(v___x_2242_, 1);
                    v_fst_2244_ = lean_ctor_get(v_a_2243_, 0);
                    v_snd_2245_ = lean_ctor_get(v_a_2243_, 1);
                    v_isSharedCheck_2295_ = (!lean_is_exclusive(v_a_2243_)) as u8;
                    if v_isSharedCheck_2295_ == 0 {
                        v___x_2247_ = v_a_2243_;
                        v_isShared_2248_ = v_isSharedCheck_2295_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_2245_);
                        lean_inc(v_fst_2244_);
                        lean_dec(v_a_2243_);
                        v___x_2247_ = lean_box(0);
                        v_isShared_2248_ = v_isSharedCheck_2295_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2240_);
                    lean_dec(v_fst_2237_);
                    return v___x_2242_;
                }
            }
            3 => {
                v___x_2249_ = lean_unsigned_to_nat(0);
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
                    v_neutral_x3f_2255_ = lean_ctor_get(v_snd_2245_, 4);
                    lean_inc(v_neutral_x3f_2255_);
                    v_idempotentInst_x3f_2256_ = lean_ctor_get(v_snd_2245_, 6);
                    lean_inc(v_idempotentInst_x3f_2256_);
                    v_commInst_x3f_2257_ = lean_ctor_get(v_snd_2245_, 7);
                    if lean_obj_tag(v_commInst_x3f_2257_) == 0 {
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
                    lean_del_object(v___x_2247_);
                    lean_del_object(v___x_2240_);
                    v_msgs_2227_ = v___x_2252_;
                    v___y_2228_ = v_snd_2245_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_2261_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__4;
                v___x_2262_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__5);
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
                if lean_obj_tag(v_neutral_x3f_2268_) == 1 {
                    v_val_2269_ = lean_ctor_get(v_neutral_x3f_2268_, 0);
                    lean_inc(v_val_2269_);
                    lean_dec_ref_known(v_neutral_x3f_2268_, 1);
                    v___x_2270_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__7);
                    v___x_2271_ = l_Lean_MessageData_ofExpr(v_val_2269_);
                    if v_isShared_2248_ == 0 {
                        lean_ctor_set_tag(v___x_2247_, 7);
                        lean_ctor_set(v___x_2247_, 1, v___x_2271_);
                        lean_ctor_set(v___x_2247_, 0, v___x_2270_);
                        v___x_2273_ = v___x_2247_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2281_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2270_);
                        lean_ctor_set(v_reuseFailAlloc_2281_, 1, v___x_2271_);
                        v___x_2273_ = v_reuseFailAlloc_2281_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_neutral_x3f_2268_);
                    lean_del_object(v___x_2247_);
                    lean_del_object(v___x_2240_);
                    v_info_2259_ = v_info_2266_;
                    v___y_2260_ = v___y_2267_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_2274_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___lam__0___closed__3);
                if v_isShared_2241_ == 0 {
                    lean_ctor_set_tag(v___x_2240_, 7);
                    lean_ctor_set(v___x_2240_, 1, v___x_2274_);
                    lean_ctor_set(v___x_2240_, 0, v___x_2273_);
                    v___x_2276_ = v___x_2240_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2280_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2273_);
                    lean_ctor_set(v_reuseFailAlloc_2280_, 1, v___x_2274_);
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
                v_neutral_x3f_2285_ = lean_ctor_get(v___y_2283_, 4);
                lean_inc(v_neutral_x3f_2285_);
                v___x_2286_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__9);
                v___x_2287_ = lean_array_push(v___y_2284_, v___x_2286_);
                v_info_2266_ = v___x_2287_;
                v___y_2267_ = v___y_2283_;
                v_neutral_x3f_2268_ = v_neutral_x3f_2285_;
                state = 5;
                continue;
            }
            9 => {
                if lean_obj_tag(v_idempotentInst_x3f_2292_) == 0 {
                    if v___x_2254_ == 0 {
                        v_info_2266_ = v_info_2289_;
                        v___y_2267_ = v___y_2290_;
                        v_neutral_x3f_2268_ = v_neutral_x3f_2291_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_neutral_x3f_2291_);
                        v___y_2283_ = v___y_2290_;
                        v___y_2284_ = v_info_2289_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_idempotentInst_x3f_2292_, 1);
                    lean_dec(v_neutral_x3f_2291_);
                    v___y_2283_ = v___y_2290_;
                    v___y_2284_ = v_info_2289_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_2294_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__12);
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
    mut v_a_2297_: *mut LeanObject,
    mut v_a_2298_: *mut LeanObject,
    mut v_a_2299_: *mut LeanObject,
    mut v_a_2300_: *mut LeanObject,
    mut v_a_2301_: *mut LeanObject,
    mut v_a_2302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2303_: *mut LeanObject = core::ptr::null_mut();
    v_res_2303_ = l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(
        v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_,
    );
    lean_dec(v_a_2301_);
    lean_dec_ref(v_a_2300_);
    lean_dec(v_a_2299_);
    lean_dec_ref(v_a_2298_);
    return v_res_2303_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(
    mut v_as_2304_: *mut LeanObject,
    mut v_sz_2305_: usize,
    mut v_i_2306_: usize,
    mut v_b_2307_: *mut LeanObject,
    mut v___y_2308_: *mut LeanObject,
    mut v___y_2309_: *mut LeanObject,
    mut v___y_2310_: *mut LeanObject,
    mut v___y_2311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: usize = 0;
    let mut v___x_2316_: usize = 0;
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2318_ = lean_usize_dec_lt(v_i_2306_, v_sz_2305_);
                if v___x_2318_ == 0 {
                    v___x_2319_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2319_, 0, v_b_2307_);
                    return v___x_2319_;
                } else {
                    v_a_2320_ = lean_array_uget_borrowed(v_as_2304_, v_i_2306_);
                    lean_inc(v_a_2320_);
                    v___x_2321_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f(
                            v_a_2320_,
                            v___y_2308_,
                            v___y_2309_,
                            v___y_2310_,
                            v___y_2311_,
                        );
                    if lean_obj_tag(v___x_2321_) == 0 {
                        v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
                        lean_inc(v_a_2322_);
                        lean_dec_ref_known(v___x_2321_, 1);
                        v_fst_2323_ = lean_ctor_get(v_a_2322_, 0);
                        lean_inc(v_fst_2323_);
                        lean_dec(v_a_2322_);
                        if lean_obj_tag(v_fst_2323_) == 1 {
                            v_val_2324_ = lean_ctor_get(v_fst_2323_, 0);
                            lean_inc(v_val_2324_);
                            lean_dec_ref_known(v_fst_2323_, 1);
                            v___x_2325_ = lean_array_push(v_b_2307_, v_val_2324_);
                            v_a_2314_ = v___x_2325_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_fst_2323_);
                            v_a_2314_ = v_b_2307_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_2307_);
                        v_a_2326_ = lean_ctor_get(v___x_2321_, 0);
                        v_isSharedCheck_2333_ = (!lean_is_exclusive(v___x_2321_)) as u8;
                        if v_isSharedCheck_2333_ == 0 {
                            v___x_2328_ = v___x_2321_;
                            v_isShared_2329_ = v_isSharedCheck_2333_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2326_);
                            lean_dec(v___x_2321_);
                            v___x_2328_ = lean_box(0);
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
                    v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
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
    mut v_as_2334_: *mut LeanObject,
    mut v_sz_2335_: *mut LeanObject,
    mut v_i_2336_: *mut LeanObject,
    mut v_b_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2343_: usize = 0;
    let mut v_i_boxed_2344_: usize = 0;
    let mut v_res_2345_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2343_ = lean_unbox_usize(v_sz_2335_);
    lean_dec(v_sz_2335_);
    v_i_boxed_2344_ = lean_unbox_usize(v_i_2336_);
    lean_dec(v_i_2336_);
    v_res_2345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_as_2334_, v_sz_boxed_2343_, v_i_boxed_2344_, v_b_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
    lean_dec(v___y_2341_);
    lean_dec_ref(v___y_2340_);
    lean_dec(v___y_2339_);
    lean_dec_ref(v___y_2338_);
    lean_dec_ref(v_as_2334_);
    return v_res_2345_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0() -> *mut LeanObject {
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: f64 = 0.0;
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    v___x_2346_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__1;
    v___x_2347_ = 1;
    v___x_2348_ = lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_toOption___closed__0);
    v___x_2349_ = lean_box(0);
    v___x_2350_ =
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppStruct_x3f___closed__1;
    v___x_2351_ = lean_alloc_ctor(0, 3, (17) as u32);
    lean_ctor_set(v___x_2351_, 0, v___x_2350_);
    lean_ctor_set(v___x_2351_, 1, v___x_2349_);
    lean_ctor_set(v___x_2351_, 2, v___x_2346_);
    lean_ctor_set_float(
        v___x_2351_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2348_,
    );
    lean_ctor_set_float(
        v___x_2351_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        v___x_2348_,
    );
    lean_ctor_set_uint8(
        v___x_2351_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
        v___x_2347_,
    );
    return v___x_2351_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Lean_Meta_Grind_AC_pp_x3f___closed__2;
    v___x_2356_ = l_Lean_MessageData_ofFormat(v___x_2355_);
    return v___x_2356_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_pp_x3f(
    mut v_goal_2357_: *mut LeanObject,
    mut v_a_2358_: *mut LeanObject,
    mut v_a_2359_: *mut LeanObject,
    mut v_a_2360_: *mut LeanObject,
    mut v_a_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structs_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgs_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2369_: usize = 0;
    let mut v___x_2370_: usize = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2396_: u8 = 0;
    let mut v_a_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2404_: u8 = 0;
    let mut v_a_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v_ref_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2363_ = l_Lean_Meta_Grind_AC_acExt;
                v___x_2364_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_2363_, v_goal_2357_);
                if lean_obj_tag(v___x_2364_) == 0 {
                    v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
                    lean_inc(v_a_2365_);
                    lean_dec_ref_known(v___x_2364_, 1);
                    v_structs_2366_ = lean_ctor_get(v_a_2365_, 0);
                    lean_inc_ref(v_structs_2366_);
                    lean_dec(v_a_2365_);
                    v___x_2367_ = lean_unsigned_to_nat(0);
                    v_msgs_2368_ = l_Lean_toTraceElem___at___00__private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_ppBasis_x3f_spec__1___closed__0;
                    v_sz_2369_ = lean_array_size(v_structs_2366_);
                    v___x_2370_ = 0usize;
                    v___x_2371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_AC_pp_x3f_spec__0(v_structs_2366_, v_sz_2369_, v___x_2370_, v_msgs_2368_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
                    lean_dec_ref(v_structs_2366_);
                    if lean_obj_tag(v___x_2371_) == 0 {
                        v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
                        v_isSharedCheck_2396_ = (!lean_is_exclusive(v___x_2371_)) as u8;
                        if v_isSharedCheck_2396_ == 0 {
                            v___x_2374_ = v___x_2371_;
                            v_isShared_2375_ = v_isSharedCheck_2396_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2372_);
                            lean_dec(v___x_2371_);
                            v___x_2374_ = lean_box(0);
                            v_isShared_2375_ = v_isSharedCheck_2396_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2397_ = lean_ctor_get(v___x_2371_, 0);
                        v_isSharedCheck_2404_ = (!lean_is_exclusive(v___x_2371_)) as u8;
                        if v_isSharedCheck_2404_ == 0 {
                            v___x_2399_ = v___x_2371_;
                            v_isShared_2400_ = v_isSharedCheck_2404_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2397_);
                            lean_dec(v___x_2371_);
                            v___x_2399_ = lean_box(0);
                            v_isShared_2400_ = v_isSharedCheck_2404_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_2405_ = lean_ctor_get(v___x_2364_, 0);
                    v_isSharedCheck_2417_ = (!lean_is_exclusive(v___x_2364_)) as u8;
                    if v_isSharedCheck_2417_ == 0 {
                        v___x_2407_ = v___x_2364_;
                        v_isShared_2408_ = v_isSharedCheck_2417_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2405_);
                        lean_dec(v___x_2364_);
                        v___x_2407_ = lean_box(0);
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
                    v___x_2378_ = lean_unsigned_to_nat(1);
                    v___x_2379_ = lean_nat_dec_eq(v___x_2376_, v___x_2378_);
                    if v___x_2379_ == 0 {
                        v___x_2380_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__0_once),
                            _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__0,
                        );
                        v___x_2381_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_pp_x3f___closed__3_once),
                            _init_l_Lean_Meta_Grind_AC_pp_x3f___closed__3,
                        );
                        v___x_2382_ = lean_alloc_ctor(9, 3, (0) as u32);
                        lean_ctor_set(v___x_2382_, 0, v___x_2380_);
                        lean_ctor_set(v___x_2382_, 1, v___x_2381_);
                        lean_ctor_set(v___x_2382_, 2, v_a_2372_);
                        v___x_2383_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2383_, 0, v___x_2382_);
                        if v_isShared_2375_ == 0 {
                            lean_ctor_set(v___x_2374_, 0, v___x_2383_);
                            v___x_2385_ = v___x_2374_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
                            v___x_2385_ = v_reuseFailAlloc_2386_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2387_ = lean_array_fget(v_a_2372_, v___x_2367_);
                        lean_dec(v_a_2372_);
                        v___x_2388_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2388_, 0, v___x_2387_);
                        if v_isShared_2375_ == 0 {
                            lean_ctor_set(v___x_2374_, 0, v___x_2388_);
                            v___x_2390_ = v___x_2374_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
                            v___x_2390_ = v_reuseFailAlloc_2391_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_2372_);
                    v___x_2392_ = lean_box(0);
                    if v_isShared_2375_ == 0 {
                        lean_ctor_set(v___x_2374_, 0, v___x_2392_);
                        v___x_2394_ = v___x_2374_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
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
                    v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
                    v___x_2402_ = v_reuseFailAlloc_2403_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2402_;
            }
            7 => {
                v_ref_2409_ = lean_ctor_get(v_a_2360_, 5);
                v___x_2410_ = lean_io_error_to_string(v_a_2405_);
                v___x_2411_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2411_, 0, v___x_2410_);
                v___x_2412_ = l_Lean_MessageData_ofFormat(v___x_2411_);
                lean_inc(v_ref_2409_);
                v___x_2413_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2413_, 0, v_ref_2409_);
                lean_ctor_set(v___x_2413_, 1, v___x_2412_);
                if v_isShared_2408_ == 0 {
                    lean_ctor_set(v___x_2407_, 0, v___x_2413_);
                    v___x_2415_ = v___x_2407_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
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
    mut v_goal_2418_: *mut LeanObject,
    mut v_a_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
    mut v_a_2421_: *mut LeanObject,
    mut v_a_2422_: *mut LeanObject,
    mut v_a_2423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2424_: *mut LeanObject = core::ptr::null_mut();
    v_res_2424_ =
        l_Lean_Meta_Grind_AC_pp_x3f(v_goal_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
    lean_dec(v_a_2422_);
    lean_dec_ref(v_a_2421_);
    lean_dec(v_a_2420_);
    lean_dec_ref(v_a_2419_);
    lean_dec_ref(v_goal_2418_);
    return v_res_2424_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM =
        _init_l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM();
    lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_AC_PP_0__Lean_Meta_Grind_AC_instMonadGetStructM,
    );
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_PP(builtin);
}
