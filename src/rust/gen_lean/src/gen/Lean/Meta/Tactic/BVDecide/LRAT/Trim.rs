// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.LRAT.Trim
// Imports: Std.Tactic.BVDecide.LRAT.Actions Init.Data.Nat.Fold Std.Data.HashMap Init.Data.Range.Polymorphic Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_pop, lean_array_push, lean_array_set,
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_byte_array_fget, lean_byte_array_push, lean_byte_array_set, lean_byte_array_size,
    lean_int_dec_eq, lean_int_dec_le, lean_int_neg, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_mk_empty_byte_array, lean_nat_abs, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_nat_to_int, lean_panic_fn_borrowed, lean_uint8_dec_eq, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Int::Basic::l_Int_instInhabited;
use crate::r#gen::Init::Data::Nat::Fold::{
    initialize_Init_Data_Nat_Fold, runtime_initialize_Init_Data_Nat_Fold,
};
use crate::r#gen::Init::Data::Range::Polymorphic::{
    initialize_Init_Data_Range_Polymorphic, runtime_initialize_Init_Data_Range_Polymorphic,
};
use crate::r#gen::Init::Data::UInt::BasicAux::l_UInt64_ofNat___boxed;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqNat___boxed,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
    l_instInhabitedUInt8,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg;
use crate::r#gen::Std::Data::HashMap::{
    initialize_Std_Data_HashMap, runtime_initialize_Std_Data_HashMap,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Actions::{
    initialize_Std_Tactic_BVDecide_LRAT_Actions,
    l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions,
};
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [76, 82, 65, 84, 32, 112, 114, 111, 111, 102, 32, 100, 111, 101, 115, 110, 39, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 97, 32, 112, 114, 111, 112, 101, 114, 32, 102, 105, 114, 115, 116, 32, 112, 114, 111, 111, 102, 32, 115, 116, 101, 112, 46, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__0_value: leanh::LeanStringObject<45> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [76, 82, 65, 84, 32, 112, 114, 111, 111, 102, 32, 100, 111, 101, 115, 110, 39, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 116, 104, 101, 32, 101, 109, 112, 116, 121, 32, 99, 108, 97, 117, 115, 101, 46, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_UInt64_ofNat___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6_value) as *mut leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76, 82, 65, 84, 46, 84, 114, 105, 109, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1_value: leanh::LeanStringObject<93> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 93, m_capacity: 93, m_length: 92, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76, 82, 65, 84, 46, 84, 114, 105, 109, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 66, 86, 68, 101, 99, 105, 100, 101, 46, 76, 82, 65, 84, 46, 116, 114, 105, 109, 46, 77, 46, 109, 97, 112, 83, 116, 101, 112, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__1_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__2_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__3_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId(
    mut v_proof_1677_: *mut leanh::LeanObject,
    mut v_curr_1678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1679_ = lean_array_get_size(v_proof_1677_);
                v___x_1680_ = lean_nat_dec_lt(v_curr_1678_, v___x_1679_);
                if v___x_1680_ == 0 {
                    leanh::lean_dec(v_curr_1678_);
                    v___x_1681_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId___closed__1;
                    return v___x_1681_;
                } else {
                    v___x_1682_ = lean_array_fget_borrowed(v_proof_1677_, v_curr_1678_);
                    if leanh::lean_obj_tag(v___x_1682_) == 3 {
                        v___x_1683_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1684_ = lean_nat_add(v_curr_1678_, v___x_1683_);
                        leanh::lean_dec(v_curr_1678_);
                        v_curr_1678_ = v___x_1684_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_curr_1678_);
                        v_id_1686_ = leanh::lean_ctor_get(v___x_1682_, 0);
                        leanh::lean_inc(v_id_1686_);
                        v___x_1687_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1687_, 0, v_id_1686_);
                        return v___x_1687_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId___boxed(
    mut v_proof_1688_: *mut leanh::LeanObject,
    mut v_curr_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1690_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId(v_proof_1688_, v_curr_1689_);
    leanh::lean_dec_ref(v_proof_1688_);
    return v_res_1690_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(
    mut v_as_1691_: *mut leanh::LeanObject,
    mut v_i_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1694_: u8 = 0;
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1693_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1694_ = lean_nat_dec_eq(v_i_1692_, v_zero_1693_);
                if v_isZero_1694_ == 1 {
                    leanh::lean_dec(v_i_1692_);
                    v___x_1695_ = leanh::lean_box(0);
                    return v___x_1695_;
                } else {
                    v_one_1696_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1697_ = lean_nat_sub(v_i_1692_, v_one_1696_);
                    leanh::lean_dec(v_i_1692_);
                    v___x_1698_ = lean_array_fget_borrowed(v_as_1691_, v_n_1697_);
                    if leanh::lean_obj_tag(v___x_1698_) == 0 {
                        leanh::lean_dec(v_n_1697_);
                        v_id_1699_ = leanh::lean_ctor_get(v___x_1698_, 0);
                        leanh::lean_inc(v_id_1699_);
                        v___x_1700_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1700_, 0, v_id_1699_);
                        return v___x_1700_;
                    } else {
                        v_i_1692_ = v_n_1697_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg___boxed(
    mut v_as_1702_: *mut leanh::LeanObject,
    mut v_i_1703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(v_as_1702_, v_i_1703_);
    leanh::lean_dec_ref(v_as_1702_);
    return v_res_1704_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId(
    mut v_proof_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1715_: u8 = 0;
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1709_ = lean_array_get_size(v_proof_1708_);
                v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(v_proof_1708_, v___x_1709_);
                if leanh::lean_obj_tag(v___x_1710_) == 0 {
                    v___x_1711_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId___closed__1;
                    return v___x_1711_;
                } else {
                    v_val_1712_ = leanh::lean_ctor_get(v___x_1710_, 0);
                    v_isSharedCheck_1719_ = (!leanh::lean_is_exclusive(v___x_1710_)) as u8;
                    if v_isSharedCheck_1719_ == 0 {
                        v___x_1714_ = v___x_1710_;
                        v_isShared_1715_ = v_isSharedCheck_1719_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1712_);
                        leanh::lean_dec(v___x_1710_);
                        v___x_1714_ = leanh::lean_box(0);
                        v_isShared_1715_ = v_isSharedCheck_1719_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1715_ == 0 {
                    v___x_1717_ = v___x_1714_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1718_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_val_1712_);
                    v___x_1717_ = v_reuseFailAlloc_1718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId___boxed(
    mut v_proof_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId(v_proof_1720_);
    leanh::lean_dec_ref(v_proof_1720_);
    return v_res_1721_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0(
    mut v_as_1722_: *mut leanh::LeanObject,
    mut v_i_1723_: *mut leanh::LeanObject,
    mut v_a_1724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___redArg(v_as_1722_, v_i_1723_);
    return v___x_1725_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0___boxed(
    mut v_as_1726_: *mut leanh::LeanObject,
    mut v_i_1727_: *mut leanh::LeanObject,
    mut v_a_1728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1729_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId_spec__0(v_as_1726_, v_i_1727_, v_a_1728_);
    leanh::lean_dec_ref(v_as_1726_);
    return v_res_1729_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_x_1730_: *mut leanh::LeanObject,
    mut v_x_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1737_: u8 = 0;
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: u64 = 0;
    let mut v___x_1740_: u64 = 0;
    let mut v___x_1741_: u64 = 0;
    let mut v_fold_1742_: u64 = 0;
    let mut v___x_1743_: u64 = 0;
    let mut v___x_1744_: u64 = 0;
    let mut v___x_1745_: u64 = 0;
    let mut v___x_1746_: usize = 0;
    let mut v___x_1747_: usize = 0;
    let mut v___x_1748_: usize = 0;
    let mut v___x_1749_: usize = 0;
    let mut v___x_1750_: usize = 0;
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1731_) == 0 {
                    return v_x_1730_;
                } else {
                    v_key_1732_ = leanh::lean_ctor_get(v_x_1731_, 0);
                    v_value_1733_ = leanh::lean_ctor_get(v_x_1731_, 1);
                    v_tail_1734_ = leanh::lean_ctor_get(v_x_1731_, 2);
                    v_isSharedCheck_1757_ = (!leanh::lean_is_exclusive(v_x_1731_)) as u8;
                    if v_isSharedCheck_1757_ == 0 {
                        v___x_1736_ = v_x_1731_;
                        v_isShared_1737_ = v_isSharedCheck_1757_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1734_);
                        leanh::lean_inc(v_value_1733_);
                        leanh::lean_inc(v_key_1732_);
                        leanh::lean_dec(v_x_1731_);
                        v___x_1736_ = leanh::lean_box(0);
                        v_isShared_1737_ = v_isSharedCheck_1757_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1738_ = lean_array_get_size(v_x_1730_);
                v___x_1739_ = lean_uint64_of_nat(v_key_1732_);
                v___x_1740_ = 32u64;
                v___x_1741_ = lean_uint64_shift_right(v___x_1739_, v___x_1740_);
                v_fold_1742_ = lean_uint64_xor(v___x_1739_, v___x_1741_);
                v___x_1743_ = 16u64;
                v___x_1744_ = lean_uint64_shift_right(v_fold_1742_, v___x_1743_);
                v___x_1745_ = lean_uint64_xor(v_fold_1742_, v___x_1744_);
                v___x_1746_ = lean_uint64_to_usize(v___x_1745_);
                v___x_1747_ = lean_usize_of_nat(v___x_1738_);
                v___x_1748_ = 1usize;
                v___x_1749_ = lean_usize_sub(v___x_1747_, v___x_1748_);
                v___x_1750_ = lean_usize_land(v___x_1746_, v___x_1749_);
                v___x_1751_ = lean_array_uget_borrowed(v_x_1730_, v___x_1750_);
                leanh::lean_inc(v___x_1751_);
                if v_isShared_1737_ == 0 {
                    leanh::lean_ctor_set(v___x_1736_, 2, v___x_1751_);
                    v___x_1753_ = v___x_1736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1756_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_key_1732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_value_1733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 2, v___x_1751_);
                    v___x_1753_ = v_reuseFailAlloc_1756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1754_ = lean_array_uset(v_x_1730_, v___x_1750_, v___x_1753_);
                v_x_1730_ = v___x_1754_;
                v_x_1731_ = v_tail_1734_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(
    mut v_i_1758_: *mut leanh::LeanObject,
    mut v_source_1759_: *mut leanh::LeanObject,
    mut v_target_1760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: u8 = 0;
    let mut v_es_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1761_ = lean_array_get_size(v_source_1759_);
                v___x_1762_ = lean_nat_dec_lt(v_i_1758_, v___x_1761_);
                if v___x_1762_ == 0 {
                    leanh::lean_dec_ref(v_source_1759_);
                    leanh::lean_dec(v_i_1758_);
                    return v_target_1760_;
                } else {
                    v_es_1763_ = lean_array_fget(v_source_1759_, v_i_1758_);
                    v___x_1764_ = leanh::lean_box(0);
                    v_source_1765_ = lean_array_fset(v_source_1759_, v_i_1758_, v___x_1764_);
                    v_target_1766_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(v_target_1760_, v_es_1763_);
                    v___x_1767_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1768_ = lean_nat_add(v_i_1758_, v___x_1767_);
                    leanh::lean_dec(v_i_1758_);
                    v_i_1758_ = v___x_1768_;
                    v_source_1759_ = v_source_1765_;
                    v_target_1760_ = v_target_1766_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(
    mut v_data_1770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1771_ = lean_array_get_size(v_data_1770_);
    v___x_1772_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1773_ = lean_nat_mul(v___x_1771_, v___x_1772_);
    v___x_1774_ = leanh::lean_unsigned_to_nat(0);
    v___x_1775_ = leanh::lean_box(0);
    v___x_1776_ = lean_mk_array(v_nbuckets_1773_, v___x_1775_);
    v___x_1777_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(v___x_1774_, v_data_1770_, v___x_1776_);
    return v___x_1777_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(
    mut v_a_1778_: *mut leanh::LeanObject,
    mut v_x_1779_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1780_: u8 = 0;
    let mut v_key_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1779_) == 0 {
                    v___x_1780_ = 0;
                    return v___x_1780_;
                } else {
                    v_key_1781_ = leanh::lean_ctor_get(v_x_1779_, 0);
                    v_tail_1782_ = leanh::lean_ctor_get(v_x_1779_, 2);
                    v___x_1783_ = lean_nat_dec_eq(v_key_1781_, v_a_1778_);
                    if v___x_1783_ == 0 {
                        v_x_1779_ = v_tail_1782_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1783_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg___boxed(
    mut v_a_1785_: *mut leanh::LeanObject,
    mut v_x_1786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1787_: u8 = 0;
    let mut v_r_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1787_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_1785_, v_x_1786_);
    leanh::lean_dec(v_x_1786_);
    leanh::lean_dec(v_a_1785_);
    v_r_1788_ = leanh::lean_box((v_res_1787_) as usize);
    return v_r_1788_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(
    mut v_a_1789_: *mut leanh::LeanObject,
    mut v_b_1790_: *mut leanh::LeanObject,
    mut v_x_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1798_: u8 = 0;
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1791_) == 0 {
                    leanh::lean_dec(v_b_1790_);
                    leanh::lean_dec(v_a_1789_);
                    return v_x_1791_;
                } else {
                    v_key_1792_ = leanh::lean_ctor_get(v_x_1791_, 0);
                    v_value_1793_ = leanh::lean_ctor_get(v_x_1791_, 1);
                    v_tail_1794_ = leanh::lean_ctor_get(v_x_1791_, 2);
                    v_isSharedCheck_1806_ = (!leanh::lean_is_exclusive(v_x_1791_)) as u8;
                    if v_isSharedCheck_1806_ == 0 {
                        v___x_1796_ = v_x_1791_;
                        v_isShared_1797_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1794_);
                        leanh::lean_inc(v_value_1793_);
                        leanh::lean_inc(v_key_1792_);
                        leanh::lean_dec(v_x_1791_);
                        v___x_1796_ = leanh::lean_box(0);
                        v_isShared_1797_ = v_isSharedCheck_1806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1798_ = lean_nat_dec_eq(v_key_1792_, v_a_1789_);
                if v___x_1798_ == 0 {
                    v___x_1799_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(v_a_1789_, v_b_1790_, v_tail_1794_);
                    if v_isShared_1797_ == 0 {
                        leanh::lean_ctor_set(v___x_1796_, 2, v___x_1799_);
                        v___x_1801_ = v___x_1796_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1802_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_key_1792_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_value_1793_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 2, v___x_1799_);
                        v___x_1801_ = v_reuseFailAlloc_1802_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_1793_);
                    leanh::lean_dec(v_key_1792_);
                    if v_isShared_1797_ == 0 {
                        leanh::lean_ctor_set(v___x_1796_, 1, v_b_1790_);
                        leanh::lean_ctor_set(v___x_1796_, 0, v_a_1789_);
                        v___x_1804_ = v___x_1796_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1805_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1789_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_b_1790_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1805_, 2, v_tail_1794_);
                        v___x_1804_ = v_reuseFailAlloc_1805_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1801_;
            }
            3 => {
                return v___x_1804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(
    mut v_m_1807_: *mut leanh::LeanObject,
    mut v_a_1808_: *mut leanh::LeanObject,
    mut v_b_1809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1814_: u8 = 0;
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: u64 = 0;
    let mut v___x_1817_: u64 = 0;
    let mut v___x_1818_: u64 = 0;
    let mut v_fold_1819_: u64 = 0;
    let mut v___x_1820_: u64 = 0;
    let mut v___x_1821_: u64 = 0;
    let mut v___x_1822_: u64 = 0;
    let mut v___x_1823_: usize = 0;
    let mut v___x_1824_: usize = 0;
    let mut v___x_1825_: usize = 0;
    let mut v___x_1826_: usize = 0;
    let mut v___x_1827_: usize = 0;
    let mut v_bkt_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: u8 = 0;
    let mut v_val_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1854_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1810_ = leanh::lean_ctor_get(v_m_1807_, 0);
                v_buckets_1811_ = leanh::lean_ctor_get(v_m_1807_, 1);
                v_isSharedCheck_1854_ = (!leanh::lean_is_exclusive(v_m_1807_)) as u8;
                if v_isSharedCheck_1854_ == 0 {
                    v___x_1813_ = v_m_1807_;
                    v_isShared_1814_ = v_isSharedCheck_1854_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_1811_);
                    leanh::lean_inc(v_size_1810_);
                    leanh::lean_dec(v_m_1807_);
                    v___x_1813_ = leanh::lean_box(0);
                    v_isShared_1814_ = v_isSharedCheck_1854_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1815_ = lean_array_get_size(v_buckets_1811_);
                v___x_1816_ = lean_uint64_of_nat(v_a_1808_);
                v___x_1817_ = 32u64;
                v___x_1818_ = lean_uint64_shift_right(v___x_1816_, v___x_1817_);
                v_fold_1819_ = lean_uint64_xor(v___x_1816_, v___x_1818_);
                v___x_1820_ = 16u64;
                v___x_1821_ = lean_uint64_shift_right(v_fold_1819_, v___x_1820_);
                v___x_1822_ = lean_uint64_xor(v_fold_1819_, v___x_1821_);
                v___x_1823_ = lean_uint64_to_usize(v___x_1822_);
                v___x_1824_ = lean_usize_of_nat(v___x_1815_);
                v___x_1825_ = 1usize;
                v___x_1826_ = lean_usize_sub(v___x_1824_, v___x_1825_);
                v___x_1827_ = lean_usize_land(v___x_1823_, v___x_1826_);
                v_bkt_1828_ = lean_array_uget_borrowed(v_buckets_1811_, v___x_1827_);
                v___x_1829_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_1808_, v_bkt_1828_);
                if v___x_1829_ == 0 {
                    v___x_1830_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1831_ = lean_nat_add(v_size_1810_, v___x_1830_);
                    leanh::lean_dec(v_size_1810_);
                    leanh::lean_inc(v_bkt_1828_);
                    v___x_1832_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1832_, 0, v_a_1808_);
                    leanh::lean_ctor_set(v___x_1832_, 1, v_b_1809_);
                    leanh::lean_ctor_set(v___x_1832_, 2, v_bkt_1828_);
                    v_buckets_x27_1833_ =
                        lean_array_uset(v_buckets_1811_, v___x_1827_, v___x_1832_);
                    v___x_1834_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1835_ = lean_nat_mul(v_size_x27_1831_, v___x_1834_);
                    v___x_1836_ = leanh::lean_unsigned_to_nat(3);
                    v___x_1837_ = lean_nat_div(v___x_1835_, v___x_1836_);
                    leanh::lean_dec(v___x_1835_);
                    v___x_1838_ = lean_array_get_size(v_buckets_x27_1833_);
                    v___x_1839_ = lean_nat_dec_le(v___x_1837_, v___x_1838_);
                    leanh::lean_dec(v___x_1837_);
                    if v___x_1839_ == 0 {
                        v_val_1840_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(v_buckets_x27_1833_);
                        if v_isShared_1814_ == 0 {
                            leanh::lean_ctor_set(v___x_1813_, 1, v_val_1840_);
                            leanh::lean_ctor_set(v___x_1813_, 0, v_size_x27_1831_);
                            v___x_1842_ = v___x_1813_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1843_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1843_,
                                0,
                                v_size_x27_1831_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_val_1840_);
                            v___x_1842_ = v_reuseFailAlloc_1843_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1814_ == 0 {
                            leanh::lean_ctor_set(v___x_1813_, 1, v_buckets_x27_1833_);
                            leanh::lean_ctor_set(v___x_1813_, 0, v_size_x27_1831_);
                            v___x_1845_ = v___x_1813_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1846_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1846_,
                                0,
                                v_size_x27_1831_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_1846_,
                                1,
                                v_buckets_x27_1833_,
                            );
                            v___x_1845_ = v_reuseFailAlloc_1846_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_1828_);
                    v___x_1847_ = leanh::lean_box(0);
                    v_buckets_x27_1848_ =
                        lean_array_uset(v_buckets_1811_, v___x_1827_, v___x_1847_);
                    v___x_1849_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(v_a_1808_, v_b_1809_, v_bkt_1828_);
                    v___x_1850_ = lean_array_uset(v_buckets_x27_1848_, v___x_1827_, v___x_1849_);
                    if v_isShared_1814_ == 0 {
                        leanh::lean_ctor_set(v___x_1813_, 1, v___x_1850_);
                        v___x_1852_ = v___x_1813_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1853_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_size_1810_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1853_, 1, v___x_1850_);
                        v___x_1852_ = v_reuseFailAlloc_1853_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1842_;
            }
            3 => {
                return v___x_1845_;
            }
            4 => {
                return v___x_1852_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__2(
    mut v_as_1855_: *mut leanh::LeanObject,
    mut v_i_1856_: usize,
    mut v_stop_1857_: usize,
    mut v_b_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: usize = 0;
    let mut v___x_1862_: usize = 0;
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1864_ = lean_usize_dec_eq(v_i_1856_, v_stop_1857_);
                if v___x_1864_ == 0 {
                    v___x_1865_ = lean_array_uget_borrowed(v_as_1855_, v_i_1856_);
                    if leanh::lean_obj_tag(v___x_1865_) == 3 {
                        v___y_1860_ = v_b_1858_;
                        state = 1;
                        continue;
                    } else {
                        v_id_1866_ = leanh::lean_ctor_get(v___x_1865_, 0);
                        leanh::lean_inc(v___x_1865_);
                        leanh::lean_inc(v_id_1866_);
                        v___x_1867_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(v_b_1858_, v_id_1866_, v___x_1865_);
                        v___y_1860_ = v___x_1867_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1858_;
                }
            }
            1 => {
                v___x_1861_ = 1usize;
                v___x_1862_ = lean_usize_add(v_i_1856_, v___x_1861_);
                v_i_1856_ = v___x_1862_;
                v_b_1858_ = v___y_1860_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__2___boxed(
    mut v_as_1868_: *mut leanh::LeanObject,
    mut v_i_1869_: *mut leanh::LeanObject,
    mut v_stop_1870_: *mut leanh::LeanObject,
    mut v_b_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1872_: usize = 0;
    let mut v_stop_boxed_1873_: usize = 0;
    let mut v_res_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1872_ = leanh::lean_unbox_usize(v_i_1869_);
    leanh::lean_dec(v_i_1869_);
    v_stop_boxed_1873_ = leanh::lean_unbox_usize(v_stop_1870_);
    leanh::lean_dec(v_stop_1870_);
    v_res_1874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__2(v_as_1868_, v_i_boxed_1872_, v_stop_boxed_1873_, v_b_1871_);
    leanh::lean_dec_ref(v_as_1868_);
    return v_res_1874_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(
    mut v_j_1875_: *mut leanh::LeanObject,
    mut v_a_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1878_: u8 = 0;
    let mut v_one_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1877_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1878_ = lean_nat_dec_eq(v_j_1875_, v_zero_1877_);
                if v_isZero_1878_ == 1 {
                    leanh::lean_dec(v_j_1875_);
                    return v_a_1876_;
                } else {
                    v_one_1879_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1880_ = lean_nat_sub(v_j_1875_, v_one_1879_);
                    leanh::lean_dec(v_j_1875_);
                    v___x_1881_ = 0;
                    v___x_1882_ = lean_byte_array_push(v_a_1876_, v___x_1881_);
                    v_j_1875_ = v_n_1880_;
                    v_a_1876_ = v___x_1882_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1884_ = leanh::lean_unsigned_to_nat(1);
    v___x_1885_ = lean_nat_to_int(v___x_1884_);
    return v___x_1885_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1886_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__0);
    v___x_1887_ = lean_int_neg(v___x_1886_);
    return v___x_1887_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1888_ = leanh::lean_box(0);
    v___x_1889_ = leanh::lean_unsigned_to_nat(16);
    v___x_1890_ = lean_mk_array(v___x_1889_, v___x_1888_);
    return v___x_1890_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__2);
    v___x_1892_ = leanh::lean_unsigned_to_nat(0);
    v___x_1893_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1893_, 0, v___x_1892_);
    leanh::lean_ctor_set(v___x_1893_, 1, v___x_1891_);
    return v___x_1893_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg(
    mut v_proof_1894_: *mut leanh::LeanObject,
    mut v_x_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1905_: u8 = 0;
    let mut v_a_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1915_: u8 = 0;
    let mut v_a_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1919_: u8 = 0;
    let mut v___y_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: u8 = 0;
    let mut v___x_1943_: usize = 0;
    let mut v___x_1944_: usize = 0;
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: usize = 0;
    let mut v___x_1947_: usize = 0;
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1896_ = leanh::lean_unsigned_to_nat(0);
                v___x_1897_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findInitialId(v_proof_1894_, v___x_1896_);
                if leanh::lean_obj_tag(v___x_1897_) == 0 {
                    leanh::lean_dec_ref(v_x_1895_);
                    v_a_1898_ = leanh::lean_ctor_get(v___x_1897_, 0);
                    v_isSharedCheck_1905_ = (!leanh::lean_is_exclusive(v___x_1897_)) as u8;
                    if v_isSharedCheck_1905_ == 0 {
                        v___x_1900_ = v___x_1897_;
                        v_isShared_1901_ = v_isSharedCheck_1905_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1898_);
                        leanh::lean_dec(v___x_1897_);
                        v___x_1900_ = leanh::lean_box(0);
                        v_isShared_1901_ = v_isSharedCheck_1905_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1906_ = leanh::lean_ctor_get(v___x_1897_, 0);
                    leanh::lean_inc(v_a_1906_);
                    leanh::lean_dec_ref_known(v___x_1897_, 1);
                    v___x_1907_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_findEmptyId(v_proof_1894_);
                    if leanh::lean_obj_tag(v___x_1907_) == 0 {
                        leanh::lean_dec(v_a_1906_);
                        leanh::lean_dec_ref(v_x_1895_);
                        v_a_1908_ = leanh::lean_ctor_get(v___x_1907_, 0);
                        v_isSharedCheck_1915_ =
                            (!leanh::lean_is_exclusive(v___x_1907_)) as u8;
                        if v_isSharedCheck_1915_ == 0 {
                            v___x_1910_ = v___x_1907_;
                            v_isShared_1911_ = v_isSharedCheck_1915_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1908_);
                            leanh::lean_dec(v___x_1907_);
                            v___x_1910_ = leanh::lean_box(0);
                            v_isShared_1911_ = v_isSharedCheck_1915_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1916_ = leanh::lean_ctor_get(v___x_1907_, 0);
                        v_isSharedCheck_1949_ =
                            (!leanh::lean_is_exclusive(v___x_1907_)) as u8;
                        if v_isSharedCheck_1949_ == 0 {
                            v___x_1918_ = v___x_1907_;
                            v_isShared_1919_ = v_isSharedCheck_1949_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1916_);
                            leanh::lean_dec(v___x_1907_);
                            v___x_1918_ = leanh::lean_box(0);
                            v_isShared_1919_ = v_isSharedCheck_1949_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1901_ == 0 {
                    v___x_1903_ = v___x_1900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1904_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
                    v___x_1903_ = v_reuseFailAlloc_1904_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1903_;
            }
            3 => {
                if v_isShared_1911_ == 0 {
                    v___x_1913_ = v___x_1910_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
                    v___x_1913_ = v_reuseFailAlloc_1914_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1913_;
            }
            5 => {
                v___x_1939_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3);
                v___x_1940_ = lean_array_get_size(v_proof_1894_);
                v___x_1941_ = lean_nat_dec_lt(v___x_1896_, v___x_1940_);
                if v___x_1941_ == 0 {
                    v___y_1921_ = v___x_1939_;
                    v_size_1922_ = v___x_1896_;
                    state = 6;
                    continue;
                } else {
                    v___x_1942_ = lean_nat_dec_le(v___x_1940_, v___x_1940_);
                    if v___x_1942_ == 0 {
                        if v___x_1941_ == 0 {
                            v___y_1921_ = v___x_1939_;
                            v_size_1922_ = v___x_1896_;
                            state = 6;
                            continue;
                        } else {
                            v___x_1943_ = 0usize;
                            v___x_1944_ = lean_usize_of_nat(v___x_1940_);
                            v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__2(v_proof_1894_, v___x_1943_, v___x_1944_, v___x_1939_);
                            v___y_1937_ = v___x_1945_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_1946_ = 0usize;
                        v___x_1947_ = lean_usize_of_nat(v___x_1940_);
                        v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__2(v_proof_1894_, v___x_1946_, v___x_1947_, v___x_1939_);
                        v___y_1937_ = v___x_1948_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1923_ = lean_mk_empty_byte_array(v_size_1922_);
                leanh::lean_inc(v_size_1922_);
                v___x_1924_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(v_size_1922_, v___x_1923_);
                v___x_1925_ = lean_nat_add(v_a_1906_, v_size_1922_);
                v___x_1926_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1);
                v___x_1927_ = lean_mk_array(v___x_1925_, v___x_1926_);
                v___x_1928_ = lean_mk_array(v_size_1922_, v___x_1896_);
                v___x_1929_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1929_, 0, v___y_1921_);
                leanh::lean_ctor_set(v___x_1929_, 1, v_a_1906_);
                leanh::lean_ctor_set(v___x_1929_, 2, v_a_1916_);
                v___x_1930_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1930_, 0, v___x_1924_);
                leanh::lean_ctor_set(v___x_1930_, 1, v___x_1928_);
                leanh::lean_ctor_set(v___x_1930_, 2, v___x_1927_);
                v___x_1931_ = leanh::lean_apply_2(v_x_1895_, v___x_1929_, v___x_1930_);
                v_fst_1932_ = leanh::lean_ctor_get(v___x_1931_, 0);
                leanh::lean_inc(v_fst_1932_);
                leanh::lean_dec_ref(v___x_1931_);
                if v_isShared_1919_ == 0 {
                    leanh::lean_ctor_set(v___x_1918_, 0, v_fst_1932_);
                    v___x_1934_ = v___x_1918_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1935_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_fst_1932_);
                    v___x_1934_ = v_reuseFailAlloc_1935_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1934_;
            }
            8 => {
                v_size_1938_ = leanh::lean_ctor_get(v___y_1937_, 0);
                leanh::lean_inc(v_size_1938_);
                v___y_1921_ = v___y_1937_;
                v_size_1922_ = v_size_1938_;
                state = 6;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___boxed(
    mut v_proof_1950_: *mut leanh::LeanObject,
    mut v_x_1951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1952_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg(v_proof_1950_, v_x_1951_);
    leanh::lean_dec_ref(v_proof_1950_);
    return v_res_1952_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run(
    mut v_00_u03b1_1953_: *mut leanh::LeanObject,
    mut v_proof_1954_: *mut leanh::LeanObject,
    mut v_x_1955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1956_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg(v_proof_1954_, v_x_1955_);
    return v___x_1956_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___boxed(
    mut v_00_u03b1_1957_: *mut leanh::LeanObject,
    mut v_proof_1958_: *mut leanh::LeanObject,
    mut v_x_1959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run(v_00_u03b1_1957_, v_proof_1958_, v_x_1959_);
    leanh::lean_dec_ref(v_proof_1958_);
    return v_res_1960_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0(
    mut v_00_u03b2_1961_: *mut leanh::LeanObject,
    mut v_m_1962_: *mut leanh::LeanObject,
    mut v_a_1963_: *mut leanh::LeanObject,
    mut v_b_1964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0___redArg(v_m_1962_, v_a_1963_, v_b_1964_);
    return v___x_1965_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__1(
    mut v_n_1966_: *mut leanh::LeanObject,
    mut v_j_1967_: *mut leanh::LeanObject,
    mut v_a_1968_: *mut leanh::LeanObject,
    mut v_a_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1970_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__1___redArg(v_j_1967_, v_a_1969_);
    return v___x_1970_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__1___boxed(
    mut v_n_1971_: *mut leanh::LeanObject,
    mut v_j_1972_: *mut leanh::LeanObject,
    mut v_a_1973_: *mut leanh::LeanObject,
    mut v_a_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__1(v_n_1971_, v_j_1972_, v_a_1973_, v_a_1974_);
    leanh::lean_dec(v_n_1971_);
    return v_res_1975_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0(
    mut v_00_u03b2_1976_: *mut leanh::LeanObject,
    mut v_a_1977_: *mut leanh::LeanObject,
    mut v_x_1978_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1979_: u8 = 0;
    v___x_1979_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_1977_, v_x_1978_);
    return v___x_1979_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___boxed(
    mut v_00_u03b2_1980_: *mut leanh::LeanObject,
    mut v_a_1981_: *mut leanh::LeanObject,
    mut v_x_1982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1983_: u8 = 0;
    let mut v_r_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1983_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0(v_00_u03b2_1980_, v_a_1981_, v_x_1982_);
    leanh::lean_dec(v_x_1982_);
    leanh::lean_dec(v_a_1981_);
    v_r_1984_ = leanh::lean_box((v_res_1983_) as usize);
    return v_r_1984_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1(
    mut v_00_u03b2_1985_: *mut leanh::LeanObject,
    mut v_data_1986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1987_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(v_data_1986_);
    return v___x_1987_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2(
    mut v_00_u03b2_1988_: *mut leanh::LeanObject,
    mut v_a_1989_: *mut leanh::LeanObject,
    mut v_b_1990_: *mut leanh::LeanObject,
    mut v_x_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1992_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__2___redArg(v_a_1989_, v_b_1990_, v_x_1991_);
    return v___x_1992_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1993_: *mut leanh::LeanObject,
    mut v_i_1994_: *mut leanh::LeanObject,
    mut v_source_1995_: *mut leanh::LeanObject,
    mut v_target_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1997_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2___redArg(v_i_1994_, v_source_1995_, v_target_1996_);
    return v___x_1997_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b2_1998_: *mut leanh::LeanObject,
    mut v_x_1999_: *mut leanh::LeanObject,
    mut v_x_2000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1_spec__2_spec__5___redArg(v_x_1999_, v_x_2000_);
    return v___x_2001_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getInitialId(
    mut v_a_2002_: *mut leanh::LeanObject,
    mut v_a_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_initialId_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_initialId_2004_ = leanh::lean_ctor_get(v_a_2002_, 1);
    leanh::lean_inc(v_initialId_2004_);
    v___x_2005_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2005_, 0, v_initialId_2004_);
    leanh::lean_ctor_set(v___x_2005_, 1, v_a_2003_);
    return v___x_2005_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getInitialId___boxed(
    mut v_a_2006_: *mut leanh::LeanObject,
    mut v_a_2007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2008_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getInitialId(v_a_2006_, v_a_2007_);
    leanh::lean_dec_ref(v_a_2006_);
    return v_res_2008_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getEmptyId(
    mut v_a_2009_: *mut leanh::LeanObject,
    mut v_a_2010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_addEmptyId_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_addEmptyId_2011_ = leanh::lean_ctor_get(v_a_2009_, 2);
    leanh::lean_inc(v_addEmptyId_2011_);
    v___x_2012_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2012_, 0, v_addEmptyId_2011_);
    leanh::lean_ctor_set(v___x_2012_, 1, v_a_2010_);
    return v___x_2012_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getEmptyId___boxed(
    mut v_a_2013_: *mut leanh::LeanObject,
    mut v_a_2014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2015_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getEmptyId(v_a_2013_, v_a_2014_);
    leanh::lean_dec_ref(v_a_2013_);
    return v_res_2015_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_idIndex(
    mut v_id_2016_: *mut leanh::LeanObject,
    mut v_a_2017_: *mut leanh::LeanObject,
    mut v_a_2018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_initialId_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_initialId_2019_ = leanh::lean_ctor_get(v_a_2017_, 1);
    v___x_2020_ = lean_nat_sub(v_id_2016_, v_initialId_2019_);
    v___x_2021_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2021_, 0, v___x_2020_);
    leanh::lean_ctor_set(v___x_2021_, 1, v_a_2018_);
    return v___x_2021_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_idIndex___boxed(
    mut v_id_2022_: *mut leanh::LeanObject,
    mut v_a_2023_: *mut leanh::LeanObject,
    mut v_a_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2025_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_idIndex(v_id_2022_, v_a_2023_, v_a_2024_);
    leanh::lean_dec_ref(v_a_2023_);
    leanh::lean_dec(v_id_2022_);
    return v_res_2025_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2027_ = leanh::lean_alloc_closure(
        l_instDecidableEqNat___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_2028_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2028_, 0, v___x_2027_);
    return v___f_2028_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep(
    mut v_id_2029_: *mut leanh::LeanObject,
    mut v_a_2030_: *mut leanh::LeanObject,
    mut v_a_2031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_proof_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_proof_2032_ = leanh::lean_ctor_get(v_a_2030_, 0);
    v___f_2033_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__0;
    v___f_2034_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___closed__1);
    v___x_2035_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
        v___f_2034_,
        v___f_2033_,
        v_proof_2032_,
        v_id_2029_,
    );
    v___x_2036_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2036_, 0, v___x_2035_);
    leanh::lean_ctor_set(v___x_2036_, 1, v_a_2031_);
    return v___x_2036_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep___boxed(
    mut v_id_2037_: *mut leanh::LeanObject,
    mut v_a_2038_: *mut leanh::LeanObject,
    mut v_a_2039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2040_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_getProofStep(v_id_2037_, v_a_2038_, v_a_2039_);
    leanh::lean_dec_ref(v_a_2038_);
    return v_res_2040_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_isUsed(
    mut v_id_2041_: *mut leanh::LeanObject,
    mut v_a_2042_: *mut leanh::LeanObject,
    mut v_a_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2045_: u8 = 0;
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2047_: u8 = 0;
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialId_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v___x_2059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_initialId_2050_ = leanh::lean_ctor_get(v_a_2042_, 1);
                v_used_2051_ = leanh::lean_ctor_get(v_a_2043_, 0);
                v___x_2052_ = lean_nat_sub(v_id_2041_, v_initialId_2050_);
                v___x_2053_ = lean_byte_array_size(v_used_2051_);
                v___x_2054_ = lean_nat_dec_lt(v___x_2052_, v___x_2053_);
                if v___x_2054_ == 0 {
                    leanh::lean_dec(v___x_2052_);
                    v___x_2055_ = l_instInhabitedUInt8;
                    v___x_2056_ = leanh::lean_box((v___x_2055_) as usize);
                    v___x_2057_ = l_outOfBounds___redArg(v___x_2056_);
                    leanh::lean_dec(v___x_2056_);
                    v___x_2058_ = (leanh::lean_unbox(v___x_2057_) as u8);
                    leanh::lean_dec(v___x_2057_);
                    v___y_2045_ = v___x_2058_;
                    state = 1;
                    continue;
                } else {
                    v___x_2059_ = lean_byte_array_fget(v_used_2051_, v___x_2052_);
                    leanh::lean_dec(v___x_2052_);
                    v___y_2045_ = v___x_2059_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2046_ = 1;
                v___x_2047_ = lean_uint8_dec_eq(v___y_2045_, v___x_2046_);
                v___x_2048_ = leanh::lean_box((v___x_2047_) as usize);
                v___x_2049_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2049_, 0, v___x_2048_);
                leanh::lean_ctor_set(v___x_2049_, 1, v_a_2043_);
                return v___x_2049_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_isUsed___boxed(
    mut v_id_2060_: *mut leanh::LeanObject,
    mut v_a_2061_: *mut leanh::LeanObject,
    mut v_a_2062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2063_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_isUsed(v_id_2060_, v_a_2061_, v_a_2062_);
    leanh::lean_dec_ref(v_a_2061_);
    leanh::lean_dec(v_id_2060_);
    return v_res_2063_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_markUsed(
    mut v_id_2064_: *mut leanh::LeanObject,
    mut v_a_2065_: *mut leanh::LeanObject,
    mut v_a_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_initialId_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapped_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2076_: u8 = 0;
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_initialId_2067_ = leanh::lean_ctor_get(v_a_2065_, 1);
                v___x_2068_ = lean_nat_dec_le(v_initialId_2067_, v_id_2064_);
                if v___x_2068_ == 0 {
                    v___x_2069_ = leanh::lean_box(0);
                    v___x_2070_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2070_, 0, v___x_2069_);
                    leanh::lean_ctor_set(v___x_2070_, 1, v_a_2066_);
                    return v___x_2070_;
                } else {
                    v_used_2071_ = leanh::lean_ctor_get(v_a_2066_, 0);
                    v_mapped_2072_ = leanh::lean_ctor_get(v_a_2066_, 1);
                    v_lastUse_2073_ = leanh::lean_ctor_get(v_a_2066_, 2);
                    v_isSharedCheck_2085_ = (!leanh::lean_is_exclusive(v_a_2066_)) as u8;
                    if v_isSharedCheck_2085_ == 0 {
                        v___x_2075_ = v_a_2066_;
                        v_isShared_2076_ = v_isSharedCheck_2085_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_lastUse_2073_);
                        leanh::lean_inc(v_mapped_2072_);
                        leanh::lean_inc(v_used_2071_);
                        leanh::lean_dec(v_a_2066_);
                        v___x_2075_ = leanh::lean_box(0);
                        v_isShared_2076_ = v_isSharedCheck_2085_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2077_ = lean_nat_sub(v_id_2064_, v_initialId_2067_);
                v___x_2078_ = leanh::lean_box(0);
                v___x_2079_ = 1;
                v___x_2080_ = lean_byte_array_set(v_used_2071_, v___x_2077_, v___x_2079_);
                leanh::lean_dec(v___x_2077_);
                if v_isShared_2076_ == 0 {
                    leanh::lean_ctor_set(v___x_2075_, 0, v___x_2080_);
                    v___x_2082_ = v___x_2075_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2084_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_mapped_2072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_lastUse_2073_);
                    v___x_2082_ = v_reuseFailAlloc_2084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2083_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2083_, 0, v___x_2078_);
                leanh::lean_ctor_set(v___x_2083_, 1, v___x_2082_);
                return v___x_2083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_markUsed___boxed(
    mut v_id_2086_: *mut leanh::LeanObject,
    mut v_a_2087_: *mut leanh::LeanObject,
    mut v_a_2088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2089_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_markUsed(v_id_2086_, v_a_2087_, v_a_2088_);
    leanh::lean_dec_ref(v_a_2087_);
    leanh::lean_dec(v_id_2086_);
    return v_res_2089_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_registerIdMap(
    mut v_oldId_2090_: *mut leanh::LeanObject,
    mut v_newId_2091_: *mut leanh::LeanObject,
    mut v_a_2092_: *mut leanh::LeanObject,
    mut v_a_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_initialId_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapped_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2100_: u8 = 0;
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_initialId_2094_ = leanh::lean_ctor_get(v_a_2092_, 1);
                v_used_2095_ = leanh::lean_ctor_get(v_a_2093_, 0);
                v_mapped_2096_ = leanh::lean_ctor_get(v_a_2093_, 1);
                v_lastUse_2097_ = leanh::lean_ctor_get(v_a_2093_, 2);
                v_isSharedCheck_2108_ = (!leanh::lean_is_exclusive(v_a_2093_)) as u8;
                if v_isSharedCheck_2108_ == 0 {
                    v___x_2099_ = v_a_2093_;
                    v_isShared_2100_ = v_isSharedCheck_2108_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_lastUse_2097_);
                    leanh::lean_inc(v_mapped_2096_);
                    leanh::lean_inc(v_used_2095_);
                    leanh::lean_dec(v_a_2093_);
                    v___x_2099_ = leanh::lean_box(0);
                    v_isShared_2100_ = v_isSharedCheck_2108_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2101_ = lean_nat_sub(v_oldId_2090_, v_initialId_2094_);
                v___x_2102_ = leanh::lean_box(0);
                v___x_2103_ = lean_array_set(v_mapped_2096_, v___x_2101_, v_newId_2091_);
                leanh::lean_dec(v___x_2101_);
                if v_isShared_2100_ == 0 {
                    leanh::lean_ctor_set(v___x_2099_, 1, v___x_2103_);
                    v___x_2105_ = v___x_2099_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2107_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_used_2095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2103_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_lastUse_2097_);
                    v___x_2105_ = v_reuseFailAlloc_2107_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2106_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2106_, 0, v___x_2102_);
                leanh::lean_ctor_set(v___x_2106_, 1, v___x_2105_);
                return v___x_2106_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_registerIdMap___boxed(
    mut v_oldId_2109_: *mut leanh::LeanObject,
    mut v_newId_2110_: *mut leanh::LeanObject,
    mut v_a_2111_: *mut leanh::LeanObject,
    mut v_a_2112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2113_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_registerIdMap(v_oldId_2109_, v_newId_2110_, v_a_2111_, v_a_2112_);
    leanh::lean_dec_ref(v_a_2111_);
    leanh::lean_dec(v_oldId_2109_);
    return v_res_2113_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg(
    mut v_hint_2114_: *mut leanh::LeanObject,
    mut v_user_2115_: *mut leanh::LeanObject,
    mut v_a_2116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_used_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapped_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prev_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_used_2117_ = leanh::lean_ctor_get(v_a_2116_, 0);
                v_mapped_2118_ = leanh::lean_ctor_get(v_a_2116_, 1);
                v_lastUse_2119_ = leanh::lean_ctor_get(v_a_2116_, 2);
                v_isSharedCheck_2135_ = (!leanh::lean_is_exclusive(v_a_2116_)) as u8;
                if v_isSharedCheck_2135_ == 0 {
                    v___x_2121_ = v_a_2116_;
                    v_isShared_2122_ = v_isSharedCheck_2135_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_lastUse_2119_);
                    leanh::lean_inc(v_mapped_2118_);
                    leanh::lean_inc(v_used_2117_);
                    leanh::lean_dec(v_a_2116_);
                    v___x_2121_ = leanh::lean_box(0);
                    v_isShared_2122_ = v_isSharedCheck_2135_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2123_ = l_Int_instInhabited;
                v___x_2124_ = leanh::lean_box(0);
                v_prev_2132_ = lean_array_get_borrowed(v___x_2123_, v_lastUse_2119_, v_hint_2114_);
                v___x_2133_ = lean_nat_to_int(v_user_2115_);
                v___x_2134_ = lean_int_dec_le(v_prev_2132_, v___x_2133_);
                if v___x_2134_ == 0 {
                    leanh::lean_dec(v___x_2133_);
                    leanh::lean_inc(v_prev_2132_);
                    v___y_2126_ = v_prev_2132_;
                    state = 2;
                    continue;
                } else {
                    v___y_2126_ = v___x_2133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2127_ = lean_array_set(v_lastUse_2119_, v_hint_2114_, v___y_2126_);
                if v_isShared_2122_ == 0 {
                    leanh::lean_ctor_set(v___x_2121_, 2, v___x_2127_);
                    v___x_2129_ = v___x_2121_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2131_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_used_2117_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_mapped_2118_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 2, v___x_2127_);
                    v___x_2129_ = v_reuseFailAlloc_2131_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2130_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2130_, 0, v___x_2124_);
                leanh::lean_ctor_set(v___x_2130_, 1, v___x_2129_);
                return v___x_2130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg___boxed(
    mut v_hint_2136_: *mut leanh::LeanObject,
    mut v_user_2137_: *mut leanh::LeanObject,
    mut v_a_2138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2139_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_updateLastUse___redArg(v_hint_2136_, v_user_2137_, v_a_2138_);
    leanh::lean_dec(v_hint_2136_);
    return v_res_2139_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_updateLastUse(
    mut v_hint_2140_: *mut leanh::LeanObject,
    mut v_user_2141_: *mut leanh::LeanObject,
    mut v_a_2142_: *mut leanh::LeanObject,
    mut v_a_2143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_used_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapped_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2149_: u8 = 0;
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prev_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: u8 = 0;
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_used_2144_ = leanh::lean_ctor_get(v_a_2143_, 0);
                v_mapped_2145_ = leanh::lean_ctor_get(v_a_2143_, 1);
                v_lastUse_2146_ = leanh::lean_ctor_get(v_a_2143_, 2);
                v_isSharedCheck_2162_ = (!leanh::lean_is_exclusive(v_a_2143_)) as u8;
                if v_isSharedCheck_2162_ == 0 {
                    v___x_2148_ = v_a_2143_;
                    v_isShared_2149_ = v_isSharedCheck_2162_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_lastUse_2146_);
                    leanh::lean_inc(v_mapped_2145_);
                    leanh::lean_inc(v_used_2144_);
                    leanh::lean_dec(v_a_2143_);
                    v___x_2148_ = leanh::lean_box(0);
                    v_isShared_2149_ = v_isSharedCheck_2162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2150_ = l_Int_instInhabited;
                v___x_2151_ = leanh::lean_box(0);
                v_prev_2159_ = lean_array_get_borrowed(v___x_2150_, v_lastUse_2146_, v_hint_2140_);
                v___x_2160_ = lean_nat_to_int(v_user_2141_);
                v___x_2161_ = lean_int_dec_le(v_prev_2159_, v___x_2160_);
                if v___x_2161_ == 0 {
                    leanh::lean_dec(v___x_2160_);
                    leanh::lean_inc(v_prev_2159_);
                    v___y_2153_ = v_prev_2159_;
                    state = 2;
                    continue;
                } else {
                    v___y_2153_ = v___x_2160_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2154_ = lean_array_set(v_lastUse_2146_, v_hint_2140_, v___y_2153_);
                if v_isShared_2149_ == 0 {
                    leanh::lean_ctor_set(v___x_2148_, 2, v___x_2154_);
                    v___x_2156_ = v___x_2148_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2158_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_used_2144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_mapped_2145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2158_, 2, v___x_2154_);
                    v___x_2156_ = v_reuseFailAlloc_2158_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2157_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2157_, 0, v___x_2151_);
                leanh::lean_ctor_set(v___x_2157_, 1, v___x_2156_);
                return v___x_2157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_updateLastUse___boxed(
    mut v_hint_2163_: *mut leanh::LeanObject,
    mut v_user_2164_: *mut leanh::LeanObject,
    mut v_a_2165_: *mut leanh::LeanObject,
    mut v_a_2166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_updateLastUse(v_hint_2163_, v_user_2164_, v_a_2165_, v_a_2166_);
    leanh::lean_dec_ref(v_a_2165_);
    leanh::lean_dec(v_hint_2163_);
    return v_res_2167_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapIdent(
    mut v_ident_2168_: *mut leanh::LeanObject,
    mut v_a_2169_: *mut leanh::LeanObject,
    mut v_a_2170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_initialId_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: u8 = 0;
    v_initialId_2171_ = leanh::lean_ctor_get(v_a_2169_, 1);
    v___x_2172_ = lean_nat_dec_lt(v_ident_2168_, v_initialId_2171_);
    if v___x_2172_ == 0 {
        let mut v_mapped_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_mapped_2173_ = leanh::lean_ctor_get(v_a_2170_, 1);
        v___x_2174_ = lean_nat_sub(v_ident_2168_, v_initialId_2171_);
        leanh::lean_dec(v_ident_2168_);
        v___x_2175_ = leanh::lean_unsigned_to_nat(0);
        v___x_2176_ = lean_array_get(v___x_2175_, v_mapped_2173_, v___x_2174_);
        leanh::lean_dec(v___x_2174_);
        v___x_2177_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2177_, 0, v___x_2176_);
        leanh::lean_ctor_set(v___x_2177_, 1, v_a_2170_);
        return v___x_2177_;
    } else {
        let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2178_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2178_, 0, v_ident_2168_);
        leanh::lean_ctor_set(v___x_2178_, 1, v_a_2170_);
        return v___x_2178_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapIdent___boxed(
    mut v_ident_2179_: *mut leanh::LeanObject,
    mut v_a_2180_: *mut leanh::LeanObject,
    mut v_a_2181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2182_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapIdent(v_ident_2179_, v_a_2180_, v_a_2181_);
    leanh::lean_dec_ref(v_a_2180_);
    return v_res_2182_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2190_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(
    mut v_msg_2191_: *mut leanh::LeanObject,
    mut v___y_2192_: *mut leanh::LeanObject,
    mut v___y_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260__overap_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2194_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__0;
    v___f_2195_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__1;
    v___f_2196_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__2;
    v___f_2197_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__3;
    v___f_2198_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__4;
    v___f_2199_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__5;
    v___f_2200_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__6;
    v___x_2201_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2201_, 0, v___f_2194_);
    leanh::lean_ctor_set(v___x_2201_, 1, v___f_2195_);
    v___x_2202_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2202_, 0, v___x_2201_);
    leanh::lean_ctor_set(v___x_2202_, 1, v___f_2196_);
    leanh::lean_ctor_set(v___x_2202_, 2, v___f_2197_);
    leanh::lean_ctor_set(v___x_2202_, 3, v___f_2198_);
    leanh::lean_ctor_set(v___x_2202_, 4, v___f_2199_);
    v___x_2203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2203_, 0, v___x_2202_);
    leanh::lean_ctor_set(v___x_2203_, 1, v___f_2200_);
    leanh::lean_inc_ref_n(v___x_2203_, 6);
    v___f_2204_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2204_, 0, v___x_2203_);
    v___f_2205_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2205_, 0, v___x_2203_);
    v___f_2206_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2206_, 0, v___x_2203_);
    v___f_2207_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2207_, 0, v___x_2203_);
    v___x_2208_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_2208_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2208_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2208_, 2, v___x_2203_);
    v___x_2209_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2209_, 0, v___x_2208_);
    leanh::lean_ctor_set(v___x_2209_, 1, v___f_2204_);
    v___x_2210_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_2210_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2210_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2210_, 2, v___x_2203_);
    v___x_2211_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2211_, 0, v___x_2209_);
    leanh::lean_ctor_set(v___x_2211_, 1, v___x_2210_);
    leanh::lean_ctor_set(v___x_2211_, 2, v___f_2205_);
    leanh::lean_ctor_set(v___x_2211_, 3, v___f_2206_);
    leanh::lean_ctor_set(v___x_2211_, 4, v___f_2207_);
    v___x_2212_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_2212_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2212_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2212_, 2, v___x_2203_);
    v___x_2213_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2213_, 0, v___x_2211_);
    leanh::lean_ctor_set(v___x_2213_, 1, v___x_2212_);
    v___x_2214_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7);
    v___x_2215_ = l_instInhabitedOfMonad___redArg(v___x_2213_, v___x_2214_);
    v___f_2216_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2216_, 0, v___x_2215_);
    v___x_4260__overap_2217_ = lean_panic_fn_borrowed(v___f_2216_, v_msg_2191_);
    leanh::lean_dec_ref(v___f_2216_);
    leanh::lean_inc_ref(v___y_2192_);
    v___x_2218_ = leanh::lean_apply_2(v___x_4260__overap_2217_, v___y_2192_, v___y_2193_);
    return v___x_2218_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___boxed(
    mut v_msg_2219_: *mut leanh::LeanObject,
    mut v___y_2220_: *mut leanh::LeanObject,
    mut v___y_2221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2222_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(v_msg_2219_, v___y_2220_, v___y_2221_);
    leanh::lean_dec_ref(v___y_2220_);
    return v_res_2222_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(
    mut v_sz_2223_: usize,
    mut v_i_2224_: usize,
    mut v_bs_2225_: *mut leanh::LeanObject,
    mut v___y_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2228_: u8 = 0;
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialId_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: usize = 0;
    let mut v___x_2238_: usize = 0;
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v_mapped_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2228_ = lean_usize_dec_lt(v_i_2224_, v_sz_2223_);
                if v___x_2228_ == 0 {
                    v___x_2229_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2229_, 0, v_bs_2225_);
                    leanh::lean_ctor_set(v___x_2229_, 1, v___y_2227_);
                    return v___x_2229_;
                } else {
                    v_initialId_2230_ = leanh::lean_ctor_get(v___y_2226_, 1);
                    v_v_2231_ = lean_array_uget(v_bs_2225_, v_i_2224_);
                    v___x_2232_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2233_ = lean_array_uset(v_bs_2225_, v_i_2224_, v___x_2232_);
                    v___x_2241_ = lean_nat_dec_lt(v_v_2231_, v_initialId_2230_);
                    if v___x_2241_ == 0 {
                        v_mapped_2242_ = leanh::lean_ctor_get(v___y_2227_, 1);
                        v___x_2243_ = lean_nat_sub(v_v_2231_, v_initialId_2230_);
                        leanh::lean_dec(v_v_2231_);
                        v___x_2244_ = lean_array_get(v___x_2232_, v_mapped_2242_, v___x_2243_);
                        leanh::lean_dec(v___x_2243_);
                        v_fst_2235_ = v___x_2244_;
                        v_snd_2236_ = v___y_2227_;
                        state = 1;
                        continue;
                    } else {
                        v_fst_2235_ = v_v_2231_;
                        v_snd_2236_ = v___y_2227_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2237_ = 1usize;
                v___x_2238_ = lean_usize_add(v_i_2224_, v___x_2237_);
                v___x_2239_ = lean_array_uset(v_bs_x27_2233_, v_i_2224_, v_fst_2235_);
                v_i_2224_ = v___x_2238_;
                v_bs_2225_ = v___x_2239_;
                v___y_2227_ = v_snd_2236_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0___boxed(
    mut v_sz_2245_: *mut leanh::LeanObject,
    mut v_i_2246_: *mut leanh::LeanObject,
    mut v_bs_2247_: *mut leanh::LeanObject,
    mut v___y_2248_: *mut leanh::LeanObject,
    mut v___y_2249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2250_: usize = 0;
    let mut v_i_boxed_2251_: usize = 0;
    let mut v_res_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2250_ = leanh::lean_unbox_usize(v_sz_2245_);
    leanh::lean_dec(v_sz_2245_);
    v_i_boxed_2251_ = leanh::lean_unbox_usize(v_i_2246_);
    leanh::lean_dec(v_i_2246_);
    v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_boxed_2250_, v_i_boxed_2251_, v_bs_2247_, v___y_2248_, v___y_2249_);
    leanh::lean_dec_ref(v___y_2248_);
    return v_res_2252_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(
    mut v_sz_2253_: usize,
    mut v_i_2254_: usize,
    mut v_bs_2255_: *mut leanh::LeanObject,
    mut v___y_2256_: *mut leanh::LeanObject,
    mut v___y_2257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2258_: u8 = 0;
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialId_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2269_: usize = 0;
    let mut v___x_2270_: usize = 0;
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2276_: u8 = 0;
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: usize = 0;
    let mut v___x_2280_: usize = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut v___x_2285_: u8 = 0;
    let mut v_mapped_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2258_ = lean_usize_dec_lt(v_i_2254_, v_sz_2253_);
                if v___x_2258_ == 0 {
                    v___x_2259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2259_, 0, v_bs_2255_);
                    leanh::lean_ctor_set(v___x_2259_, 1, v___y_2257_);
                    return v___x_2259_;
                } else {
                    v_v_2260_ = lean_array_uget(v_bs_2255_, v_i_2254_);
                    v_fst_2261_ = leanh::lean_ctor_get(v_v_2260_, 0);
                    v_initialId_2262_ = leanh::lean_ctor_get(v___y_2256_, 1);
                    v___x_2263_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2264_ = lean_array_uset(v_bs_2255_, v_i_2254_, v___x_2263_);
                    v___x_2285_ = lean_nat_dec_lt(v_fst_2261_, v_initialId_2262_);
                    if v___x_2285_ == 0 {
                        v_mapped_2286_ = leanh::lean_ctor_get(v___y_2257_, 1);
                        v___x_2287_ = lean_nat_sub(v_fst_2261_, v_initialId_2262_);
                        v___x_2288_ = lean_array_get(v___x_2263_, v_mapped_2286_, v___x_2287_);
                        leanh::lean_dec(v___x_2287_);
                        v_fst_2266_ = v___x_2288_;
                        v_snd_2267_ = v___y_2257_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2261_);
                        v_fst_2266_ = v_fst_2261_;
                        v_snd_2267_ = v___y_2257_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2268_ = leanh::lean_ctor_get(v_v_2260_, 1);
                leanh::lean_inc(v_snd_2268_);
                leanh::lean_dec(v_v_2260_);
                v_sz_2269_ = lean_array_size(v_snd_2268_);
                v___x_2270_ = 0usize;
                v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_2269_, v___x_2270_, v_snd_2268_, v___y_2256_, v_snd_2267_);
                v_fst_2272_ = leanh::lean_ctor_get(v___x_2271_, 0);
                v_snd_2273_ = leanh::lean_ctor_get(v___x_2271_, 1);
                v_isSharedCheck_2284_ = (!leanh::lean_is_exclusive(v___x_2271_)) as u8;
                if v_isSharedCheck_2284_ == 0 {
                    v___x_2275_ = v___x_2271_;
                    v_isShared_2276_ = v_isSharedCheck_2284_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2273_);
                    leanh::lean_inc(v_fst_2272_);
                    leanh::lean_dec(v___x_2271_);
                    v___x_2275_ = leanh::lean_box(0);
                    v_isShared_2276_ = v_isSharedCheck_2284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2276_ == 0 {
                    leanh::lean_ctor_set(v___x_2275_, 1, v_fst_2272_);
                    leanh::lean_ctor_set(v___x_2275_, 0, v_fst_2266_);
                    v___x_2278_ = v___x_2275_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2283_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_fst_2266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_fst_2272_);
                    v___x_2278_ = v_reuseFailAlloc_2283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2279_ = 1usize;
                v___x_2280_ = lean_usize_add(v_i_2254_, v___x_2279_);
                v___x_2281_ = lean_array_uset(v_bs_x27_2264_, v_i_2254_, v___x_2278_);
                v_i_2254_ = v___x_2280_;
                v_bs_2255_ = v___x_2281_;
                v___y_2257_ = v_snd_2273_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1___boxed(
    mut v_sz_2289_: *mut leanh::LeanObject,
    mut v_i_2290_: *mut leanh::LeanObject,
    mut v_bs_2291_: *mut leanh::LeanObject,
    mut v___y_2292_: *mut leanh::LeanObject,
    mut v___y_2293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2294_: usize = 0;
    let mut v_i_boxed_2295_: usize = 0;
    let mut v_res_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2294_ = leanh::lean_unbox_usize(v_sz_2289_);
    leanh::lean_dec(v_sz_2289_);
    v_i_boxed_2295_ = leanh::lean_unbox_usize(v_i_2290_);
    leanh::lean_dec(v_i_2290_);
    v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(v_sz_boxed_2294_, v_i_boxed_2295_, v_bs_2291_, v___y_2292_, v___y_2293_);
    leanh::lean_dec_ref(v___y_2292_);
    return v_res_2296_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__2;
    v___x_2301_ = leanh::lean_unsigned_to_nat(15);
    v___x_2302_ = leanh::lean_unsigned_to_nat(164);
    v___x_2303_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__1;
    v___x_2304_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__0;
    v___x_2305_ = l_mkPanicMessageWithDecl(
        v___x_2304_,
        v___x_2303_,
        v___x_2302_,
        v___x_2301_,
        v___x_2300_,
    );
    return v___x_2305_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep(
    mut v_step_2306_: *mut leanh::LeanObject,
    mut v_a_2307_: *mut leanh::LeanObject,
    mut v_a_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v_fst_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2317_: usize = 0;
    let mut v___x_2318_: usize = 0;
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v_initialId_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: u8 = 0;
    let mut v_mapped_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2338_: u8 = 0;
    let mut v_id_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2344_: u8 = 0;
    let mut v_fst_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2348_: usize = 0;
    let mut v___x_2349_: usize = 0;
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2362_: u8 = 0;
    let mut v_initialId_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: u8 = 0;
    let mut v_mapped_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2369_: u8 = 0;
    let mut v_id_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratHints_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2377_: u8 = 0;
    let mut v_fst_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2381_: usize = 0;
    let mut v___x_2382_: usize = 0;
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2386_: usize = 0;
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2399_: u8 = 0;
    let mut v_initialId_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: u8 = 0;
    let mut v_mapped_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_step_2306_) {
                0 => {
                    v_id_2309_ = leanh::lean_ctor_get(v_step_2306_, 0);
                    v_rupHints_2310_ = leanh::lean_ctor_get(v_step_2306_, 1);
                    v_isSharedCheck_2338_ = (!leanh::lean_is_exclusive(v_step_2306_)) as u8;
                    if v_isSharedCheck_2338_ == 0 {
                        v___x_2312_ = v_step_2306_;
                        v_isShared_2313_ = v_isSharedCheck_2338_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_rupHints_2310_);
                        leanh::lean_inc(v_id_2309_);
                        leanh::lean_dec(v_step_2306_);
                        v___x_2312_ = leanh::lean_box(0);
                        v_isShared_2313_ = v_isSharedCheck_2338_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_id_2339_ = leanh::lean_ctor_get(v_step_2306_, 0);
                    v_c_2340_ = leanh::lean_ctor_get(v_step_2306_, 1);
                    v_rupHints_2341_ = leanh::lean_ctor_get(v_step_2306_, 2);
                    v_isSharedCheck_2369_ = (!leanh::lean_is_exclusive(v_step_2306_)) as u8;
                    if v_isSharedCheck_2369_ == 0 {
                        v___x_2343_ = v_step_2306_;
                        v_isShared_2344_ = v_isSharedCheck_2369_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_rupHints_2341_);
                        leanh::lean_inc(v_c_2340_);
                        leanh::lean_inc(v_id_2339_);
                        leanh::lean_dec(v_step_2306_);
                        v___x_2343_ = leanh::lean_box(0);
                        v_isShared_2344_ = v_isSharedCheck_2369_;
                        state = 6;
                        continue;
                    }
                }
                2 => {
                    v_id_2370_ = leanh::lean_ctor_get(v_step_2306_, 0);
                    v_c_2371_ = leanh::lean_ctor_get(v_step_2306_, 1);
                    v_pivot_2372_ = leanh::lean_ctor_get(v_step_2306_, 2);
                    v_rupHints_2373_ = leanh::lean_ctor_get(v_step_2306_, 3);
                    v_ratHints_2374_ = leanh::lean_ctor_get(v_step_2306_, 4);
                    v_isSharedCheck_2406_ = (!leanh::lean_is_exclusive(v_step_2306_)) as u8;
                    if v_isSharedCheck_2406_ == 0 {
                        v___x_2376_ = v_step_2306_;
                        v_isShared_2377_ = v_isSharedCheck_2406_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_ratHints_2374_);
                        leanh::lean_inc(v_rupHints_2373_);
                        leanh::lean_inc(v_pivot_2372_);
                        leanh::lean_inc(v_c_2371_);
                        leanh::lean_inc(v_id_2370_);
                        leanh::lean_dec(v_step_2306_);
                        v___x_2376_ = leanh::lean_box(0);
                        v_isShared_2377_ = v_isSharedCheck_2406_;
                        state = 11;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec_ref_known(v_step_2306_, 1);
                    v___x_2407_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___closed__3);
                    v___x_2408_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2(v___x_2407_, v_a_2307_, v_a_2308_);
                    return v___x_2408_;
                }
            },
            1 => {
                v_initialId_2332_ = leanh::lean_ctor_get(v_a_2307_, 1);
                v___x_2333_ = lean_nat_dec_lt(v_id_2309_, v_initialId_2332_);
                if v___x_2333_ == 0 {
                    v_mapped_2334_ = leanh::lean_ctor_get(v_a_2308_, 1);
                    v___x_2335_ = lean_nat_sub(v_id_2309_, v_initialId_2332_);
                    leanh::lean_dec(v_id_2309_);
                    v___x_2336_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2337_ = lean_array_get(v___x_2336_, v_mapped_2334_, v___x_2335_);
                    leanh::lean_dec(v___x_2335_);
                    v_fst_2315_ = v___x_2337_;
                    v_snd_2316_ = v_a_2308_;
                    state = 2;
                    continue;
                } else {
                    v_fst_2315_ = v_id_2309_;
                    v_snd_2316_ = v_a_2308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_2317_ = lean_array_size(v_rupHints_2310_);
                v___x_2318_ = 0usize;
                v___x_2319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_2317_, v___x_2318_, v_rupHints_2310_, v_a_2307_, v_snd_2316_);
                v_fst_2320_ = leanh::lean_ctor_get(v___x_2319_, 0);
                v_snd_2321_ = leanh::lean_ctor_get(v___x_2319_, 1);
                v_isSharedCheck_2331_ = (!leanh::lean_is_exclusive(v___x_2319_)) as u8;
                if v_isSharedCheck_2331_ == 0 {
                    v___x_2323_ = v___x_2319_;
                    v_isShared_2324_ = v_isSharedCheck_2331_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2321_);
                    leanh::lean_inc(v_fst_2320_);
                    leanh::lean_dec(v___x_2319_);
                    v___x_2323_ = leanh::lean_box(0);
                    v_isShared_2324_ = v_isSharedCheck_2331_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2313_ == 0 {
                    leanh::lean_ctor_set(v___x_2312_, 1, v_fst_2320_);
                    leanh::lean_ctor_set(v___x_2312_, 0, v_fst_2315_);
                    v___x_2326_ = v___x_2312_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fst_2315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_fst_2320_);
                    v___x_2326_ = v_reuseFailAlloc_2330_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2324_ == 0 {
                    leanh::lean_ctor_set(v___x_2323_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2323_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_snd_2321_);
                    v___x_2328_ = v_reuseFailAlloc_2329_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2328_;
            }
            6 => {
                v_initialId_2363_ = leanh::lean_ctor_get(v_a_2307_, 1);
                v___x_2364_ = lean_nat_dec_lt(v_id_2339_, v_initialId_2363_);
                if v___x_2364_ == 0 {
                    v_mapped_2365_ = leanh::lean_ctor_get(v_a_2308_, 1);
                    v___x_2366_ = lean_nat_sub(v_id_2339_, v_initialId_2363_);
                    leanh::lean_dec(v_id_2339_);
                    v___x_2367_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2368_ = lean_array_get(v___x_2367_, v_mapped_2365_, v___x_2366_);
                    leanh::lean_dec(v___x_2366_);
                    v_fst_2346_ = v___x_2368_;
                    v_snd_2347_ = v_a_2308_;
                    state = 7;
                    continue;
                } else {
                    v_fst_2346_ = v_id_2339_;
                    v_snd_2347_ = v_a_2308_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_sz_2348_ = lean_array_size(v_rupHints_2341_);
                v___x_2349_ = 0usize;
                v___x_2350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_2348_, v___x_2349_, v_rupHints_2341_, v_a_2307_, v_snd_2347_);
                v_fst_2351_ = leanh::lean_ctor_get(v___x_2350_, 0);
                v_snd_2352_ = leanh::lean_ctor_get(v___x_2350_, 1);
                v_isSharedCheck_2362_ = (!leanh::lean_is_exclusive(v___x_2350_)) as u8;
                if v_isSharedCheck_2362_ == 0 {
                    v___x_2354_ = v___x_2350_;
                    v_isShared_2355_ = v_isSharedCheck_2362_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2352_);
                    leanh::lean_inc(v_fst_2351_);
                    leanh::lean_dec(v___x_2350_);
                    v___x_2354_ = leanh::lean_box(0);
                    v_isShared_2355_ = v_isSharedCheck_2362_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2344_ == 0 {
                    leanh::lean_ctor_set(v___x_2343_, 2, v_fst_2351_);
                    leanh::lean_ctor_set(v___x_2343_, 0, v_fst_2346_);
                    v___x_2357_ = v___x_2343_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2361_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_fst_2346_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_c_2340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 2, v_fst_2351_);
                    v___x_2357_ = v_reuseFailAlloc_2361_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2355_ == 0 {
                    leanh::lean_ctor_set(v___x_2354_, 0, v___x_2357_);
                    v___x_2359_ = v___x_2354_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_snd_2352_);
                    v___x_2359_ = v_reuseFailAlloc_2360_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2359_;
            }
            11 => {
                v_initialId_2400_ = leanh::lean_ctor_get(v_a_2307_, 1);
                v___x_2401_ = lean_nat_dec_lt(v_id_2370_, v_initialId_2400_);
                if v___x_2401_ == 0 {
                    v_mapped_2402_ = leanh::lean_ctor_get(v_a_2308_, 1);
                    v___x_2403_ = lean_nat_sub(v_id_2370_, v_initialId_2400_);
                    leanh::lean_dec(v_id_2370_);
                    v___x_2404_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2405_ = lean_array_get(v___x_2404_, v_mapped_2402_, v___x_2403_);
                    leanh::lean_dec(v___x_2403_);
                    v_fst_2379_ = v___x_2405_;
                    v_snd_2380_ = v_a_2308_;
                    state = 12;
                    continue;
                } else {
                    v_fst_2379_ = v_id_2370_;
                    v_snd_2380_ = v_a_2308_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_sz_2381_ = lean_array_size(v_rupHints_2373_);
                v___x_2382_ = 0usize;
                v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_2381_, v___x_2382_, v_rupHints_2373_, v_a_2307_, v_snd_2380_);
                v_fst_2384_ = leanh::lean_ctor_get(v___x_2383_, 0);
                leanh::lean_inc(v_fst_2384_);
                v_snd_2385_ = leanh::lean_ctor_get(v___x_2383_, 1);
                leanh::lean_inc(v_snd_2385_);
                leanh::lean_dec_ref(v___x_2383_);
                v_sz_2386_ = lean_array_size(v_ratHints_2374_);
                v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__1(v_sz_2386_, v___x_2382_, v_ratHints_2374_, v_a_2307_, v_snd_2385_);
                v_fst_2388_ = leanh::lean_ctor_get(v___x_2387_, 0);
                v_snd_2389_ = leanh::lean_ctor_get(v___x_2387_, 1);
                v_isSharedCheck_2399_ = (!leanh::lean_is_exclusive(v___x_2387_)) as u8;
                if v_isSharedCheck_2399_ == 0 {
                    v___x_2391_ = v___x_2387_;
                    v_isShared_2392_ = v_isSharedCheck_2399_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2389_);
                    leanh::lean_inc(v_fst_2388_);
                    leanh::lean_dec(v___x_2387_);
                    v___x_2391_ = leanh::lean_box(0);
                    v_isShared_2392_ = v_isSharedCheck_2399_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2377_ == 0 {
                    leanh::lean_ctor_set(v___x_2376_, 4, v_fst_2388_);
                    leanh::lean_ctor_set(v___x_2376_, 3, v_fst_2384_);
                    leanh::lean_ctor_set(v___x_2376_, 0, v_fst_2379_);
                    v___x_2394_ = v___x_2376_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = leanh::lean_alloc_ctor(2, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_fst_2379_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_c_2371_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_pivot_2372_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 3, v_fst_2384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 4, v_fst_2388_);
                    v___x_2394_ = v_reuseFailAlloc_2398_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2392_ == 0 {
                    leanh::lean_ctor_set(v___x_2391_, 0, v___x_2394_);
                    v___x_2396_ = v___x_2391_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2397_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_snd_2389_);
                    v___x_2396_ = v_reuseFailAlloc_2397_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep___boxed(
    mut v_step_2409_: *mut leanh::LeanObject,
    mut v_a_2410_: *mut leanh::LeanObject,
    mut v_a_2411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep(v_step_2409_, v_a_2410_, v_a_2411_);
    leanh::lean_dec_ref(v_a_2410_);
    return v_res_2412_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__0(
    mut v_a_2413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = lean_nat_to_int(v_a_2413_);
    return v___x_2414_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(
    mut v_a_2415_: *mut leanh::LeanObject,
    mut v_x_2416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2416_) == 0 {
                    v___x_2417_ = leanh::lean_box(0);
                    return v___x_2417_;
                } else {
                    v_key_2418_ = leanh::lean_ctor_get(v_x_2416_, 0);
                    v_value_2419_ = leanh::lean_ctor_get(v_x_2416_, 1);
                    v_tail_2420_ = leanh::lean_ctor_get(v_x_2416_, 2);
                    v___x_2421_ = lean_nat_dec_eq(v_key_2418_, v_a_2415_);
                    if v___x_2421_ == 0 {
                        v_x_2416_ = v_tail_2420_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_2419_);
                        v___x_2423_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2423_, 0, v_value_2419_);
                        return v___x_2423_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg___boxed(
    mut v_a_2424_: *mut leanh::LeanObject,
    mut v_x_2425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2426_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(v_a_2424_, v_x_2425_);
    leanh::lean_dec(v_x_2425_);
    leanh::lean_dec(v_a_2424_);
    return v_res_2426_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(
    mut v_m_2427_: *mut leanh::LeanObject,
    mut v_a_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: u64 = 0;
    let mut v___x_2432_: u64 = 0;
    let mut v___x_2433_: u64 = 0;
    let mut v_fold_2434_: u64 = 0;
    let mut v___x_2435_: u64 = 0;
    let mut v___x_2436_: u64 = 0;
    let mut v___x_2437_: u64 = 0;
    let mut v___x_2438_: usize = 0;
    let mut v___x_2439_: usize = 0;
    let mut v___x_2440_: usize = 0;
    let mut v___x_2441_: usize = 0;
    let mut v___x_2442_: usize = 0;
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2429_ = leanh::lean_ctor_get(v_m_2427_, 1);
    v___x_2430_ = lean_array_get_size(v_buckets_2429_);
    v___x_2431_ = lean_uint64_of_nat(v_a_2428_);
    v___x_2432_ = 32u64;
    v___x_2433_ = lean_uint64_shift_right(v___x_2431_, v___x_2432_);
    v_fold_2434_ = lean_uint64_xor(v___x_2431_, v___x_2433_);
    v___x_2435_ = 16u64;
    v___x_2436_ = lean_uint64_shift_right(v_fold_2434_, v___x_2435_);
    v___x_2437_ = lean_uint64_xor(v_fold_2434_, v___x_2436_);
    v___x_2438_ = lean_uint64_to_usize(v___x_2437_);
    v___x_2439_ = lean_usize_of_nat(v___x_2430_);
    v___x_2440_ = 1usize;
    v___x_2441_ = lean_usize_sub(v___x_2439_, v___x_2440_);
    v___x_2442_ = lean_usize_land(v___x_2438_, v___x_2441_);
    v___x_2443_ = lean_array_uget_borrowed(v_buckets_2429_, v___x_2442_);
    v___x_2444_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(v_a_2428_, v___x_2443_);
    return v___x_2444_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg___boxed(
    mut v_m_2445_: *mut leanh::LeanObject,
    mut v_a_2446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2447_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_m_2445_, v_a_2446_);
    leanh::lean_dec(v_a_2446_);
    leanh::lean_dec_ref(v_m_2445_);
    return v_res_2447_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(
    mut v_id_2448_: *mut leanh::LeanObject,
    mut v_as_2449_: *mut leanh::LeanObject,
    mut v_i_2450_: usize,
    mut v_stop_2451_: usize,
    mut v_b_2452_: *mut leanh::LeanObject,
    mut v___y_2453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2454_: u8 = 0;
    let mut v_used_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapped_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2460_: u8 = 0;
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: usize = 0;
    let mut v___x_2470_: usize = 0;
    let mut v_reuseFailAlloc_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prev_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: u8 = 0;
    let mut v_isSharedCheck_2476_: u8 = 0;
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2454_ = lean_usize_dec_eq(v_i_2450_, v_stop_2451_);
                if v___x_2454_ == 0 {
                    v_used_2455_ = leanh::lean_ctor_get(v___y_2453_, 0);
                    v_mapped_2456_ = leanh::lean_ctor_get(v___y_2453_, 1);
                    v_lastUse_2457_ = leanh::lean_ctor_get(v___y_2453_, 2);
                    v_isSharedCheck_2476_ = (!leanh::lean_is_exclusive(v___y_2453_)) as u8;
                    if v_isSharedCheck_2476_ == 0 {
                        v___x_2459_ = v___y_2453_;
                        v_isShared_2460_ = v_isSharedCheck_2476_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_lastUse_2457_);
                        leanh::lean_inc(v_mapped_2456_);
                        leanh::lean_inc(v_used_2455_);
                        leanh::lean_dec(v___y_2453_);
                        v___x_2459_ = leanh::lean_box(0);
                        v_isShared_2460_ = v_isSharedCheck_2476_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_id_2448_);
                    v___x_2477_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2477_, 0, v_b_2452_);
                    leanh::lean_ctor_set(v___x_2477_, 1, v___y_2453_);
                    return v___x_2477_;
                }
            }
            1 => {
                v___x_2461_ = lean_array_uget_borrowed(v_as_2449_, v_i_2450_);
                v___x_2462_ = l_Int_instInhabited;
                v___x_2463_ = leanh::lean_box(0);
                v_prev_2473_ = lean_array_get_borrowed(v___x_2462_, v_lastUse_2457_, v___x_2461_);
                leanh::lean_inc(v_id_2448_);
                v___x_2474_ = lean_nat_to_int(v_id_2448_);
                v___x_2475_ = lean_int_dec_le(v_prev_2473_, v___x_2474_);
                if v___x_2475_ == 0 {
                    leanh::lean_dec(v___x_2474_);
                    leanh::lean_inc(v_prev_2473_);
                    v___y_2465_ = v_prev_2473_;
                    state = 2;
                    continue;
                } else {
                    v___y_2465_ = v___x_2474_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2466_ = lean_array_set(v_lastUse_2457_, v___x_2461_, v___y_2465_);
                if v_isShared_2460_ == 0 {
                    leanh::lean_ctor_set(v___x_2459_, 2, v___x_2466_);
                    v___x_2468_ = v___x_2459_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2472_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_used_2455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_mapped_2456_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 2, v___x_2466_);
                    v___x_2468_ = v_reuseFailAlloc_2472_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2469_ = 1usize;
                v___x_2470_ = lean_usize_add(v_i_2450_, v___x_2469_);
                v_i_2450_ = v___x_2470_;
                v_b_2452_ = v___x_2463_;
                v___y_2453_ = v___x_2468_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg___boxed(
    mut v_id_2478_: *mut leanh::LeanObject,
    mut v_as_2479_: *mut leanh::LeanObject,
    mut v_i_2480_: *mut leanh::LeanObject,
    mut v_stop_2481_: *mut leanh::LeanObject,
    mut v_b_2482_: *mut leanh::LeanObject,
    mut v___y_2483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2484_: usize = 0;
    let mut v_stop_boxed_2485_: usize = 0;
    let mut v_res_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2484_ = leanh::lean_unbox_usize(v_i_2480_);
    leanh::lean_dec(v_i_2480_);
    v_stop_boxed_2485_ = leanh::lean_unbox_usize(v_stop_2481_);
    leanh::lean_dec(v_stop_2481_);
    v_res_2486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_2478_, v_as_2479_, v_i_boxed_2484_, v_stop_boxed_2485_, v_b_2482_, v___y_2483_);
    leanh::lean_dec_ref(v_as_2479_);
    return v_res_2486_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(
    mut v_id_2487_: *mut leanh::LeanObject,
    mut v_as_2488_: *mut leanh::LeanObject,
    mut v_i_2489_: usize,
    mut v_stop_2490_: usize,
    mut v_b_2491_: *mut leanh::LeanObject,
    mut v___y_2492_: *mut leanh::LeanObject,
    mut v___y_2493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2494_: u8 = 0;
    let mut v_used_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapped_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2500_: u8 = 0;
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: usize = 0;
    let mut v___x_2510_: usize = 0;
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prev_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: u8 = 0;
    let mut v_isSharedCheck_2516_: u8 = 0;
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2494_ = lean_usize_dec_eq(v_i_2489_, v_stop_2490_);
                if v___x_2494_ == 0 {
                    v_used_2495_ = leanh::lean_ctor_get(v___y_2493_, 0);
                    v_mapped_2496_ = leanh::lean_ctor_get(v___y_2493_, 1);
                    v_lastUse_2497_ = leanh::lean_ctor_get(v___y_2493_, 2);
                    v_isSharedCheck_2516_ = (!leanh::lean_is_exclusive(v___y_2493_)) as u8;
                    if v_isSharedCheck_2516_ == 0 {
                        v___x_2499_ = v___y_2493_;
                        v_isShared_2500_ = v_isSharedCheck_2516_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_lastUse_2497_);
                        leanh::lean_inc(v_mapped_2496_);
                        leanh::lean_inc(v_used_2495_);
                        leanh::lean_dec(v___y_2493_);
                        v___x_2499_ = leanh::lean_box(0);
                        v_isShared_2500_ = v_isSharedCheck_2516_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_id_2487_);
                    v___x_2517_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2517_, 0, v_b_2491_);
                    leanh::lean_ctor_set(v___x_2517_, 1, v___y_2493_);
                    return v___x_2517_;
                }
            }
            1 => {
                v___x_2501_ = lean_array_uget_borrowed(v_as_2488_, v_i_2489_);
                v___x_2502_ = l_Int_instInhabited;
                v___x_2503_ = leanh::lean_box(0);
                v_prev_2513_ = lean_array_get_borrowed(v___x_2502_, v_lastUse_2497_, v___x_2501_);
                leanh::lean_inc(v_id_2487_);
                v___x_2514_ = lean_nat_to_int(v_id_2487_);
                v___x_2515_ = lean_int_dec_le(v_prev_2513_, v___x_2514_);
                if v___x_2515_ == 0 {
                    leanh::lean_dec(v___x_2514_);
                    leanh::lean_inc(v_prev_2513_);
                    v___y_2505_ = v_prev_2513_;
                    state = 2;
                    continue;
                } else {
                    v___y_2505_ = v___x_2514_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2506_ = lean_array_set(v_lastUse_2497_, v___x_2501_, v___y_2505_);
                if v_isShared_2500_ == 0 {
                    leanh::lean_ctor_set(v___x_2499_, 2, v___x_2506_);
                    v___x_2508_ = v___x_2499_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2512_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_used_2495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_mapped_2496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2512_, 2, v___x_2506_);
                    v___x_2508_ = v_reuseFailAlloc_2512_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2509_ = 1usize;
                v___x_2510_ = lean_usize_add(v_i_2489_, v___x_2509_);
                v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_2487_, v_as_2488_, v___x_2510_, v_stop_2490_, v___x_2503_, v___x_2508_);
                return v___x_2511_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4___boxed(
    mut v_id_2518_: *mut leanh::LeanObject,
    mut v_as_2519_: *mut leanh::LeanObject,
    mut v_i_2520_: *mut leanh::LeanObject,
    mut v_stop_2521_: *mut leanh::LeanObject,
    mut v_b_2522_: *mut leanh::LeanObject,
    mut v___y_2523_: *mut leanh::LeanObject,
    mut v___y_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2525_: usize = 0;
    let mut v_stop_boxed_2526_: usize = 0;
    let mut v_res_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2525_ = leanh::lean_unbox_usize(v_i_2520_);
    leanh::lean_dec(v_i_2520_);
    v_stop_boxed_2526_ = leanh::lean_unbox_usize(v_stop_2521_);
    leanh::lean_dec(v_stop_2521_);
    v_res_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_2518_, v_as_2519_, v_i_boxed_2525_, v_stop_boxed_2526_, v_b_2522_, v___y_2523_, v___y_2524_);
    leanh::lean_dec_ref(v___y_2523_);
    leanh::lean_dec_ref(v_as_2519_);
    return v_res_2527_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(
    mut v_as_2528_: *mut leanh::LeanObject,
    mut v_i_2529_: usize,
    mut v_stop_2530_: usize,
    mut v_b_2531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2532_: u8 = 0;
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: usize = 0;
    let mut v___x_2539_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2532_ = lean_usize_dec_eq(v_i_2529_, v_stop_2530_);
                if v___x_2532_ == 0 {
                    v___x_2533_ = lean_array_uget_borrowed(v_as_2528_, v_i_2529_);
                    v_fst_2534_ = leanh::lean_ctor_get(v___x_2533_, 0);
                    v_snd_2535_ = leanh::lean_ctor_get(v___x_2533_, 1);
                    leanh::lean_inc(v_fst_2534_);
                    v___x_2536_ = lean_array_push(v_b_2531_, v_fst_2534_);
                    v___x_2537_ = l_Array_append___redArg(v___x_2536_, v_snd_2535_);
                    v___x_2538_ = 1usize;
                    v___x_2539_ = lean_usize_add(v_i_2529_, v___x_2538_);
                    v_i_2529_ = v___x_2539_;
                    v_b_2531_ = v___x_2537_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2531_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5___boxed(
    mut v_as_2541_: *mut leanh::LeanObject,
    mut v_i_2542_: *mut leanh::LeanObject,
    mut v_stop_2543_: *mut leanh::LeanObject,
    mut v_b_2544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2545_: usize = 0;
    let mut v_stop_boxed_2546_: usize = 0;
    let mut v_res_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2545_ = leanh::lean_unbox_usize(v_i_2542_);
    leanh::lean_dec(v_i_2542_);
    v_stop_boxed_2546_ = leanh::lean_unbox_usize(v_stop_2543_);
    leanh::lean_dec(v_stop_2543_);
    v_res_2547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(v_as_2541_, v_i_boxed_2545_, v_stop_boxed_2546_, v_b_2544_);
    leanh::lean_dec_ref(v_as_2541_);
    return v_res_2547_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(
    mut v_id_2548_: *mut leanh::LeanObject,
    mut v_as_2549_: *mut leanh::LeanObject,
    mut v_sz_2550_: usize,
    mut v_i_2551_: usize,
    mut v_b_2552_: *mut leanh::LeanObject,
    mut v___y_2553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapped_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2561_: u8 = 0;
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: usize = 0;
    let mut v___x_2570_: usize = 0;
    let mut v_reuseFailAlloc_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prev_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u8 = 0;
    let mut v_isSharedCheck_2577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2554_ = lean_usize_dec_lt(v_i_2551_, v_sz_2550_);
                if v___x_2554_ == 0 {
                    leanh::lean_dec(v_id_2548_);
                    v___x_2555_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2555_, 0, v_b_2552_);
                    leanh::lean_ctor_set(v___x_2555_, 1, v___y_2553_);
                    return v___x_2555_;
                } else {
                    v_used_2556_ = leanh::lean_ctor_get(v___y_2553_, 0);
                    v_mapped_2557_ = leanh::lean_ctor_get(v___y_2553_, 1);
                    v_lastUse_2558_ = leanh::lean_ctor_get(v___y_2553_, 2);
                    v_isSharedCheck_2577_ = (!leanh::lean_is_exclusive(v___y_2553_)) as u8;
                    if v_isSharedCheck_2577_ == 0 {
                        v___x_2560_ = v___y_2553_;
                        v_isShared_2561_ = v_isSharedCheck_2577_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_lastUse_2558_);
                        leanh::lean_inc(v_mapped_2557_);
                        leanh::lean_inc(v_used_2556_);
                        leanh::lean_dec(v___y_2553_);
                        v___x_2560_ = leanh::lean_box(0);
                        v_isShared_2561_ = v_isSharedCheck_2577_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2562_ = leanh::lean_box(0);
                v_a_2563_ = lean_array_uget_borrowed(v_as_2549_, v_i_2551_);
                v___x_2573_ = l_Int_instInhabited;
                v_prev_2574_ = lean_array_get_borrowed(v___x_2573_, v_lastUse_2558_, v_a_2563_);
                leanh::lean_inc(v_id_2548_);
                v___x_2575_ = lean_nat_to_int(v_id_2548_);
                v___x_2576_ = lean_int_dec_le(v_prev_2574_, v___x_2575_);
                if v___x_2576_ == 0 {
                    leanh::lean_dec(v___x_2575_);
                    leanh::lean_inc(v_prev_2574_);
                    v___y_2565_ = v_prev_2574_;
                    state = 2;
                    continue;
                } else {
                    v___y_2565_ = v___x_2575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2566_ = lean_array_set(v_lastUse_2558_, v_a_2563_, v___y_2565_);
                if v_isShared_2561_ == 0 {
                    leanh::lean_ctor_set(v___x_2560_, 2, v___x_2566_);
                    v___x_2568_ = v___x_2560_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2572_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_used_2556_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_mapped_2557_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 2, v___x_2566_);
                    v___x_2568_ = v_reuseFailAlloc_2572_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2569_ = 1usize;
                v___x_2570_ = lean_usize_add(v_i_2551_, v___x_2569_);
                v_i_2551_ = v___x_2570_;
                v_b_2552_ = v___x_2562_;
                v___y_2553_ = v___x_2568_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg___boxed(
    mut v_id_2578_: *mut leanh::LeanObject,
    mut v_as_2579_: *mut leanh::LeanObject,
    mut v_sz_2580_: *mut leanh::LeanObject,
    mut v_i_2581_: *mut leanh::LeanObject,
    mut v_b_2582_: *mut leanh::LeanObject,
    mut v___y_2583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2584_: usize = 0;
    let mut v_i_boxed_2585_: usize = 0;
    let mut v_res_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2584_ = leanh::lean_unbox_usize(v_sz_2580_);
    leanh::lean_dec(v_sz_2580_);
    v_i_boxed_2585_ = leanh::lean_unbox_usize(v_i_2581_);
    leanh::lean_dec(v_i_2581_);
    v_res_2586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(v_id_2578_, v_as_2579_, v_sz_boxed_2584_, v_i_boxed_2585_, v_b_2582_, v___y_2583_);
    leanh::lean_dec_ref(v_as_2579_);
    return v_res_2586_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go(
    mut v_worklist_2587_: *mut leanh::LeanObject,
    mut v_a_2588_: *mut leanh::LeanObject,
    mut v_a_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: u8 = 0;
    let mut v_proof_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialId_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapped_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_worklist_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2635_: usize = 0;
    let mut v___y_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: u8 = 0;
    let mut v___x_2640_: u8 = 0;
    let mut v___x_2641_: usize = 0;
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: usize = 0;
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2650_: usize = 0;
    let mut v___x_2651_: usize = 0;
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: u8 = 0;
    let mut v___x_2657_: u8 = 0;
    let mut v___x_2658_: usize = 0;
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: usize = 0;
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: u8 = 0;
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: u8 = 0;
    let mut v___x_2677_: usize = 0;
    let mut v___x_2678_: usize = 0;
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: usize = 0;
    let mut v___x_2681_: usize = 0;
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: u8 = 0;
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: usize = 0;
    let mut v___x_2689_: usize = 0;
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: usize = 0;
    let mut v___x_2692_: usize = 0;
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratHints_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: u8 = 0;
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: usize = 0;
    let mut v___x_2701_: usize = 0;
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: usize = 0;
    let mut v___x_2704_: usize = 0;
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2708_: u8 = 0;
    let mut v___x_2709_: u8 = 0;
    let mut v___x_2710_: u8 = 0;
    let mut v___x_2711_: u8 = 0;
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2714_: u8 = 0;
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2720_: u8 = 0;
    let mut v_unused_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: u8 = 0;
    let mut v___x_2728_: u8 = 0;
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: u8 = 0;
    let mut v___x_2732_: u8 = 0;
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2590_ = lean_array_get_size(v_worklist_2587_);
                v___x_2591_ = leanh::lean_unsigned_to_nat(0);
                v___x_2592_ = lean_nat_dec_eq(v___x_2590_, v___x_2591_);
                if v___x_2592_ == 0 {
                    v_proof_2593_ = leanh::lean_ctor_get(v_a_2588_, 0);
                    v_initialId_2594_ = leanh::lean_ctor_get(v_a_2588_, 1);
                    v_used_2595_ = leanh::lean_ctor_get(v_a_2589_, 0);
                    v_mapped_2596_ = leanh::lean_ctor_get(v_a_2589_, 1);
                    v_lastUse_2597_ = leanh::lean_ctor_get(v_a_2589_, 2);
                    v___x_2598_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2599_ = lean_nat_sub(v___x_2590_, v___x_2598_);
                    v_id_2600_ = lean_array_fget(v_worklist_2587_, v___x_2599_);
                    leanh::lean_dec(v___x_2599_);
                    v_worklist_2601_ = lean_array_pop(v_worklist_2587_);
                    v___x_2725_ = lean_nat_sub(v_id_2600_, v_initialId_2594_);
                    v___x_2726_ = lean_byte_array_size(v_used_2595_);
                    v___x_2727_ = lean_nat_dec_lt(v___x_2725_, v___x_2726_);
                    if v___x_2727_ == 0 {
                        leanh::lean_dec(v___x_2725_);
                        v___x_2728_ = l_instInhabitedUInt8;
                        v___x_2729_ = leanh::lean_box((v___x_2728_) as usize);
                        v___x_2730_ = l_outOfBounds___redArg(v___x_2729_);
                        leanh::lean_dec(v___x_2729_);
                        v___x_2731_ = (leanh::lean_unbox(v___x_2730_) as u8);
                        leanh::lean_dec(v___x_2730_);
                        v___y_2708_ = v___x_2731_;
                        state = 11;
                        continue;
                    } else {
                        v___x_2732_ = lean_byte_array_fget(v_used_2595_, v___x_2725_);
                        leanh::lean_dec(v___x_2725_);
                        v___y_2708_ = v___x_2732_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_worklist_2587_);
                    v___x_2733_ = leanh::lean_box(0);
                    v___x_2734_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2734_, 0, v___x_2733_);
                    leanh::lean_ctor_set(v___x_2734_, 1, v_a_2589_);
                    return v___x_2734_;
                }
            }
            1 => {
                v___x_2605_ = l_Array_append___redArg(v_worklist_2601_, v___y_2603_);
                leanh::lean_dec_ref(v___y_2603_);
                v_worklist_2587_ = v___x_2605_;
                v_a_2589_ = v_snd_2604_;
                state = 0;
                continue;
            }
            2 => {
                v_snd_2610_ = leanh::lean_ctor_get(v___y_2609_, 1);
                leanh::lean_inc(v_snd_2610_);
                leanh::lean_dec_ref(v___y_2609_);
                v___y_2603_ = v___y_2608_;
                v_snd_2604_ = v_snd_2610_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2614_ = l_Array_append___redArg(v_worklist_2601_, v___y_2612_);
                leanh::lean_dec_ref(v___y_2612_);
                v_worklist_2587_ = v___x_2614_;
                v_a_2589_ = v_snd_2613_;
                state = 0;
                continue;
            }
            4 => {
                v_snd_2619_ = leanh::lean_ctor_get(v___y_2618_, 1);
                leanh::lean_inc(v_snd_2619_);
                leanh::lean_dec_ref(v___y_2618_);
                v___y_2612_ = v___y_2617_;
                v_snd_2613_ = v_snd_2619_;
                state = 3;
                continue;
            }
            5 => {
                v___x_2624_ = l_Array_append___redArg(v_worklist_2601_, v___y_2621_);
                leanh::lean_dec_ref(v___y_2621_);
                v___x_2625_ = l_Array_append___redArg(v___x_2624_, v___y_2622_);
                leanh::lean_dec_ref(v___y_2622_);
                v_worklist_2587_ = v___x_2625_;
                v_a_2589_ = v_snd_2623_;
                state = 0;
                continue;
            }
            6 => {
                v_snd_2631_ = leanh::lean_ctor_get(v___y_2630_, 1);
                leanh::lean_inc(v_snd_2631_);
                leanh::lean_dec_ref(v___y_2630_);
                v___y_2621_ = v___y_2628_;
                v___y_2622_ = v___y_2629_;
                v_snd_2623_ = v_snd_2631_;
                state = 5;
                continue;
            }
            7 => {
                v___x_2638_ = lean_array_get_size(v___y_2637_);
                v___x_2639_ = lean_nat_dec_lt(v___x_2591_, v___x_2638_);
                if v___x_2639_ == 0 {
                    leanh::lean_dec(v_id_2600_);
                    v___y_2621_ = v___y_2637_;
                    v___y_2622_ = v___y_2636_;
                    v_snd_2623_ = v___y_2634_;
                    state = 5;
                    continue;
                } else {
                    v___x_2640_ = lean_nat_dec_le(v___x_2638_, v___x_2638_);
                    if v___x_2640_ == 0 {
                        if v___x_2639_ == 0 {
                            leanh::lean_dec(v_id_2600_);
                            v___y_2621_ = v___y_2637_;
                            v___y_2622_ = v___y_2636_;
                            v_snd_2623_ = v___y_2634_;
                            state = 5;
                            continue;
                        } else {
                            v___x_2641_ = lean_usize_of_nat(v___x_2638_);
                            v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_2600_, v___y_2637_, v___y_2635_, v___x_2641_, v___y_2633_, v_a_2588_, v___y_2634_);
                            v___y_2628_ = v___y_2637_;
                            v___y_2629_ = v___y_2636_;
                            v___y_2630_ = v___x_2642_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_2643_ = lean_usize_of_nat(v___x_2638_);
                        v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_2600_, v___y_2637_, v___y_2635_, v___x_2643_, v___y_2633_, v_a_2588_, v___y_2634_);
                        v___y_2628_ = v___y_2637_;
                        v___y_2629_ = v___y_2636_;
                        v___y_2630_ = v___x_2644_;
                        state = 6;
                        continue;
                    }
                }
            }
            8 => {
                v___x_2649_ = leanh::lean_box(0);
                v_sz_2650_ = lean_array_size(v___y_2647_);
                v___x_2651_ = 0usize;
                leanh::lean_inc(v_id_2600_);
                v___x_2652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(v_id_2600_, v___y_2647_, v_sz_2650_, v___x_2651_, v___x_2649_, v_snd_2648_);
                v_snd_2653_ = leanh::lean_ctor_get(v___x_2652_, 1);
                leanh::lean_inc(v_snd_2653_);
                leanh::lean_dec_ref(v___x_2652_);
                v___x_2654_ = lean_array_get_size(v___y_2646_);
                v___x_2655_ = lean_mk_empty_array_with_capacity(v___x_2654_);
                v___x_2656_ = lean_nat_dec_lt(v___x_2591_, v___x_2654_);
                if v___x_2656_ == 0 {
                    leanh::lean_dec_ref(v___y_2646_);
                    v___y_2633_ = v___x_2649_;
                    v___y_2634_ = v_snd_2653_;
                    v___y_2635_ = v___x_2651_;
                    v___y_2636_ = v___y_2647_;
                    v___y_2637_ = v___x_2655_;
                    state = 7;
                    continue;
                } else {
                    v___x_2657_ = lean_nat_dec_le(v___x_2654_, v___x_2654_);
                    if v___x_2657_ == 0 {
                        if v___x_2656_ == 0 {
                            leanh::lean_dec_ref(v___y_2646_);
                            v___y_2633_ = v___x_2649_;
                            v___y_2634_ = v_snd_2653_;
                            v___y_2635_ = v___x_2651_;
                            v___y_2636_ = v___y_2647_;
                            v___y_2637_ = v___x_2655_;
                            state = 7;
                            continue;
                        } else {
                            v___x_2658_ = lean_usize_of_nat(v___x_2654_);
                            v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(v___y_2646_, v___x_2651_, v___x_2658_, v___x_2655_);
                            leanh::lean_dec_ref(v___y_2646_);
                            v___y_2633_ = v___x_2649_;
                            v___y_2634_ = v_snd_2653_;
                            v___y_2635_ = v___x_2651_;
                            v___y_2636_ = v___y_2647_;
                            v___y_2637_ = v___x_2659_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___x_2660_ = lean_usize_of_nat(v___x_2654_);
                        v___x_2661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__5(v___y_2646_, v___x_2651_, v___x_2660_, v___x_2655_);
                        leanh::lean_dec_ref(v___y_2646_);
                        v___y_2633_ = v___x_2649_;
                        v___y_2634_ = v_snd_2653_;
                        v___y_2635_ = v___x_2651_;
                        v___y_2636_ = v___y_2647_;
                        v___y_2637_ = v___x_2661_;
                        state = 7;
                        continue;
                    }
                }
            }
            9 => {
                v_snd_2666_ = leanh::lean_ctor_get(v___y_2665_, 1);
                leanh::lean_inc(v_snd_2666_);
                leanh::lean_dec_ref(v___y_2665_);
                v___y_2646_ = v___y_2663_;
                v___y_2647_ = v___y_2664_;
                v_snd_2648_ = v_snd_2666_;
                state = 8;
                continue;
            }
            10 => {
                v___x_2669_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_proof_2593_, v_id_2600_);
                if leanh::lean_obj_tag(v___x_2669_) == 0 {
                    leanh::lean_dec(v_id_2600_);
                    v_worklist_2587_ = v_worklist_2601_;
                    v_a_2589_ = v_snd_2668_;
                    state = 0;
                    continue;
                } else {
                    v_val_2671_ = leanh::lean_ctor_get(v___x_2669_, 0);
                    leanh::lean_inc(v_val_2671_);
                    leanh::lean_dec_ref_known(v___x_2669_, 1);
                    match leanh::lean_obj_tag(v_val_2671_) {
                        0 => {
                            v_rupHints_2672_ = leanh::lean_ctor_get(v_val_2671_, 1);
                            leanh::lean_inc_ref(v_rupHints_2672_);
                            leanh::lean_dec_ref_known(v_val_2671_, 2);
                            v___x_2673_ = lean_array_get_size(v_rupHints_2672_);
                            v___x_2674_ = lean_nat_dec_lt(v___x_2591_, v___x_2673_);
                            if v___x_2674_ == 0 {
                                leanh::lean_dec(v_id_2600_);
                                v___y_2603_ = v_rupHints_2672_;
                                v_snd_2604_ = v_snd_2668_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2675_ = leanh::lean_box(0);
                                v___x_2676_ = lean_nat_dec_le(v___x_2673_, v___x_2673_);
                                if v___x_2676_ == 0 {
                                    if v___x_2674_ == 0 {
                                        leanh::lean_dec(v_id_2600_);
                                        v___y_2603_ = v_rupHints_2672_;
                                        v_snd_2604_ = v_snd_2668_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_2677_ = 0usize;
                                        v___x_2678_ = lean_usize_of_nat(v___x_2673_);
                                        v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_2600_, v_rupHints_2672_, v___x_2677_, v___x_2678_, v___x_2675_, v_snd_2668_);
                                        v___y_2608_ = v_rupHints_2672_;
                                        v___y_2609_ = v___x_2679_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___x_2680_ = 0usize;
                                    v___x_2681_ = lean_usize_of_nat(v___x_2673_);
                                    v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_2600_, v_rupHints_2672_, v___x_2680_, v___x_2681_, v___x_2675_, v_snd_2668_);
                                    v___y_2608_ = v_rupHints_2672_;
                                    v___y_2609_ = v___x_2682_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            v_rupHints_2683_ = leanh::lean_ctor_get(v_val_2671_, 2);
                            leanh::lean_inc_ref(v_rupHints_2683_);
                            leanh::lean_dec_ref_known(v_val_2671_, 3);
                            v___x_2684_ = lean_array_get_size(v_rupHints_2683_);
                            v___x_2685_ = lean_nat_dec_lt(v___x_2591_, v___x_2684_);
                            if v___x_2685_ == 0 {
                                leanh::lean_dec(v_id_2600_);
                                v___y_2612_ = v_rupHints_2683_;
                                v_snd_2613_ = v_snd_2668_;
                                state = 3;
                                continue;
                            } else {
                                v___x_2686_ = leanh::lean_box(0);
                                v___x_2687_ = lean_nat_dec_le(v___x_2684_, v___x_2684_);
                                if v___x_2687_ == 0 {
                                    if v___x_2685_ == 0 {
                                        leanh::lean_dec(v_id_2600_);
                                        v___y_2612_ = v_rupHints_2683_;
                                        v_snd_2613_ = v_snd_2668_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_2688_ = 0usize;
                                        v___x_2689_ = lean_usize_of_nat(v___x_2684_);
                                        v___x_2690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_2600_, v_rupHints_2683_, v___x_2688_, v___x_2689_, v___x_2686_, v_snd_2668_);
                                        v___y_2617_ = v_rupHints_2683_;
                                        v___y_2618_ = v___x_2690_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    v___x_2691_ = 0usize;
                                    v___x_2692_ = lean_usize_of_nat(v___x_2684_);
                                    v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_2600_, v_rupHints_2683_, v___x_2691_, v___x_2692_, v___x_2686_, v_snd_2668_);
                                    v___y_2617_ = v_rupHints_2683_;
                                    v___y_2618_ = v___x_2693_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                        2 => {
                            v_rupHints_2694_ = leanh::lean_ctor_get(v_val_2671_, 3);
                            leanh::lean_inc_ref(v_rupHints_2694_);
                            v_ratHints_2695_ = leanh::lean_ctor_get(v_val_2671_, 4);
                            leanh::lean_inc_ref(v_ratHints_2695_);
                            leanh::lean_dec_ref_known(v_val_2671_, 5);
                            v___x_2696_ = lean_array_get_size(v_rupHints_2694_);
                            v___x_2697_ = lean_nat_dec_lt(v___x_2591_, v___x_2696_);
                            if v___x_2697_ == 0 {
                                v___y_2646_ = v_ratHints_2695_;
                                v___y_2647_ = v_rupHints_2694_;
                                v_snd_2648_ = v_snd_2668_;
                                state = 8;
                                continue;
                            } else {
                                v___x_2698_ = leanh::lean_box(0);
                                v___x_2699_ = lean_nat_dec_le(v___x_2696_, v___x_2696_);
                                if v___x_2699_ == 0 {
                                    if v___x_2697_ == 0 {
                                        v___y_2646_ = v_ratHints_2695_;
                                        v___y_2647_ = v_rupHints_2694_;
                                        v_snd_2648_ = v_snd_2668_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v___x_2700_ = 0usize;
                                        v___x_2701_ = lean_usize_of_nat(v___x_2696_);
                                        leanh::lean_inc(v_id_2600_);
                                        v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_2600_, v_rupHints_2694_, v___x_2700_, v___x_2701_, v___x_2698_, v_a_2588_, v_snd_2668_);
                                        v___y_2663_ = v_ratHints_2695_;
                                        v___y_2664_ = v_rupHints_2694_;
                                        v___y_2665_ = v___x_2702_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    v___x_2703_ = 0usize;
                                    v___x_2704_ = lean_usize_of_nat(v___x_2696_);
                                    leanh::lean_inc(v_id_2600_);
                                    v___x_2705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__4(v_id_2600_, v_rupHints_2694_, v___x_2703_, v___x_2704_, v___x_2698_, v_a_2588_, v_snd_2668_);
                                    v___y_2663_ = v_ratHints_2695_;
                                    v___y_2664_ = v_rupHints_2694_;
                                    v___y_2665_ = v___x_2705_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            leanh::lean_dec_ref_known(v_val_2671_, 1);
                            leanh::lean_dec(v_id_2600_);
                            v_worklist_2587_ = v_worklist_2601_;
                            v_a_2589_ = v_snd_2668_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            11 => {
                v___x_2709_ = 1;
                v___x_2710_ = lean_uint8_dec_eq(v___y_2708_, v___x_2709_);
                if v___x_2710_ == 0 {
                    v___x_2711_ = lean_nat_dec_le(v_initialId_2594_, v_id_2600_);
                    if v___x_2711_ == 0 {
                        v_snd_2668_ = v_a_2589_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_lastUse_2597_);
                        leanh::lean_inc_ref(v_mapped_2596_);
                        leanh::lean_inc_ref(v_used_2595_);
                        v_isSharedCheck_2720_ = (!leanh::lean_is_exclusive(v_a_2589_)) as u8;
                        if v_isSharedCheck_2720_ == 0 {
                            v_unused_2721_ = leanh::lean_ctor_get(v_a_2589_, 2);
                            leanh::lean_dec(v_unused_2721_);
                            v_unused_2722_ = leanh::lean_ctor_get(v_a_2589_, 1);
                            leanh::lean_dec(v_unused_2722_);
                            v_unused_2723_ = leanh::lean_ctor_get(v_a_2589_, 0);
                            leanh::lean_dec(v_unused_2723_);
                            v___x_2713_ = v_a_2589_;
                            v_isShared_2714_ = v_isSharedCheck_2720_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_2589_);
                            v___x_2713_ = leanh::lean_box(0);
                            v_isShared_2714_ = v_isSharedCheck_2720_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_id_2600_);
                    v_worklist_2587_ = v_worklist_2601_;
                    state = 0;
                    continue;
                }
            }
            12 => {
                v___x_2715_ = lean_nat_sub(v_id_2600_, v_initialId_2594_);
                v___x_2716_ = lean_byte_array_set(v_used_2595_, v___x_2715_, v___x_2709_);
                leanh::lean_dec(v___x_2715_);
                if v_isShared_2714_ == 0 {
                    leanh::lean_ctor_set(v___x_2713_, 0, v___x_2716_);
                    v___x_2718_ = v___x_2713_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2719_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 1, v_mapped_2596_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2719_, 2, v_lastUse_2597_);
                    v___x_2718_ = v_reuseFailAlloc_2719_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_snd_2668_ = v___x_2718_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go___boxed(
    mut v_worklist_2735_: *mut leanh::LeanObject,
    mut v_a_2736_: *mut leanh::LeanObject,
    mut v_a_2737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2738_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go(v_worklist_2735_, v_a_2736_, v_a_2737_);
    leanh::lean_dec_ref(v_a_2736_);
    return v_res_2738_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1(
    mut v_00_u03b2_2739_: *mut leanh::LeanObject,
    mut v_m_2740_: *mut leanh::LeanObject,
    mut v_a_2741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_m_2740_, v_a_2741_);
    return v___x_2742_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___boxed(
    mut v_00_u03b2_2743_: *mut leanh::LeanObject,
    mut v_m_2744_: *mut leanh::LeanObject,
    mut v_a_2745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1(v_00_u03b2_2743_, v_m_2744_, v_a_2745_);
    leanh::lean_dec(v_a_2745_);
    leanh::lean_dec_ref(v_m_2744_);
    return v_res_2746_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2(
    mut v_id_2747_: *mut leanh::LeanObject,
    mut v_as_2748_: *mut leanh::LeanObject,
    mut v_i_2749_: usize,
    mut v_stop_2750_: usize,
    mut v_b_2751_: *mut leanh::LeanObject,
    mut v___y_2752_: *mut leanh::LeanObject,
    mut v___y_2753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___redArg(v_id_2747_, v_as_2748_, v_i_2749_, v_stop_2750_, v_b_2751_, v___y_2753_);
    return v___x_2754_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2___boxed(
    mut v_id_2755_: *mut leanh::LeanObject,
    mut v_as_2756_: *mut leanh::LeanObject,
    mut v_i_2757_: *mut leanh::LeanObject,
    mut v_stop_2758_: *mut leanh::LeanObject,
    mut v_b_2759_: *mut leanh::LeanObject,
    mut v___y_2760_: *mut leanh::LeanObject,
    mut v___y_2761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2762_: usize = 0;
    let mut v_stop_boxed_2763_: usize = 0;
    let mut v_res_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2762_ = leanh::lean_unbox_usize(v_i_2757_);
    leanh::lean_dec(v_i_2757_);
    v_stop_boxed_2763_ = leanh::lean_unbox_usize(v_stop_2758_);
    leanh::lean_dec(v_stop_2758_);
    v_res_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__2(v_id_2755_, v_as_2756_, v_i_boxed_2762_, v_stop_boxed_2763_, v_b_2759_, v___y_2760_, v___y_2761_);
    leanh::lean_dec_ref(v___y_2760_);
    leanh::lean_dec_ref(v_as_2756_);
    return v_res_2764_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3(
    mut v_id_2765_: *mut leanh::LeanObject,
    mut v_as_2766_: *mut leanh::LeanObject,
    mut v_sz_2767_: usize,
    mut v_i_2768_: usize,
    mut v_b_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
    mut v___y_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___redArg(v_id_2765_, v_as_2766_, v_sz_2767_, v_i_2768_, v_b_2769_, v___y_2771_);
    return v___x_2772_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3___boxed(
    mut v_id_2773_: *mut leanh::LeanObject,
    mut v_as_2774_: *mut leanh::LeanObject,
    mut v_sz_2775_: *mut leanh::LeanObject,
    mut v_i_2776_: *mut leanh::LeanObject,
    mut v_b_2777_: *mut leanh::LeanObject,
    mut v___y_2778_: *mut leanh::LeanObject,
    mut v___y_2779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2780_: usize = 0;
    let mut v_i_boxed_2781_: usize = 0;
    let mut v_res_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2780_ = leanh::lean_unbox_usize(v_sz_2775_);
    leanh::lean_dec(v_sz_2775_);
    v_i_boxed_2781_ = leanh::lean_unbox_usize(v_i_2776_);
    leanh::lean_dec(v_i_2776_);
    v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__3(v_id_2773_, v_as_2774_, v_sz_boxed_2780_, v_i_boxed_2781_, v_b_2777_, v___y_2778_, v___y_2779_);
    leanh::lean_dec_ref(v___y_2778_);
    leanh::lean_dec_ref(v_as_2774_);
    return v_res_2782_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1(
    mut v_00_u03b2_2783_: *mut leanh::LeanObject,
    mut v_a_2784_: *mut leanh::LeanObject,
    mut v_x_2785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2786_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___redArg(v_a_2784_, v_x_2785_);
    return v___x_2786_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1___boxed(
    mut v_00_u03b2_2787_: *mut leanh::LeanObject,
    mut v_a_2788_: *mut leanh::LeanObject,
    mut v_x_2789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2790_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1_spec__1(v_00_u03b2_2787_, v_a_2788_, v_x_2789_);
    leanh::lean_dec(v_x_2789_);
    leanh::lean_dec(v_a_2788_);
    return v_res_2790_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis(
    mut v_a_2791_: *mut leanh::LeanObject,
    mut v_a_2792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_addEmptyId_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_addEmptyId_2793_ = leanh::lean_ctor_get(v_a_2791_, 2);
    v___x_2794_ = leanh::lean_unsigned_to_nat(1);
    v___x_2795_ = lean_mk_empty_array_with_capacity(v___x_2794_);
    leanh::lean_inc(v_addEmptyId_2793_);
    v___x_2796_ = lean_array_push(v___x_2795_, v_addEmptyId_2793_);
    v___x_2797_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go(v___x_2796_, v_a_2791_, v_a_2792_);
    return v___x_2797_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis___boxed(
    mut v_a_2798_: *mut leanh::LeanObject,
    mut v_a_2799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2800_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis(v_a_2798_, v_a_2799_);
    leanh::lean_dec_ref(v_a_2798_);
    return v_res_2800_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(
    mut v_next_2801_: *mut leanh::LeanObject,
    mut v_x_2802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2802_) == 0 {
                    v___x_2803_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2804_ = lean_mk_empty_array_with_capacity(v___x_2803_);
                    v___x_2805_ = lean_array_push(v___x_2804_, v_next_2801_);
                    v___x_2806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2806_, 0, v___x_2805_);
                    return v___x_2806_;
                } else {
                    v_val_2807_ = leanh::lean_ctor_get(v_x_2802_, 0);
                    v_isSharedCheck_2815_ = (!leanh::lean_is_exclusive(v_x_2802_)) as u8;
                    if v_isSharedCheck_2815_ == 0 {
                        v___x_2809_ = v_x_2802_;
                        v_isShared_2810_ = v_isSharedCheck_2815_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2807_);
                        leanh::lean_dec(v_x_2802_);
                        v___x_2809_ = leanh::lean_box(0);
                        v_isShared_2810_ = v_isSharedCheck_2815_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2811_ = lean_array_push(v_val_2807_, v_next_2801_);
                if v_isShared_2810_ == 0 {
                    leanh::lean_ctor_set(v___x_2809_, 0, v___x_2811_);
                    v___x_2813_ = v___x_2809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2814_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
                    v___x_2813_ = v_reuseFailAlloc_2814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(
    mut v_next_2816_: *mut leanh::LeanObject,
    mut v_a_2817_: *mut leanh::LeanObject,
    mut v_x_2818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2828_: u8 = 0;
    let mut v___x_2829_: u8 = 0;
    let mut v_tail_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2818_) == 0 {
                    v___x_2819_ = leanh::lean_box(0);
                    v___x_2820_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(v_next_2816_, v___x_2819_);
                    v_val_2821_ = leanh::lean_ctor_get(v___x_2820_, 0);
                    leanh::lean_inc(v_val_2821_);
                    leanh::lean_dec(v___x_2820_);
                    v___x_2822_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2822_, 0, v_a_2817_);
                    leanh::lean_ctor_set(v___x_2822_, 1, v_val_2821_);
                    leanh::lean_ctor_set(v___x_2822_, 2, v_x_2818_);
                    return v___x_2822_;
                } else {
                    v_key_2823_ = leanh::lean_ctor_get(v_x_2818_, 0);
                    v_value_2824_ = leanh::lean_ctor_get(v_x_2818_, 1);
                    v_tail_2825_ = leanh::lean_ctor_get(v_x_2818_, 2);
                    v_isSharedCheck_2840_ = (!leanh::lean_is_exclusive(v_x_2818_)) as u8;
                    if v_isSharedCheck_2840_ == 0 {
                        v___x_2827_ = v_x_2818_;
                        v_isShared_2828_ = v_isSharedCheck_2840_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2825_);
                        leanh::lean_inc(v_value_2824_);
                        leanh::lean_inc(v_key_2823_);
                        leanh::lean_dec(v_x_2818_);
                        v___x_2827_ = leanh::lean_box(0);
                        v_isShared_2828_ = v_isSharedCheck_2840_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2829_ = lean_nat_dec_eq(v_key_2823_, v_a_2817_);
                if v___x_2829_ == 0 {
                    v_tail_2830_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(v_next_2816_, v_a_2817_, v_tail_2825_);
                    if v_isShared_2828_ == 0 {
                        leanh::lean_ctor_set(v___x_2827_, 2, v_tail_2830_);
                        v___x_2832_ = v___x_2827_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2833_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_key_2823_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_value_2824_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_tail_2830_);
                        v___x_2832_ = v_reuseFailAlloc_2833_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_key_2823_);
                    v___x_2834_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2834_, 0, v_value_2824_);
                    v___x_2835_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0___lam__0(v_next_2816_, v___x_2834_);
                    v_val_2836_ = leanh::lean_ctor_get(v___x_2835_, 0);
                    leanh::lean_inc(v_val_2836_);
                    leanh::lean_dec(v___x_2835_);
                    if v_isShared_2828_ == 0 {
                        leanh::lean_ctor_set(v___x_2827_, 1, v_val_2836_);
                        leanh::lean_ctor_set(v___x_2827_, 0, v_a_2817_);
                        v___x_2838_ = v___x_2827_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2839_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2817_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_val_2836_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_tail_2825_);
                        v___x_2838_ = v_reuseFailAlloc_2839_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2832_;
            }
            3 => {
                return v___x_2838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0(
    mut v_next_2841_: *mut leanh::LeanObject,
    mut v_m_2842_: *mut leanh::LeanObject,
    mut v_a_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2848_: u8 = 0;
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: u64 = 0;
    let mut v___x_2851_: u64 = 0;
    let mut v___x_2852_: u64 = 0;
    let mut v_fold_2853_: u64 = 0;
    let mut v___x_2854_: u64 = 0;
    let mut v___x_2855_: u64 = 0;
    let mut v___x_2856_: u64 = 0;
    let mut v___x_2857_: usize = 0;
    let mut v___x_2858_: usize = 0;
    let mut v___x_2859_: usize = 0;
    let mut v___x_2860_: usize = 0;
    let mut v___x_2861_: usize = 0;
    let mut v_bkt_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: u8 = 0;
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: u8 = 0;
    let mut v_val_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2844_ = leanh::lean_ctor_get(v_m_2842_, 0);
                v_buckets_2845_ = leanh::lean_ctor_get(v_m_2842_, 1);
                v_isSharedCheck_2895_ = (!leanh::lean_is_exclusive(v_m_2842_)) as u8;
                if v_isSharedCheck_2895_ == 0 {
                    v___x_2847_ = v_m_2842_;
                    v_isShared_2848_ = v_isSharedCheck_2895_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_2845_);
                    leanh::lean_inc(v_size_2844_);
                    leanh::lean_dec(v_m_2842_);
                    v___x_2847_ = leanh::lean_box(0);
                    v_isShared_2848_ = v_isSharedCheck_2895_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2849_ = lean_array_get_size(v_buckets_2845_);
                v___x_2850_ = lean_uint64_of_nat(v_a_2843_);
                v___x_2851_ = 32u64;
                v___x_2852_ = lean_uint64_shift_right(v___x_2850_, v___x_2851_);
                v_fold_2853_ = lean_uint64_xor(v___x_2850_, v___x_2852_);
                v___x_2854_ = 16u64;
                v___x_2855_ = lean_uint64_shift_right(v_fold_2853_, v___x_2854_);
                v___x_2856_ = lean_uint64_xor(v_fold_2853_, v___x_2855_);
                v___x_2857_ = lean_uint64_to_usize(v___x_2856_);
                v___x_2858_ = lean_usize_of_nat(v___x_2849_);
                v___x_2859_ = 1usize;
                v___x_2860_ = lean_usize_sub(v___x_2858_, v___x_2859_);
                v___x_2861_ = lean_usize_land(v___x_2857_, v___x_2860_);
                v_bkt_2862_ = lean_array_uget_borrowed(v_buckets_2845_, v___x_2861_);
                v___x_2863_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_2843_, v_bkt_2862_);
                if v___x_2863_ == 0 {
                    v___x_2864_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2865_ = lean_mk_empty_array_with_capacity(v___x_2864_);
                    v___x_2866_ = lean_array_push(v___x_2865_, v_next_2841_);
                    v_size_x27_2867_ = lean_nat_add(v_size_2844_, v___x_2864_);
                    leanh::lean_dec(v_size_2844_);
                    leanh::lean_inc(v_bkt_2862_);
                    v___x_2868_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2868_, 0, v_a_2843_);
                    leanh::lean_ctor_set(v___x_2868_, 1, v___x_2866_);
                    leanh::lean_ctor_set(v___x_2868_, 2, v_bkt_2862_);
                    v_buckets_x27_2869_ =
                        lean_array_uset(v_buckets_2845_, v___x_2861_, v___x_2868_);
                    v___x_2870_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2871_ = lean_nat_mul(v_size_x27_2867_, v___x_2870_);
                    v___x_2872_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2873_ = lean_nat_div(v___x_2871_, v___x_2872_);
                    leanh::lean_dec(v___x_2871_);
                    v___x_2874_ = lean_array_get_size(v_buckets_x27_2869_);
                    v___x_2875_ = lean_nat_dec_le(v___x_2873_, v___x_2874_);
                    leanh::lean_dec(v___x_2873_);
                    if v___x_2875_ == 0 {
                        v_val_2876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__1___redArg(v_buckets_x27_2869_);
                        if v_isShared_2848_ == 0 {
                            leanh::lean_ctor_set(v___x_2847_, 1, v_val_2876_);
                            leanh::lean_ctor_set(v___x_2847_, 0, v_size_x27_2867_);
                            v___x_2878_ = v___x_2847_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2879_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2879_,
                                0,
                                v_size_x27_2867_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_val_2876_);
                            v___x_2878_ = v_reuseFailAlloc_2879_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2848_ == 0 {
                            leanh::lean_ctor_set(v___x_2847_, 1, v_buckets_x27_2869_);
                            leanh::lean_ctor_set(v___x_2847_, 0, v_size_x27_2867_);
                            v___x_2881_ = v___x_2847_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2882_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2882_,
                                0,
                                v_size_x27_2867_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_2882_,
                                1,
                                v_buckets_x27_2869_,
                            );
                            v___x_2881_ = v_reuseFailAlloc_2882_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_2862_);
                    v___x_2883_ = leanh::lean_box(0);
                    v_buckets_x27_2884_ =
                        lean_array_uset(v_buckets_2845_, v___x_2861_, v___x_2883_);
                    leanh::lean_inc(v_a_2843_);
                    v_bkt_x27_2885_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0_spec__0(v_next_2841_, v_a_2843_, v_bkt_2862_);
                    v___x_2892_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run_spec__0_spec__0___redArg(v_a_2843_, v_bkt_x27_2885_);
                    leanh::lean_dec(v_a_2843_);
                    if v___x_2892_ == 0 {
                        v___x_2893_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2894_ = lean_nat_sub(v_size_2844_, v___x_2893_);
                        leanh::lean_dec(v_size_2844_);
                        v___y_2887_ = v___x_2894_;
                        state = 4;
                        continue;
                    } else {
                        v___y_2887_ = v_size_2844_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2878_;
            }
            3 => {
                return v___x_2881_;
            }
            4 => {
                v___x_2888_ = lean_array_uset(v_buckets_x27_2884_, v___x_2861_, v_bkt_x27_2885_);
                if v_isShared_2848_ == 0 {
                    leanh::lean_ctor_set(v___x_2847_, 1, v___x_2888_);
                    leanh::lean_ctor_set(v___x_2847_, 0, v___y_2887_);
                    v___x_2890_ = v___x_2847_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2891_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___y_2887_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 1, v___x_2888_);
                    v___x_2890_ = v_reuseFailAlloc_2891_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(
    mut v_upperBound_2896_: *mut leanh::LeanObject,
    mut v___x_2897_: *mut leanh::LeanObject,
    mut v_a_2898_: *mut leanh::LeanObject,
    mut v_b_2899_: *mut leanh::LeanObject,
    mut v___y_2900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: u8 = 0;
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2907_ = lean_nat_dec_lt(v_a_2898_, v_upperBound_2896_);
                if v___x_2907_ == 0 {
                    leanh::lean_dec(v_a_2898_);
                    v___x_2908_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2908_, 0, v_b_2899_);
                    leanh::lean_ctor_set(v___x_2908_, 1, v___y_2900_);
                    return v___x_2908_;
                } else {
                    v___x_2909_ = lean_array_fget_borrowed(v___x_2897_, v_a_2898_);
                    v___x_2910_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__1);
                    v___x_2911_ = lean_int_dec_eq(v___x_2909_, v___x_2910_);
                    if v___x_2911_ == 0 {
                        v___x_2912_ = lean_nat_abs(v___x_2909_);
                        leanh::lean_inc(v_a_2898_);
                        v___x_2913_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__0(v_a_2898_, v_b_2899_, v___x_2912_);
                        v_a_2902_ = v___x_2913_;
                        v_snd_2903_ = v___y_2900_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2902_ = v_b_2899_;
                        v_snd_2903_ = v___y_2900_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2904_ = leanh::lean_unsigned_to_nat(1);
                v___x_2905_ = lean_nat_add(v_a_2898_, v___x_2904_);
                leanh::lean_dec(v_a_2898_);
                v_a_2898_ = v___x_2905_;
                v_b_2899_ = v_a_2902_;
                v___y_2900_ = v_snd_2903_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg___boxed(
    mut v_upperBound_2914_: *mut leanh::LeanObject,
    mut v___x_2915_: *mut leanh::LeanObject,
    mut v_a_2916_: *mut leanh::LeanObject,
    mut v_b_2917_: *mut leanh::LeanObject,
    mut v___y_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2919_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(v_upperBound_2914_, v___x_2915_, v_a_2916_, v_b_2917_, v___y_2918_);
    leanh::lean_dec_ref(v___x_2915_);
    leanh::lean_dec(v_upperBound_2914_);
    return v_res_2919_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete(
    mut v_a_2920_: *mut leanh::LeanObject,
    mut v_a_2921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lastUse_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lastUse_2922_ = leanh::lean_ctor_get(v_a_2921_, 2);
    leanh::lean_inc_ref(v_lastUse_2922_);
    v___x_2923_ = leanh::lean_unsigned_to_nat(0);
    v___x_2924_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg___closed__3);
    v___x_2925_ = lean_array_get_size(v_lastUse_2922_);
    v___x_2926_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(v___x_2925_, v_lastUse_2922_, v___x_2923_, v___x_2924_, v_a_2921_);
    leanh::lean_dec_ref(v_lastUse_2922_);
    return v___x_2926_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete___boxed(
    mut v_a_2927_: *mut leanh::LeanObject,
    mut v_a_2928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2929_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete(v_a_2927_, v_a_2928_);
    leanh::lean_dec_ref(v_a_2927_);
    return v_res_2929_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1(
    mut v_upperBound_2930_: *mut leanh::LeanObject,
    mut v___x_2931_: *mut leanh::LeanObject,
    mut v_inst_2932_: *mut leanh::LeanObject,
    mut v_R_2933_: *mut leanh::LeanObject,
    mut v_a_2934_: *mut leanh::LeanObject,
    mut v_b_2935_: *mut leanh::LeanObject,
    mut v_c_2936_: *mut leanh::LeanObject,
    mut v___y_2937_: *mut leanh::LeanObject,
    mut v___y_2938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2939_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___redArg(v_upperBound_2930_, v___x_2931_, v_a_2934_, v_b_2935_, v___y_2938_);
    return v___x_2939_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1___boxed(
    mut v_upperBound_2940_: *mut leanh::LeanObject,
    mut v___x_2941_: *mut leanh::LeanObject,
    mut v_inst_2942_: *mut leanh::LeanObject,
    mut v_R_2943_: *mut leanh::LeanObject,
    mut v_a_2944_: *mut leanh::LeanObject,
    mut v_b_2945_: *mut leanh::LeanObject,
    mut v_c_2946_: *mut leanh::LeanObject,
    mut v___y_2947_: *mut leanh::LeanObject,
    mut v___y_2948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_computeToDelete_spec__1(v_upperBound_2940_, v___x_2941_, v_inst_2942_, v_R_2943_, v_a_2944_, v_b_2945_, v_c_2946_, v___y_2947_, v___y_2948_);
    leanh::lean_dec_ref(v___y_2947_);
    leanh::lean_dec_ref(v___x_2941_);
    leanh::lean_dec(v_upperBound_2940_);
    return v_res_2949_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__2(
    mut v_msg_2950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2951_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__2___closed__7);
    v___x_2952_ = lean_panic_fn_borrowed(v___x_2951_, v_msg_2950_);
    return v___x_2952_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(
    mut v_next_2953_: *mut leanh::LeanObject,
    mut v_as_2954_: *mut leanh::LeanObject,
    mut v_sz_2955_: usize,
    mut v_i_2956_: usize,
    mut v_b_2957_: *mut leanh::LeanObject,
    mut v___y_2958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: usize = 0;
    let mut v___x_2963_: usize = 0;
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: u8 = 0;
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2965_ = lean_usize_dec_lt(v_i_2956_, v_sz_2955_);
                if v___x_2965_ == 0 {
                    leanh::lean_dec(v_next_2953_);
                    v___x_2966_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2966_, 0, v_b_2957_);
                    leanh::lean_ctor_set(v___x_2966_, 1, v___y_2958_);
                    return v___x_2966_;
                } else {
                    v_lastUse_2967_ = leanh::lean_ctor_get(v___y_2958_, 2);
                    v_a_2968_ = lean_array_uget_borrowed(v_as_2954_, v_i_2956_);
                    v___x_2969_ = l_Int_instInhabited;
                    v___x_2970_ = lean_array_get_borrowed(v___x_2969_, v_lastUse_2967_, v_a_2968_);
                    leanh::lean_inc(v_next_2953_);
                    v___x_2971_ = lean_nat_to_int(v_next_2953_);
                    v___x_2972_ = lean_int_dec_eq(v___x_2970_, v___x_2971_);
                    leanh::lean_dec(v___x_2971_);
                    if v___x_2972_ == 0 {
                        v_a_2960_ = v_b_2957_;
                        v_snd_2961_ = v___y_2958_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2968_);
                        v___x_2973_ = lean_array_push(v_b_2957_, v_a_2968_);
                        v_a_2960_ = v___x_2973_;
                        v_snd_2961_ = v___y_2958_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2962_ = 1usize;
                v___x_2963_ = lean_usize_add(v_i_2956_, v___x_2962_);
                v_i_2956_ = v___x_2963_;
                v_b_2957_ = v_a_2960_;
                v___y_2958_ = v_snd_2961_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg___boxed(
    mut v_next_2974_: *mut leanh::LeanObject,
    mut v_as_2975_: *mut leanh::LeanObject,
    mut v_sz_2976_: *mut leanh::LeanObject,
    mut v_i_2977_: *mut leanh::LeanObject,
    mut v_b_2978_: *mut leanh::LeanObject,
    mut v___y_2979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2980_: usize = 0;
    let mut v_i_boxed_2981_: usize = 0;
    let mut v_res_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2980_ = leanh::lean_unbox_usize(v_sz_2976_);
    leanh::lean_dec(v_sz_2976_);
    v_i_boxed_2981_ = leanh::lean_unbox_usize(v_i_2977_);
    leanh::lean_dec(v_i_2977_);
    v_res_2982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(v_next_2974_, v_as_2975_, v_sz_boxed_2980_, v_i_boxed_2981_, v_b_2978_, v___y_2979_);
    leanh::lean_dec_ref(v_as_2975_);
    return v_res_2982_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0(
    mut v_next_2983_: *mut leanh::LeanObject,
    mut v_as_2984_: *mut leanh::LeanObject,
    mut v_sz_2985_: usize,
    mut v_i_2986_: usize,
    mut v_b_2987_: *mut leanh::LeanObject,
    mut v___y_2988_: *mut leanh::LeanObject,
    mut v___y_2989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: usize = 0;
    let mut v___x_2994_: usize = 0;
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: u8 = 0;
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: u8 = 0;
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2996_ = lean_usize_dec_lt(v_i_2986_, v_sz_2985_);
                if v___x_2996_ == 0 {
                    leanh::lean_dec(v_next_2983_);
                    v___x_2997_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2997_, 0, v_b_2987_);
                    leanh::lean_ctor_set(v___x_2997_, 1, v___y_2989_);
                    return v___x_2997_;
                } else {
                    v_lastUse_2998_ = leanh::lean_ctor_get(v___y_2989_, 2);
                    v_a_2999_ = lean_array_uget_borrowed(v_as_2984_, v_i_2986_);
                    v___x_3000_ = l_Int_instInhabited;
                    v___x_3001_ = lean_array_get_borrowed(v___x_3000_, v_lastUse_2998_, v_a_2999_);
                    leanh::lean_inc(v_next_2983_);
                    v___x_3002_ = lean_nat_to_int(v_next_2983_);
                    v___x_3003_ = lean_int_dec_eq(v___x_3001_, v___x_3002_);
                    leanh::lean_dec(v___x_3002_);
                    if v___x_3003_ == 0 {
                        v_a_2991_ = v_b_2987_;
                        v_snd_2992_ = v___y_2989_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2999_);
                        v___x_3004_ = lean_array_push(v_b_2987_, v_a_2999_);
                        v_a_2991_ = v___x_3004_;
                        v_snd_2992_ = v___y_2989_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2993_ = 1usize;
                v___x_2994_ = lean_usize_add(v_i_2986_, v___x_2993_);
                v___x_2995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(v_next_2983_, v_as_2984_, v_sz_2985_, v___x_2994_, v_a_2991_, v_snd_2992_);
                return v___x_2995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0___boxed(
    mut v_next_3005_: *mut leanh::LeanObject,
    mut v_as_3006_: *mut leanh::LeanObject,
    mut v_sz_3007_: *mut leanh::LeanObject,
    mut v_i_3008_: *mut leanh::LeanObject,
    mut v_b_3009_: *mut leanh::LeanObject,
    mut v___y_3010_: *mut leanh::LeanObject,
    mut v___y_3011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3012_: usize = 0;
    let mut v_i_boxed_3013_: usize = 0;
    let mut v_res_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3012_ = leanh::lean_unbox_usize(v_sz_3007_);
    leanh::lean_dec(v_sz_3007_);
    v_i_boxed_3013_ = leanh::lean_unbox_usize(v_i_3008_);
    leanh::lean_dec(v_i_3008_);
    v_res_3014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_next_3005_, v_as_3006_, v_sz_boxed_3012_, v_i_boxed_3013_, v_b_3009_, v___y_3010_, v___y_3011_);
    leanh::lean_dec_ref(v___y_3010_);
    leanh::lean_dec_ref(v_as_3006_);
    return v_res_3014_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(
    mut v_next_3015_: *mut leanh::LeanObject,
    mut v_as_3016_: *mut leanh::LeanObject,
    mut v_sz_3017_: usize,
    mut v_i_3018_: usize,
    mut v_b_3019_: *mut leanh::LeanObject,
    mut v___y_3020_: *mut leanh::LeanObject,
    mut v___y_3021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3022_: u8 = 0;
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deletions_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3031_: usize = 0;
    let mut v___x_3032_: usize = 0;
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: usize = 0;
    let mut v___x_3037_: usize = 0;
    let mut v_lastUse_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3022_ = lean_usize_dec_lt(v_i_3018_, v_sz_3017_);
                if v___x_3022_ == 0 {
                    leanh::lean_dec(v_next_3015_);
                    v___x_3023_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3023_, 0, v_b_3019_);
                    leanh::lean_ctor_set(v___x_3023_, 1, v___y_3021_);
                    return v___x_3023_;
                } else {
                    v_a_3024_ = lean_array_uget_borrowed(v_as_3016_, v_i_3018_);
                    v_fst_3025_ = leanh::lean_ctor_get(v_a_3024_, 0);
                    v_snd_3026_ = leanh::lean_ctor_get(v_a_3024_, 1);
                    v_lastUse_3039_ = leanh::lean_ctor_get(v___y_3021_, 2);
                    v___x_3040_ = l_Int_instInhabited;
                    v___x_3041_ =
                        lean_array_get_borrowed(v___x_3040_, v_lastUse_3039_, v_fst_3025_);
                    leanh::lean_inc(v_next_3015_);
                    v___x_3042_ = lean_nat_to_int(v_next_3015_);
                    v___x_3043_ = lean_int_dec_eq(v___x_3041_, v___x_3042_);
                    leanh::lean_dec(v___x_3042_);
                    if v___x_3043_ == 0 {
                        v_deletions_3028_ = v_b_3019_;
                        v___y_3029_ = v___y_3020_;
                        v___y_3030_ = v___y_3021_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_3025_);
                        v___x_3044_ = lean_array_push(v_b_3019_, v_fst_3025_);
                        v_deletions_3028_ = v___x_3044_;
                        v___y_3029_ = v___y_3020_;
                        v___y_3030_ = v___y_3021_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_3031_ = lean_array_size(v_snd_3026_);
                v___x_3032_ = 0usize;
                leanh::lean_inc(v_next_3015_);
                v___x_3033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_next_3015_, v_snd_3026_, v_sz_3031_, v___x_3032_, v_deletions_3028_, v___y_3029_, v___y_3030_);
                v_fst_3034_ = leanh::lean_ctor_get(v___x_3033_, 0);
                leanh::lean_inc(v_fst_3034_);
                v_snd_3035_ = leanh::lean_ctor_get(v___x_3033_, 1);
                leanh::lean_inc(v_snd_3035_);
                leanh::lean_dec_ref(v___x_3033_);
                v___x_3036_ = 1usize;
                v___x_3037_ = lean_usize_add(v_i_3018_, v___x_3036_);
                v_i_3018_ = v___x_3037_;
                v_b_3019_ = v_fst_3034_;
                v___y_3021_ = v_snd_3035_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2___boxed(
    mut v_next_3045_: *mut leanh::LeanObject,
    mut v_as_3046_: *mut leanh::LeanObject,
    mut v_sz_3047_: *mut leanh::LeanObject,
    mut v_i_3048_: *mut leanh::LeanObject,
    mut v_b_3049_: *mut leanh::LeanObject,
    mut v___y_3050_: *mut leanh::LeanObject,
    mut v___y_3051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3052_: usize = 0;
    let mut v_i_boxed_3053_: usize = 0;
    let mut v_res_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3052_ = leanh::lean_unbox_usize(v_sz_3047_);
    leanh::lean_dec(v_sz_3047_);
    v_i_boxed_3053_ = leanh::lean_unbox_usize(v_i_3048_);
    leanh::lean_dec(v_i_3048_);
    v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(v_next_3045_, v_as_3046_, v_sz_boxed_3052_, v_i_boxed_3053_, v_b_3049_, v___y_3050_, v___y_3051_);
    leanh::lean_dec_ref(v___y_3050_);
    leanh::lean_dec_ref(v_as_3046_);
    return v_res_3054_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__1(
    mut v_next_3055_: *mut leanh::LeanObject,
    mut v_as_3056_: *mut leanh::LeanObject,
    mut v_sz_3057_: usize,
    mut v_i_3058_: usize,
    mut v_b_3059_: *mut leanh::LeanObject,
    mut v___y_3060_: *mut leanh::LeanObject,
    mut v___y_3061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3062_: u8 = 0;
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deletions_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3071_: usize = 0;
    let mut v___x_3072_: usize = 0;
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: usize = 0;
    let mut v___x_3077_: usize = 0;
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: u8 = 0;
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3062_ = lean_usize_dec_lt(v_i_3058_, v_sz_3057_);
                if v___x_3062_ == 0 {
                    leanh::lean_dec(v_next_3055_);
                    v___x_3063_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3063_, 0, v_b_3059_);
                    leanh::lean_ctor_set(v___x_3063_, 1, v___y_3061_);
                    return v___x_3063_;
                } else {
                    v_a_3064_ = lean_array_uget_borrowed(v_as_3056_, v_i_3058_);
                    v_fst_3065_ = leanh::lean_ctor_get(v_a_3064_, 0);
                    v_snd_3066_ = leanh::lean_ctor_get(v_a_3064_, 1);
                    v_lastUse_3079_ = leanh::lean_ctor_get(v___y_3061_, 2);
                    v___x_3080_ = l_Int_instInhabited;
                    v___x_3081_ =
                        lean_array_get_borrowed(v___x_3080_, v_lastUse_3079_, v_fst_3065_);
                    leanh::lean_inc(v_next_3055_);
                    v___x_3082_ = lean_nat_to_int(v_next_3055_);
                    v___x_3083_ = lean_int_dec_eq(v___x_3081_, v___x_3082_);
                    leanh::lean_dec(v___x_3082_);
                    if v___x_3083_ == 0 {
                        v_deletions_3068_ = v_b_3059_;
                        v___y_3069_ = v___y_3060_;
                        v___y_3070_ = v___y_3061_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_3065_);
                        v___x_3084_ = lean_array_push(v_b_3059_, v_fst_3065_);
                        v_deletions_3068_ = v___x_3084_;
                        v___y_3069_ = v___y_3060_;
                        v___y_3070_ = v___y_3061_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_3071_ = lean_array_size(v_snd_3066_);
                v___x_3072_ = 0usize;
                leanh::lean_inc(v_next_3055_);
                v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_next_3055_, v_snd_3066_, v_sz_3071_, v___x_3072_, v_deletions_3068_, v___y_3069_, v___y_3070_);
                v_fst_3074_ = leanh::lean_ctor_get(v___x_3073_, 0);
                leanh::lean_inc(v_fst_3074_);
                v_snd_3075_ = leanh::lean_ctor_get(v___x_3073_, 1);
                leanh::lean_inc(v_snd_3075_);
                leanh::lean_dec_ref(v___x_3073_);
                v___x_3076_ = 1usize;
                v___x_3077_ = lean_usize_add(v_i_3058_, v___x_3076_);
                v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__1_spec__2(v_next_3055_, v_as_3056_, v_sz_3057_, v___x_3077_, v_fst_3074_, v___y_3060_, v_snd_3075_);
                return v___x_3078_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__1___boxed(
    mut v_next_3085_: *mut leanh::LeanObject,
    mut v_as_3086_: *mut leanh::LeanObject,
    mut v_sz_3087_: *mut leanh::LeanObject,
    mut v_i_3088_: *mut leanh::LeanObject,
    mut v_b_3089_: *mut leanh::LeanObject,
    mut v___y_3090_: *mut leanh::LeanObject,
    mut v___y_3091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3092_: usize = 0;
    let mut v_i_boxed_3093_: usize = 0;
    let mut v_res_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3092_ = leanh::lean_unbox_usize(v_sz_3087_);
    leanh::lean_dec(v_sz_3087_);
    v_i_boxed_3093_ = leanh::lean_unbox_usize(v_i_3088_);
    leanh::lean_dec(v_i_3088_);
    v_res_3094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__1(v_next_3085_, v_as_3086_, v_sz_boxed_3092_, v_i_boxed_3093_, v_b_3089_, v___y_3090_, v___y_3091_);
    leanh::lean_dec_ref(v___y_3090_);
    leanh::lean_dec_ref(v_as_3086_);
    return v_res_3094_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(
    mut v___y_3095_: *mut leanh::LeanObject,
    mut v_fst_3096_: *mut leanh::LeanObject,
    mut v_snd_3097_: *mut leanh::LeanObject,
    mut v___x_3098_: u8,
    mut v_____r_3099_: *mut leanh::LeanObject,
    mut v_deletions_3100_: *mut leanh::LeanObject,
    mut v___y_3101_: *mut leanh::LeanObject,
    mut v___y_3102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3108_: u8 = 0;
    let mut v_sz_3109_: usize = 0;
    let mut v___x_3110_: usize = 0;
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v_newProof_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3103_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep(v___y_3095_, v___y_3101_, v___y_3102_);
                v_fst_3104_ = leanh::lean_ctor_get(v___x_3103_, 0);
                v_snd_3105_ = leanh::lean_ctor_get(v___x_3103_, 1);
                v_isSharedCheck_3135_ = (!leanh::lean_is_exclusive(v___x_3103_)) as u8;
                if v_isSharedCheck_3135_ == 0 {
                    v___x_3107_ = v___x_3103_;
                    v_isShared_3108_ = v_isSharedCheck_3135_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3105_);
                    leanh::lean_inc(v_fst_3104_);
                    leanh::lean_dec(v___x_3103_);
                    v___x_3107_ = leanh::lean_box(0);
                    v_isShared_3108_ = v_isSharedCheck_3135_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_3109_ = lean_array_size(v_deletions_3100_);
                v___x_3110_ = 0usize;
                v___x_3111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_mapStep_spec__0(v_sz_3109_, v___x_3110_, v_deletions_3100_, v___y_3101_, v_snd_3105_);
                v_fst_3112_ = leanh::lean_ctor_get(v___x_3111_, 0);
                v_snd_3113_ = leanh::lean_ctor_get(v___x_3111_, 1);
                v_isSharedCheck_3134_ = (!leanh::lean_is_exclusive(v___x_3111_)) as u8;
                if v_isSharedCheck_3134_ == 0 {
                    v___x_3115_ = v___x_3111_;
                    v_isShared_3116_ = v_isSharedCheck_3134_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3113_);
                    leanh::lean_inc(v_fst_3112_);
                    leanh::lean_dec(v___x_3111_);
                    v___x_3115_ = leanh::lean_box(0);
                    v_isShared_3116_ = v_isSharedCheck_3134_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3128_ = lean_array_push(v_snd_3097_, v_fst_3104_);
                v___x_3129_ = lean_array_get_size(v_fst_3112_);
                v___x_3130_ = leanh::lean_unsigned_to_nat(0);
                v___x_3131_ = lean_nat_dec_eq(v___x_3129_, v___x_3130_);
                if v___x_3131_ == 0 {
                    if v___x_3098_ == 0 {
                        leanh::lean_dec(v_fst_3112_);
                        v_newProof_3118_ = v___x_3128_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3132_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3132_, 0, v_fst_3112_);
                        v___x_3133_ = lean_array_push(v___x_3128_, v___x_3132_);
                        v_newProof_3118_ = v___x_3133_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_3112_);
                    v_newProof_3118_ = v___x_3128_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3119_ = leanh::lean_unsigned_to_nat(1);
                v___x_3120_ = lean_nat_add(v_fst_3096_, v___x_3119_);
                if v_isShared_3116_ == 0 {
                    leanh::lean_ctor_set(v___x_3115_, 1, v_newProof_3118_);
                    leanh::lean_ctor_set(v___x_3115_, 0, v___x_3120_);
                    v___x_3122_ = v___x_3115_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3120_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3127_, 1, v_newProof_3118_);
                    v___x_3122_ = v_reuseFailAlloc_3127_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3123_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3123_, 0, v___x_3122_);
                if v_isShared_3108_ == 0 {
                    leanh::lean_ctor_set(v___x_3107_, 1, v_snd_3113_);
                    leanh::lean_ctor_set(v___x_3107_, 0, v___x_3123_);
                    v___x_3125_ = v___x_3107_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3126_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3123_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_snd_3113_);
                    v___x_3125_ = v_reuseFailAlloc_3126_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0___boxed(
    mut v___y_3136_: *mut leanh::LeanObject,
    mut v_fst_3137_: *mut leanh::LeanObject,
    mut v_snd_3138_: *mut leanh::LeanObject,
    mut v___x_3139_: *mut leanh::LeanObject,
    mut v_____r_3140_: *mut leanh::LeanObject,
    mut v_deletions_3141_: *mut leanh::LeanObject,
    mut v___y_3142_: *mut leanh::LeanObject,
    mut v___y_3143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_22197__boxed_3144_: u8 = 0;
    let mut v_res_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_22197__boxed_3144_ = (leanh::lean_unbox(v___x_3139_) as u8);
    v_res_3145_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_3136_, v_fst_3137_, v_snd_3138_, v___x_22197__boxed_3144_, v_____r_3140_, v_deletions_3141_, v___y_3142_, v___y_3143_);
    leanh::lean_dec_ref(v___y_3142_);
    leanh::lean_dec(v_fst_3137_);
    return v_res_3145_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3151_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__3;
    v___x_3152_ = leanh::lean_unsigned_to_nat(14);
    v___x_3153_ = leanh::lean_unsigned_to_nat(22);
    v___x_3154_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__2;
    v___x_3155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__1;
    v___x_3156_ = l_mkPanicMessageWithDecl(
        v___x_3155_,
        v___x_3154_,
        v___x_3153_,
        v___x_3152_,
        v___x_3151_,
    );
    return v___x_3156_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(
    mut v_upperBound_3157_: *mut leanh::LeanObject,
    mut v___x_3158_: *mut leanh::LeanObject,
    mut v_a_3159_: *mut leanh::LeanObject,
    mut v_b_3160_: *mut leanh::LeanObject,
    mut v___y_3161_: *mut leanh::LeanObject,
    mut v___y_3162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3175_: u8 = 0;
    let mut v_a_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3180_: u8 = 0;
    let mut v_unused_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: u8 = 0;
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___y_3198_: u8 = 0;
    let mut v___y_3199_: u8 = 0;
    let mut v___y_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: u8 = 0;
    let mut v_rupHints_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3207_: usize = 0;
    let mut v___x_3208_: usize = 0;
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratHints_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3216_: usize = 0;
    let mut v___x_3217_: usize = 0;
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3221_: usize = 0;
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialId_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mapped_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastUse_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3235_: u8 = 0;
    let mut v___x_3236_: u8 = 0;
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3253_: u8 = 0;
    let mut v_unused_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: u8 = 0;
    let mut v___x_3260_: u8 = 0;
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: u8 = 0;
    let mut v___x_3264_: u8 = 0;
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3190_ = lean_nat_dec_le(v_a_3159_, v_upperBound_3157_);
                if v___x_3190_ == 0 {
                    leanh::lean_dec(v_a_3159_);
                    v___x_3191_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3191_, 0, v_b_3160_);
                    leanh::lean_ctor_set(v___x_3191_, 1, v___y_3162_);
                    return v___x_3191_;
                } else {
                    v_fst_3192_ = leanh::lean_ctor_get(v_b_3160_, 0);
                    v_snd_3193_ = leanh::lean_ctor_get(v_b_3160_, 1);
                    v_isSharedCheck_3265_ = (!leanh::lean_is_exclusive(v_b_3160_)) as u8;
                    if v_isSharedCheck_3265_ == 0 {
                        v___x_3195_ = v_b_3160_;
                        v_isShared_3196_ = v_isSharedCheck_3265_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3193_);
                        leanh::lean_inc(v_fst_3192_);
                        leanh::lean_dec(v_b_3160_);
                        v___x_3195_ = leanh::lean_box(0);
                        v_isShared_3196_ = v_isSharedCheck_3265_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3166_ = leanh::lean_unsigned_to_nat(1);
                v___x_3167_ = lean_nat_add(v_a_3159_, v___x_3166_);
                leanh::lean_dec(v_a_3159_);
                v_a_3159_ = v___x_3167_;
                v_b_3160_ = v_a_3164_;
                v___y_3162_ = v_snd_3165_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_3171_ = leanh::lean_ctor_get(v___y_3170_, 0);
                leanh::lean_inc(v_fst_3171_);
                if leanh::lean_obj_tag(v_fst_3171_) == 0 {
                    leanh::lean_dec(v_a_3159_);
                    v_snd_3172_ = leanh::lean_ctor_get(v___y_3170_, 1);
                    v_isSharedCheck_3180_ = (!leanh::lean_is_exclusive(v___y_3170_)) as u8;
                    if v_isSharedCheck_3180_ == 0 {
                        v_unused_3181_ = leanh::lean_ctor_get(v___y_3170_, 0);
                        leanh::lean_dec(v_unused_3181_);
                        v___x_3174_ = v___y_3170_;
                        v_isShared_3175_ = v_isSharedCheck_3180_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3172_);
                        leanh::lean_dec(v___y_3170_);
                        v___x_3174_ = leanh::lean_box(0);
                        v_isShared_3175_ = v_isSharedCheck_3180_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_snd_3182_ = leanh::lean_ctor_get(v___y_3170_, 1);
                    leanh::lean_inc(v_snd_3182_);
                    leanh::lean_dec_ref(v___y_3170_);
                    v_a_3183_ = leanh::lean_ctor_get(v_fst_3171_, 0);
                    leanh::lean_inc(v_a_3183_);
                    leanh::lean_dec_ref_known(v_fst_3171_, 1);
                    v_a_3164_ = v_a_3183_;
                    v_snd_3165_ = v_snd_3182_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_3176_ = leanh::lean_ctor_get(v_fst_3171_, 0);
                leanh::lean_inc(v_a_3176_);
                leanh::lean_dec_ref_known(v_fst_3171_, 1);
                if v_isShared_3175_ == 0 {
                    leanh::lean_ctor_set(v___x_3174_, 0, v_a_3176_);
                    v___x_3178_ = v___x_3174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3179_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_snd_3172_);
                    v___x_3178_ = v_reuseFailAlloc_3179_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3178_;
            }
            5 => {
                v___x_3188_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___y_3161_);
                v___x_3189_ = leanh::lean_apply_4(
                    v___y_3186_,
                    v___x_3188_,
                    v___y_3185_,
                    v___y_3161_,
                    v___y_3187_,
                );
                v___y_3170_ = v___x_3189_;
                state = 2;
                continue;
            }
            6 => {
                v_proof_3229_ = leanh::lean_ctor_get(v___y_3161_, 0);
                v_initialId_3230_ = leanh::lean_ctor_get(v___y_3161_, 1);
                v_used_3231_ = leanh::lean_ctor_get(v___y_3162_, 0);
                v_mapped_3232_ = leanh::lean_ctor_get(v___y_3162_, 1);
                v_lastUse_3233_ = leanh::lean_ctor_get(v___y_3162_, 2);
                v___x_3257_ = lean_nat_sub(v_a_3159_, v_initialId_3230_);
                v___x_3258_ = lean_byte_array_size(v_used_3231_);
                v___x_3259_ = lean_nat_dec_lt(v___x_3257_, v___x_3258_);
                if v___x_3259_ == 0 {
                    leanh::lean_dec(v___x_3257_);
                    v___x_3260_ = l_instInhabitedUInt8;
                    v___x_3261_ = leanh::lean_box((v___x_3260_) as usize);
                    v___x_3262_ = l_outOfBounds___redArg(v___x_3261_);
                    leanh::lean_dec(v___x_3261_);
                    v___x_3263_ = (leanh::lean_unbox(v___x_3262_) as u8);
                    leanh::lean_dec(v___x_3262_);
                    v___y_3235_ = v___x_3263_;
                    state = 8;
                    continue;
                } else {
                    v___x_3264_ = lean_byte_array_fget(v_used_3231_, v___x_3257_);
                    leanh::lean_dec(v___x_3257_);
                    v___y_3235_ = v___x_3264_;
                    state = 8;
                    continue;
                }
            }
            7 => {
                v___x_3202_ = leanh::lean_box((v___y_3198_) as usize);
                leanh::lean_inc(v_snd_3193_);
                leanh::lean_inc(v_fst_3192_);
                leanh::lean_inc_ref(v___y_3201_);
                v___f_3203_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 4);
                leanh::lean_closure_set(v___f_3203_, 0, v___y_3201_);
                leanh::lean_closure_set(v___f_3203_, 1, v_fst_3192_);
                leanh::lean_closure_set(v___f_3203_, 2, v_snd_3193_);
                leanh::lean_closure_set(v___f_3203_, 3, v___x_3202_);
                v___x_3204_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__0;
                v___x_3205_ = lean_nat_dec_eq(v_a_3159_, v___x_3158_);
                if v___x_3205_ == 0 {
                    if v___y_3199_ == 0 {
                        leanh::lean_dec_ref(v___y_3201_);
                        leanh::lean_dec(v_snd_3193_);
                        leanh::lean_dec(v_fst_3192_);
                        v___y_3185_ = v___x_3204_;
                        v___y_3186_ = v___f_3203_;
                        v___y_3187_ = v___y_3200_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___f_3203_);
                        match leanh::lean_obj_tag(v___y_3201_) {
                            1 => {
                                v_rupHints_3206_ = leanh::lean_ctor_get(v___y_3201_, 2);
                                v_sz_3207_ = lean_array_size(v_rupHints_3206_);
                                v___x_3208_ = 0usize;
                                leanh::lean_inc(v_a_3159_);
                                v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_a_3159_, v_rupHints_3206_, v_sz_3207_, v___x_3208_, v___x_3204_, v___y_3161_, v___y_3200_);
                                v_fst_3210_ = leanh::lean_ctor_get(v___x_3209_, 0);
                                leanh::lean_inc(v_fst_3210_);
                                v_snd_3211_ = leanh::lean_ctor_get(v___x_3209_, 1);
                                leanh::lean_inc(v_snd_3211_);
                                leanh::lean_dec_ref(v___x_3209_);
                                v___x_3212_ = leanh::lean_box(0);
                                v___x_3213_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_3201_, v_fst_3192_, v_snd_3193_, v___y_3198_, v___x_3212_, v_fst_3210_, v___y_3161_, v_snd_3211_);
                                leanh::lean_dec(v_fst_3192_);
                                v___y_3170_ = v___x_3213_;
                                state = 2;
                                continue;
                            }
                            2 => {
                                v_rupHints_3214_ = leanh::lean_ctor_get(v___y_3201_, 3);
                                v_ratHints_3215_ = leanh::lean_ctor_get(v___y_3201_, 4);
                                v_sz_3216_ = lean_array_size(v_rupHints_3214_);
                                v___x_3217_ = 0usize;
                                leanh::lean_inc_n(v_a_3159_, 2);
                                v___x_3218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0(v_a_3159_, v_rupHints_3214_, v_sz_3216_, v___x_3217_, v___x_3204_, v___y_3161_, v___y_3200_);
                                v_fst_3219_ = leanh::lean_ctor_get(v___x_3218_, 0);
                                leanh::lean_inc(v_fst_3219_);
                                v_snd_3220_ = leanh::lean_ctor_get(v___x_3218_, 1);
                                leanh::lean_inc(v_snd_3220_);
                                leanh::lean_dec_ref(v___x_3218_);
                                v_sz_3221_ = lean_array_size(v_ratHints_3215_);
                                v___x_3222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__1(v_a_3159_, v_ratHints_3215_, v_sz_3221_, v___x_3217_, v_fst_3219_, v___y_3161_, v_snd_3220_);
                                v_fst_3223_ = leanh::lean_ctor_get(v___x_3222_, 0);
                                leanh::lean_inc(v_fst_3223_);
                                v_snd_3224_ = leanh::lean_ctor_get(v___x_3222_, 1);
                                leanh::lean_inc(v_snd_3224_);
                                leanh::lean_dec_ref(v___x_3222_);
                                v___x_3225_ = leanh::lean_box(0);
                                v___x_3226_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_3201_, v_fst_3192_, v_snd_3193_, v___y_3198_, v___x_3225_, v_fst_3223_, v___y_3161_, v_snd_3224_);
                                leanh::lean_dec(v_fst_3192_);
                                v___y_3170_ = v___x_3226_;
                                state = 2;
                                continue;
                            }
                            _ => {
                                v___x_3227_ = leanh::lean_box(0);
                                v___x_3228_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___lam__0(v___y_3201_, v_fst_3192_, v_snd_3193_, v___y_3198_, v___x_3227_, v___x_3204_, v___y_3161_, v___y_3200_);
                                leanh::lean_dec(v_fst_3192_);
                                v___y_3170_ = v___x_3228_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3201_);
                    leanh::lean_dec(v_snd_3193_);
                    leanh::lean_dec(v_fst_3192_);
                    v___y_3185_ = v___x_3204_;
                    v___y_3186_ = v___f_3203_;
                    v___y_3187_ = v___y_3200_;
                    state = 5;
                    continue;
                }
            }
            8 => {
                v___x_3236_ = 1;
                v___x_3237_ = lean_uint8_dec_eq(v___y_3235_, v___x_3236_);
                if v___x_3237_ == 0 {
                    if v_isShared_3196_ == 0 {
                        v___x_3239_ = v___x_3195_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3240_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_fst_3192_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_snd_3193_);
                        v___x_3239_ = v_reuseFailAlloc_3240_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_lastUse_3233_);
                    leanh::lean_inc_ref(v_mapped_3232_);
                    leanh::lean_inc_ref(v_used_3231_);
                    leanh::lean_del_object(v___x_3195_);
                    v_isSharedCheck_3253_ = (!leanh::lean_is_exclusive(v___y_3162_)) as u8;
                    if v_isSharedCheck_3253_ == 0 {
                        v_unused_3254_ = leanh::lean_ctor_get(v___y_3162_, 2);
                        leanh::lean_dec(v_unused_3254_);
                        v_unused_3255_ = leanh::lean_ctor_get(v___y_3162_, 1);
                        leanh::lean_dec(v_unused_3255_);
                        v_unused_3256_ = leanh::lean_ctor_get(v___y_3162_, 0);
                        leanh::lean_dec(v_unused_3256_);
                        v___x_3242_ = v___y_3162_;
                        v_isShared_3243_ = v_isSharedCheck_3253_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_3162_);
                        v___x_3242_ = leanh::lean_box(0);
                        v_isShared_3243_ = v_isSharedCheck_3253_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                v_a_3164_ = v___x_3239_;
                v_snd_3165_ = v___y_3162_;
                state = 1;
                continue;
            }
            10 => {
                v___x_3244_ = lean_nat_sub(v_a_3159_, v_initialId_3230_);
                leanh::lean_inc(v_fst_3192_);
                v___x_3245_ = lean_array_set(v_mapped_3232_, v___x_3244_, v_fst_3192_);
                leanh::lean_dec(v___x_3244_);
                if v_isShared_3243_ == 0 {
                    leanh::lean_ctor_set(v___x_3242_, 1, v___x_3245_);
                    v___x_3247_ = v___x_3242_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3252_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_used_3231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 1, v___x_3245_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 2, v_lastUse_3233_);
                    v___x_3247_ = v_reuseFailAlloc_3252_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis_go_spec__1___redArg(v_proof_3229_, v_a_3159_);
                if leanh::lean_obj_tag(v___x_3248_) == 0 {
                    v___x_3249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___closed__4);
                    v___x_3250_ = l_panic___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__2(v___x_3249_);
                    v___y_3198_ = v___x_3237_;
                    v___y_3199_ = v___x_3237_;
                    v___y_3200_ = v___x_3247_;
                    v___y_3201_ = v___x_3250_;
                    state = 7;
                    continue;
                } else {
                    v_val_3251_ = leanh::lean_ctor_get(v___x_3248_, 0);
                    leanh::lean_inc(v_val_3251_);
                    leanh::lean_dec_ref_known(v___x_3248_, 1);
                    v___y_3198_ = v___x_3237_;
                    v___y_3199_ = v___x_3237_;
                    v___y_3200_ = v___x_3247_;
                    v___y_3201_ = v_val_3251_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg___boxed(
    mut v_upperBound_3266_: *mut leanh::LeanObject,
    mut v___x_3267_: *mut leanh::LeanObject,
    mut v_a_3268_: *mut leanh::LeanObject,
    mut v_b_3269_: *mut leanh::LeanObject,
    mut v___y_3270_: *mut leanh::LeanObject,
    mut v___y_3271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3272_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(v_upperBound_3266_, v___x_3267_, v_a_3268_, v_b_3269_, v___y_3270_, v___y_3271_);
    leanh::lean_dec_ref(v___y_3270_);
    leanh::lean_dec(v___x_3267_);
    leanh::lean_dec(v_upperBound_3266_);
    return v_res_3272_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping(
    mut v_a_3275_: *mut leanh::LeanObject,
    mut v_a_3276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_initialId_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addEmptyId_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3291_: u8 = 0;
    let mut v_unused_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_initialId_3277_ = leanh::lean_ctor_get(v_a_3275_, 1);
                v_addEmptyId_3278_ = leanh::lean_ctor_get(v_a_3275_, 2);
                v___x_3279_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping___closed__0;
                leanh::lean_inc_n(v_initialId_3277_, 2);
                v___x_3280_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3280_, 0, v_initialId_3277_);
                leanh::lean_ctor_set(v___x_3280_, 1, v___x_3279_);
                v___x_3281_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(v_addEmptyId_3278_, v_addEmptyId_3278_, v_initialId_3277_, v___x_3280_, v_a_3275_, v_a_3276_);
                v_fst_3282_ = leanh::lean_ctor_get(v___x_3281_, 0);
                leanh::lean_inc(v_fst_3282_);
                v_snd_3283_ = leanh::lean_ctor_get(v___x_3281_, 1);
                leanh::lean_inc(v_snd_3283_);
                leanh::lean_dec_ref(v___x_3281_);
                v_snd_3284_ = leanh::lean_ctor_get(v_fst_3282_, 1);
                v_isSharedCheck_3291_ = (!leanh::lean_is_exclusive(v_fst_3282_)) as u8;
                if v_isSharedCheck_3291_ == 0 {
                    v_unused_3292_ = leanh::lean_ctor_get(v_fst_3282_, 0);
                    leanh::lean_dec(v_unused_3292_);
                    v___x_3286_ = v_fst_3282_;
                    v_isShared_3287_ = v_isSharedCheck_3291_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3284_);
                    leanh::lean_dec(v_fst_3282_);
                    v___x_3286_ = leanh::lean_box(0);
                    v_isShared_3287_ = v_isSharedCheck_3291_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3287_ == 0 {
                    leanh::lean_ctor_set(v___x_3286_, 1, v_snd_3283_);
                    leanh::lean_ctor_set(v___x_3286_, 0, v_snd_3284_);
                    v___x_3289_ = v___x_3286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3290_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_snd_3284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_snd_3283_);
                    v___x_3289_ = v_reuseFailAlloc_3290_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping___boxed(
    mut v_a_3293_: *mut leanh::LeanObject,
    mut v_a_3294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3295_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping(v_a_3293_, v_a_3294_);
    leanh::lean_dec_ref(v_a_3293_);
    return v_res_3295_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3(
    mut v_upperBound_3296_: *mut leanh::LeanObject,
    mut v___x_3297_: *mut leanh::LeanObject,
    mut v_inst_3298_: *mut leanh::LeanObject,
    mut v_R_3299_: *mut leanh::LeanObject,
    mut v_a_3300_: *mut leanh::LeanObject,
    mut v_b_3301_: *mut leanh::LeanObject,
    mut v_c_3302_: *mut leanh::LeanObject,
    mut v___y_3303_: *mut leanh::LeanObject,
    mut v___y_3304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3305_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___redArg(v_upperBound_3296_, v___x_3297_, v_a_3300_, v_b_3301_, v___y_3303_, v___y_3304_);
    return v___x_3305_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3___boxed(
    mut v_upperBound_3306_: *mut leanh::LeanObject,
    mut v___x_3307_: *mut leanh::LeanObject,
    mut v_inst_3308_: *mut leanh::LeanObject,
    mut v_R_3309_: *mut leanh::LeanObject,
    mut v_a_3310_: *mut leanh::LeanObject,
    mut v_b_3311_: *mut leanh::LeanObject,
    mut v_c_3312_: *mut leanh::LeanObject,
    mut v___y_3313_: *mut leanh::LeanObject,
    mut v___y_3314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__3(v_upperBound_3306_, v___x_3307_, v_inst_3308_, v_R_3309_, v_a_3310_, v_b_3311_, v_c_3312_, v___y_3313_, v___y_3314_);
    leanh::lean_dec_ref(v___y_3313_);
    leanh::lean_dec(v___x_3307_);
    leanh::lean_dec(v_upperBound_3306_);
    return v_res_3315_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(
    mut v_next_3316_: *mut leanh::LeanObject,
    mut v_as_3317_: *mut leanh::LeanObject,
    mut v_sz_3318_: usize,
    mut v_i_3319_: usize,
    mut v_b_3320_: *mut leanh::LeanObject,
    mut v___y_3321_: *mut leanh::LeanObject,
    mut v___y_3322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___redArg(v_next_3316_, v_as_3317_, v_sz_3318_, v_i_3319_, v_b_3320_, v___y_3322_);
    return v___x_3323_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0___boxed(
    mut v_next_3324_: *mut leanh::LeanObject,
    mut v_as_3325_: *mut leanh::LeanObject,
    mut v_sz_3326_: *mut leanh::LeanObject,
    mut v_i_3327_: *mut leanh::LeanObject,
    mut v_b_3328_: *mut leanh::LeanObject,
    mut v___y_3329_: *mut leanh::LeanObject,
    mut v___y_3330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3331_: usize = 0;
    let mut v_i_boxed_3332_: usize = 0;
    let mut v_res_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3331_ = leanh::lean_unbox_usize(v_sz_3326_);
    leanh::lean_dec(v_sz_3326_);
    v_i_boxed_3332_ = leanh::lean_unbox_usize(v_i_3327_);
    leanh::lean_dec(v_i_3327_);
    v_res_3333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping_spec__0_spec__0(v_next_3324_, v_as_3325_, v_sz_boxed_3331_, v_i_boxed_3332_, v_b_3328_, v___y_3329_, v___y_3330_);
    leanh::lean_dec_ref(v___y_3329_);
    leanh::lean_dec_ref(v_as_3325_);
    return v_res_3333_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_go(
    mut v_a_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3336_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_useAnalysis(v_a_3334_, v_a_3335_);
    v_snd_3337_ = leanh::lean_ctor_get(v___x_3336_, 1);
    leanh::lean_inc(v_snd_3337_);
    leanh::lean_dec_ref(v___x_3336_);
    v___x_3338_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_mapping(v_a_3334_, v_snd_3337_);
    return v___x_3338_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_go___boxed(
    mut v_a_3339_: *mut leanh::LeanObject,
    mut v_a_3340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3341_ =
        l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_go(
            v_a_3339_, v_a_3340_,
        );
    leanh::lean_dec_ref(v_a_3339_);
    return v_res_3341_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LRAT_trim(
    mut v_proof_3342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3343_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_go___boxed as *mut core::ffi::c_void, 2, 0);
    v___x_3344_ = l___private_Lean_Meta_Tactic_BVDecide_LRAT_Trim_0__Lean_Meta_Tactic_BVDecide_LRAT_trim_M_run___redArg(v_proof_3342_, v___x_3343_);
    return v___x_3344_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LRAT_trim___boxed(
    mut v_proof_3345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3346_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_proof_3345_);
    leanh::lean_dec_ref(v_proof_3345_);
    return v_res_3346_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
}