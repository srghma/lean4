// Lean compiler output
// Module: Lean.Namespace
// Imports: Lean.EnvExtension
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Prelude::{l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed};
use crate::r#gen::Lean::Data::Iterators::Producers::PersistentHashMap::l_Lean_PersistentHashMap_Zipper_prependNode___redArg;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_quickLt;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::SMap::l_Lean_SMap_instInhabited;
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, runtime_initialize_Lean_EnvExtension,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_header, l_Lean_Environment_instBEqVisibility_beq,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::ffi::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::lean_nat_shiftr;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_nat_sub, lean_uint64_of_nat, lean_usize_dec_eq,
};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Namespace_0__Lean_initFn___lam__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Namespace_0__Lean_initFn___lam__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__2_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__2_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__2_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__3_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__2_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__3_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__3_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__4_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__4_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__4_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__5_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__3_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__4_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__5_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__5_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__6_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [78, 97, 109, 101, 115, 112, 97, 99, 101, 0]};
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__6_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__6_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__7_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__5_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__6_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2828215076575793209 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__7_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__7_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__8_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Namespace_0__Lean_initFn___lam__2_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__8_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__8_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__9_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Namespace_0__Lean_initFn___lam__3_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__9_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__9_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__10_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__7_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,870715181848501532 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__10_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__10_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__11_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__10_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__4_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12959053782675887933 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__11_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__11_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__12_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 97, 109, 101, 115, 112, 97, 99, 101, 115, 69, 120, 116, 0]};
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__12_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__12_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__13_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__11_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__12_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18065394951000533458 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__13_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__13_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Namespace_0__Lean_initFn___closed__14_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Namespace_0__Lean_initFn___lam__4_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 2, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__14_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Namespace_0__Lean_initFn___closed__14_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__15_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__15_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__16_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__16_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__17_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__17_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__18_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__18_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__19_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__19_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__20_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Namespace_0__Lean_initFn___closed__20_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Namespace_0__Lean_namespacesExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Environment_registerNamespace___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Environment_registerNamespace___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Environment_registerNamespace___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Environment_registerNamespace___closed__1_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Environment_registerNamespace___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Environment_registerNamespace___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Environment_registerNamespace___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Environment_registerNamespace___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__7___redArg(
    mut v_m_1524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_1525_: u8 = 0;
    let mut v_map_u2081_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1530_: u8 = 0;
    let mut v___x_1531_: u8 = 0;
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1535_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_1525_ = crate::leanh::lean_ctor_get_uint8(
                    v_m_1524_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_1525_ == 0 {
                    return v_m_1524_;
                } else {
                    v_map_u2081_1526_ = crate::leanh::lean_ctor_get(v_m_1524_, 0);
                    v_map_u2082_1527_ = crate::leanh::lean_ctor_get(v_m_1524_, 1);
                    v_isSharedCheck_1535_ = (!crate::leanh::lean_is_exclusive(v_m_1524_)) as u8;
                    if v_isSharedCheck_1535_ == 0 {
                        v___x_1529_ = v_m_1524_;
                        v_isShared_1530_ = v_isSharedCheck_1535_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_1527_);
                        crate::leanh::lean_inc(v_map_u2081_1526_);
                        crate::leanh::lean_dec(v_m_1524_);
                        v___x_1529_ = crate::leanh::lean_box(0);
                        v_isShared_1530_ = v_isSharedCheck_1535_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1531_ = 0;
                if v_isShared_1530_ == 0 {
                    v___x_1533_ = v___x_1529_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1534_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_map_u2081_1526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_map_u2082_1527_);
                    v___x_1533_ = v_reuseFailAlloc_1534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1533_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1531_,
                );
                return v___x_1533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__7(
    mut v_00_u03b2_1536_: *mut crate::leanh::LeanObject,
    mut v_m_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1538_ = l_Lean_SMap_switch___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__7___redArg(v_m_1537_);
    return v___x_1538_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0()
-> u64 {
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: u64 = 0;
    v___x_1539_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1540_ = lean_uint64_of_nat(v___x_1539_);
    return v___x_1540_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg(
    mut v_x_1541_: *mut crate::leanh::LeanObject,
    mut v_x_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1548_: u8 = 0;
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1551_: u64 = 0;
    let mut v___x_1552_: u64 = 0;
    let mut v___x_1553_: u64 = 0;
    let mut v_fold_1554_: u64 = 0;
    let mut v___x_1555_: u64 = 0;
    let mut v___x_1556_: u64 = 0;
    let mut v___x_1557_: u64 = 0;
    let mut v___x_1558_: usize = 0;
    let mut v___x_1559_: usize = 0;
    let mut v___x_1560_: usize = 0;
    let mut v___x_1561_: usize = 0;
    let mut v___x_1562_: usize = 0;
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u64 = 0;
    let mut v_hash_1570_: u64 = 0;
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1542_) == 0 {
                    return v_x_1541_;
                } else {
                    v_key_1543_ = crate::leanh::lean_ctor_get(v_x_1542_, 0);
                    v_value_1544_ = crate::leanh::lean_ctor_get(v_x_1542_, 1);
                    v_tail_1545_ = crate::leanh::lean_ctor_get(v_x_1542_, 2);
                    v_isSharedCheck_1571_ = (!crate::leanh::lean_is_exclusive(v_x_1542_)) as u8;
                    if v_isSharedCheck_1571_ == 0 {
                        v___x_1547_ = v_x_1542_;
                        v_isShared_1548_ = v_isSharedCheck_1571_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1545_);
                        crate::leanh::lean_inc(v_value_1544_);
                        crate::leanh::lean_inc(v_key_1543_);
                        crate::leanh::lean_dec(v_x_1542_);
                        v___x_1547_ = crate::leanh::lean_box(0);
                        v_isShared_1548_ = v_isSharedCheck_1571_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1549_ = lean_array_get_size(v_x_1541_);
                if crate::leanh::lean_obj_tag(v_key_1543_) == 0 {
                    v___x_1569_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0);
                    v___y_1551_ = v___x_1569_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1570_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_1543_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1551_ = v_hash_1570_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1552_ = 32u64;
                v___x_1553_ = lean_uint64_shift_right(v___y_1551_, v___x_1552_);
                v_fold_1554_ = lean_uint64_xor(v___y_1551_, v___x_1553_);
                v___x_1555_ = 16u64;
                v___x_1556_ = lean_uint64_shift_right(v_fold_1554_, v___x_1555_);
                v___x_1557_ = lean_uint64_xor(v_fold_1554_, v___x_1556_);
                v___x_1558_ = lean_uint64_to_usize(v___x_1557_);
                v___x_1559_ = lean_usize_of_nat(v___x_1549_);
                v___x_1560_ = 1usize;
                v___x_1561_ = lean_usize_sub(v___x_1559_, v___x_1560_);
                v___x_1562_ = lean_usize_land(v___x_1558_, v___x_1561_);
                v___x_1563_ = lean_array_uget_borrowed(v_x_1541_, v___x_1562_);
                crate::leanh::lean_inc(v___x_1563_);
                if v_isShared_1548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1547_, 2, v___x_1563_);
                    v___x_1565_ = v___x_1547_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1568_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_key_1543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_value_1544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1568_, 2, v___x_1563_);
                    v___x_1565_ = v_reuseFailAlloc_1568_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1566_ = lean_array_uset(v_x_1541_, v___x_1562_, v___x_1565_);
                v_x_1541_ = v___x_1566_;
                v_x_1542_ = v_tail_1545_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(
    mut v_i_1572_: *mut crate::leanh::LeanObject,
    mut v_source_1573_: *mut crate::leanh::LeanObject,
    mut v_target_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: u8 = 0;
    let mut v_es_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1575_ = lean_array_get_size(v_source_1573_);
                v___x_1576_ = lean_nat_dec_lt(v_i_1572_, v___x_1575_);
                if v___x_1576_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1573_);
                    crate::leanh::lean_dec(v_i_1572_);
                    return v_target_1574_;
                } else {
                    v_es_1577_ = lean_array_fget(v_source_1573_, v_i_1572_);
                    v___x_1578_ = crate::leanh::lean_box(0);
                    v_source_1579_ = lean_array_fset(v_source_1573_, v_i_1572_, v___x_1578_);
                    v_target_1580_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg(v_target_1574_, v_es_1577_);
                    v___x_1581_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1582_ = lean_nat_add(v_i_1572_, v___x_1581_);
                    crate::leanh::lean_dec(v_i_1572_);
                    v_i_1572_ = v___x_1582_;
                    v_source_1573_ = v_source_1579_;
                    v_target_1574_ = v_target_1580_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4___redArg(
    mut v_data_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = lean_array_get_size(v_data_1584_);
    v___x_1586_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1587_ = lean_nat_mul(v___x_1585_, v___x_1586_);
    v___x_1588_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1589_ = crate::leanh::lean_box(0);
    v___x_1590_ = lean_mk_array(v_nbuckets_1587_, v___x_1589_);
    v___x_1591_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v___x_1588_, v_data_1584_, v___x_1590_);
    return v___x_1591_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__1_spec__4___redArg(
    mut v_a_1592_: *mut crate::leanh::LeanObject,
    mut v_b_1593_: *mut crate::leanh::LeanObject,
    mut v_x_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1601_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1594_) == 0 {
                    crate::leanh::lean_dec(v_b_1593_);
                    crate::leanh::lean_dec(v_a_1592_);
                    return v_x_1594_;
                } else {
                    v_key_1595_ = crate::leanh::lean_ctor_get(v_x_1594_, 0);
                    v_value_1596_ = crate::leanh::lean_ctor_get(v_x_1594_, 1);
                    v_tail_1597_ = crate::leanh::lean_ctor_get(v_x_1594_, 2);
                    v_isSharedCheck_1609_ = (!crate::leanh::lean_is_exclusive(v_x_1594_)) as u8;
                    if v_isSharedCheck_1609_ == 0 {
                        v___x_1599_ = v_x_1594_;
                        v_isShared_1600_ = v_isSharedCheck_1609_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1597_);
                        crate::leanh::lean_inc(v_value_1596_);
                        crate::leanh::lean_inc(v_key_1595_);
                        crate::leanh::lean_dec(v_x_1594_);
                        v___x_1599_ = crate::leanh::lean_box(0);
                        v_isShared_1600_ = v_isSharedCheck_1609_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1601_ = lean_name_eq(v_key_1595_, v_a_1592_);
                if v___x_1601_ == 0 {
                    v___x_1602_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__1_spec__4___redArg(v_a_1592_, v_b_1593_, v_tail_1597_);
                    if v_isShared_1600_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1599_, 2, v___x_1602_);
                        v___x_1604_ = v___x_1599_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1605_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_key_1595_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_value_1596_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 2, v___x_1602_);
                        v___x_1604_ = v_reuseFailAlloc_1605_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1596_);
                    crate::leanh::lean_dec(v_key_1595_);
                    if v_isShared_1600_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1599_, 1, v_b_1593_);
                        crate::leanh::lean_ctor_set(v___x_1599_, 0, v_a_1592_);
                        v___x_1607_ = v___x_1599_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1608_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1592_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_b_1593_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_tail_1597_);
                        v___x_1607_ = v_reuseFailAlloc_1608_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1604_;
            }
            3 => {
                return v___x_1607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3___redArg(
    mut v_a_1610_: *mut crate::leanh::LeanObject,
    mut v_x_1611_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1612_: u8 = 0;
    let mut v_key_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1611_) == 0 {
                    v___x_1612_ = 0;
                    return v___x_1612_;
                } else {
                    v_key_1613_ = crate::leanh::lean_ctor_get(v_x_1611_, 0);
                    v_tail_1614_ = crate::leanh::lean_ctor_get(v_x_1611_, 2);
                    v___x_1615_ = lean_name_eq(v_key_1613_, v_a_1610_);
                    if v___x_1615_ == 0 {
                        v_x_1611_ = v_tail_1614_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1615_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(
    mut v_a_1617_: *mut crate::leanh::LeanObject,
    mut v_x_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1619_: u8 = 0;
    let mut v_r_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3___redArg(v_a_1617_, v_x_1618_);
    crate::leanh::lean_dec(v_x_1618_);
    crate::leanh::lean_dec(v_a_1617_);
    v_r_1620_ = crate::leanh::lean_box((v_res_1619_) as usize);
    return v_r_1620_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_m_1621_: *mut crate::leanh::LeanObject,
    mut v_a_1622_: *mut crate::leanh::LeanObject,
    mut v_b_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1631_: u64 = 0;
    let mut v___x_1632_: u64 = 0;
    let mut v___x_1633_: u64 = 0;
    let mut v_fold_1634_: u64 = 0;
    let mut v___x_1635_: u64 = 0;
    let mut v___x_1636_: u64 = 0;
    let mut v___x_1637_: u64 = 0;
    let mut v___x_1638_: usize = 0;
    let mut v___x_1639_: usize = 0;
    let mut v___x_1640_: usize = 0;
    let mut v___x_1641_: usize = 0;
    let mut v___x_1642_: usize = 0;
    let mut v_bkt_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: u8 = 0;
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: u8 = 0;
    let mut v_val_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: u64 = 0;
    let mut v_hash_1670_: u64 = 0;
    let mut v_isSharedCheck_1671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1624_ = crate::leanh::lean_ctor_get(v_m_1621_, 0);
                v_buckets_1625_ = crate::leanh::lean_ctor_get(v_m_1621_, 1);
                v_isSharedCheck_1671_ = (!crate::leanh::lean_is_exclusive(v_m_1621_)) as u8;
                if v_isSharedCheck_1671_ == 0 {
                    v___x_1627_ = v_m_1621_;
                    v_isShared_1628_ = v_isSharedCheck_1671_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1625_);
                    crate::leanh::lean_inc(v_size_1624_);
                    crate::leanh::lean_dec(v_m_1621_);
                    v___x_1627_ = crate::leanh::lean_box(0);
                    v_isShared_1628_ = v_isSharedCheck_1671_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1629_ = lean_array_get_size(v_buckets_1625_);
                if crate::leanh::lean_obj_tag(v_a_1622_) == 0 {
                    v___x_1669_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0);
                    v___y_1631_ = v___x_1669_;
                    state = 2;
                    continue;
                } else {
                    v_hash_1670_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_1622_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1631_ = v_hash_1670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1632_ = 32u64;
                v___x_1633_ = lean_uint64_shift_right(v___y_1631_, v___x_1632_);
                v_fold_1634_ = lean_uint64_xor(v___y_1631_, v___x_1633_);
                v___x_1635_ = 16u64;
                v___x_1636_ = lean_uint64_shift_right(v_fold_1634_, v___x_1635_);
                v___x_1637_ = lean_uint64_xor(v_fold_1634_, v___x_1636_);
                v___x_1638_ = lean_uint64_to_usize(v___x_1637_);
                v___x_1639_ = lean_usize_of_nat(v___x_1629_);
                v___x_1640_ = 1usize;
                v___x_1641_ = lean_usize_sub(v___x_1639_, v___x_1640_);
                v___x_1642_ = lean_usize_land(v___x_1638_, v___x_1641_);
                v_bkt_1643_ = lean_array_uget_borrowed(v_buckets_1625_, v___x_1642_);
                v___x_1644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3___redArg(v_a_1622_, v_bkt_1643_);
                if v___x_1644_ == 0 {
                    v___x_1645_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_1646_ = lean_nat_add(v_size_1624_, v___x_1645_);
                    crate::leanh::lean_dec(v_size_1624_);
                    crate::leanh::lean_inc(v_bkt_1643_);
                    v___x_1647_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1647_, 0, v_a_1622_);
                    crate::leanh::lean_ctor_set(v___x_1647_, 1, v_b_1623_);
                    crate::leanh::lean_ctor_set(v___x_1647_, 2, v_bkt_1643_);
                    v_buckets_x27_1648_ =
                        lean_array_uset(v_buckets_1625_, v___x_1642_, v___x_1647_);
                    v___x_1649_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1650_ = lean_nat_mul(v_size_x27_1646_, v___x_1649_);
                    v___x_1651_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_1652_ = lean_nat_div(v___x_1650_, v___x_1651_);
                    crate::leanh::lean_dec(v___x_1650_);
                    v___x_1653_ = lean_array_get_size(v_buckets_x27_1648_);
                    v___x_1654_ = lean_nat_dec_le(v___x_1652_, v___x_1653_);
                    crate::leanh::lean_dec(v___x_1652_);
                    if v___x_1654_ == 0 {
                        v_val_1655_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4___redArg(v_buckets_x27_1648_);
                        if v_isShared_1628_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1627_, 1, v_val_1655_);
                            crate::leanh::lean_ctor_set(v___x_1627_, 0, v_size_x27_1646_);
                            v___x_1657_ = v___x_1627_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1658_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1658_,
                                0,
                                v_size_x27_1646_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_val_1655_);
                            v___x_1657_ = v_reuseFailAlloc_1658_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_1628_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1627_, 1, v_buckets_x27_1648_);
                            crate::leanh::lean_ctor_set(v___x_1627_, 0, v_size_x27_1646_);
                            v___x_1660_ = v___x_1627_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1661_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1661_,
                                0,
                                v_size_x27_1646_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_1661_,
                                1,
                                v_buckets_x27_1648_,
                            );
                            v___x_1660_ = v_reuseFailAlloc_1661_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_1643_);
                    v___x_1662_ = crate::leanh::lean_box(0);
                    v_buckets_x27_1663_ =
                        lean_array_uset(v_buckets_1625_, v___x_1642_, v___x_1662_);
                    v___x_1664_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__1_spec__4___redArg(v_a_1622_, v_b_1623_, v_bkt_1643_);
                    v___x_1665_ = lean_array_uset(v_buckets_x27_1663_, v___x_1642_, v___x_1664_);
                    if v_isShared_1628_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1627_, 1, v___x_1665_);
                        v___x_1667_ = v___x_1627_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1668_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_size_1624_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1665_);
                        v___x_1667_ = v_reuseFailAlloc_1668_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1657_;
            }
            4 => {
                return v___x_1660_;
            }
            5 => {
                return v___x_1667_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__10_spec__17___redArg(
    mut v_x_1672_: *mut crate::leanh::LeanObject,
    mut v_x_1673_: *mut crate::leanh::LeanObject,
    mut v_x_1674_: *mut crate::leanh::LeanObject,
    mut v_x_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1680_: u8 = 0;
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: u8 = 0;
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1676_ = crate::leanh::lean_ctor_get(v_x_1672_, 0);
                v_vs_1677_ = crate::leanh::lean_ctor_get(v_x_1672_, 1);
                v_isSharedCheck_1701_ = (!crate::leanh::lean_is_exclusive(v_x_1672_)) as u8;
                if v_isSharedCheck_1701_ == 0 {
                    v___x_1679_ = v_x_1672_;
                    v_isShared_1680_ = v_isSharedCheck_1701_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1677_);
                    crate::leanh::lean_inc(v_ks_1676_);
                    crate::leanh::lean_dec(v_x_1672_);
                    v___x_1679_ = crate::leanh::lean_box(0);
                    v_isShared_1680_ = v_isSharedCheck_1701_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1681_ = lean_array_get_size(v_ks_1676_);
                v___x_1682_ = lean_nat_dec_lt(v_x_1673_, v___x_1681_);
                if v___x_1682_ == 0 {
                    crate::leanh::lean_dec(v_x_1673_);
                    v___x_1683_ = lean_array_push(v_ks_1676_, v_x_1674_);
                    v___x_1684_ = lean_array_push(v_vs_1677_, v_x_1675_);
                    if v_isShared_1680_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1679_, 1, v___x_1684_);
                        crate::leanh::lean_ctor_set(v___x_1679_, 0, v___x_1683_);
                        v___x_1686_ = v___x_1679_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1687_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1683_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1684_);
                        v___x_1686_ = v_reuseFailAlloc_1687_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1688_ = lean_array_fget_borrowed(v_ks_1676_, v_x_1673_);
                    v___x_1689_ = lean_name_eq(v_x_1674_, v_k_x27_1688_);
                    if v___x_1689_ == 0 {
                        if v_isShared_1680_ == 0 {
                            v___x_1691_ = v___x_1679_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1695_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_ks_1676_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_vs_1677_);
                            v___x_1691_ = v_reuseFailAlloc_1695_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1696_ = lean_array_fset(v_ks_1676_, v_x_1673_, v_x_1674_);
                        v___x_1697_ = lean_array_fset(v_vs_1677_, v_x_1673_, v_x_1675_);
                        crate::leanh::lean_dec(v_x_1673_);
                        if v_isShared_1680_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1679_, 1, v___x_1697_);
                            crate::leanh::lean_ctor_set(v___x_1679_, 0, v___x_1696_);
                            v___x_1699_ = v___x_1679_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1700_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1696_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1697_);
                            v___x_1699_ = v_reuseFailAlloc_1700_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1686_;
            }
            3 => {
                v___x_1692_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1693_ = lean_nat_add(v_x_1673_, v___x_1692_);
                crate::leanh::lean_dec(v_x_1673_);
                v_x_1672_ = v___x_1691_;
                v_x_1673_ = v___x_1693_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__10___redArg(
    mut v_n_1702_: *mut crate::leanh::LeanObject,
    mut v_k_1703_: *mut crate::leanh::LeanObject,
    mut v_v_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1706_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__10_spec__17___redArg(v_n_1702_, v___x_1705_, v_k_1703_, v_v_1704_);
    return v___x_1706_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_1707_: usize = 0;
    let mut v___x_1708_: usize = 0;
    let mut v___x_1709_: usize = 0;
    v___x_1707_ = 5usize;
    v___x_1708_ = 1usize;
    v___x_1709_ = lean_usize_shift_left(v___x_1708_, v___x_1707_);
    return v___x_1709_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_1710_: usize = 0;
    let mut v___x_1711_: usize = 0;
    let mut v___x_1712_: usize = 0;
    v___x_1710_ = 1usize;
    v___x_1711_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_1712_ = lean_usize_sub(v___x_1711_, v___x_1710_);
    return v___x_1712_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1713_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1713_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(
    mut v_x_1714_: *mut crate::leanh::LeanObject,
    mut v_x_1715_: usize,
    mut v_x_1716_: usize,
    mut v_x_1717_: *mut crate::leanh::LeanObject,
    mut v_x_1718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: usize = 0;
    let mut v___x_1721_: usize = 0;
    let mut v___x_1722_: usize = 0;
    let mut v___x_1723_: usize = 0;
    let mut v_j_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: u8 = 0;
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1729_: u8 = 0;
    let mut v_v_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1743_: u8 = 0;
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut v_node_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1754_: u8 = 0;
    let mut v___x_1755_: usize = 0;
    let mut v___x_1756_: usize = 0;
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1761_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v_unused_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1774_: u8 = 0;
    let mut v_ks_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: usize = 0;
    let mut v___x_1781_: u8 = 0;
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: u8 = 0;
    let mut v_reuseFailAlloc_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1714_) == 0 {
                    v_es_1719_ = crate::leanh::lean_ctor_get(v_x_1714_, 0);
                    v___x_1720_ = 5usize;
                    v___x_1721_ = 1usize;
                    v___x_1722_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_1723_ = lean_usize_land(v_x_1715_, v___x_1722_);
                    v_j_1724_ = lean_usize_to_nat(v___x_1723_);
                    v___x_1725_ = lean_array_get_size(v_es_1719_);
                    v___x_1726_ = lean_nat_dec_lt(v_j_1724_, v___x_1725_);
                    if v___x_1726_ == 0 {
                        crate::leanh::lean_dec(v_j_1724_);
                        crate::leanh::lean_dec(v_x_1718_);
                        crate::leanh::lean_dec(v_x_1717_);
                        return v_x_1714_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1719_);
                        v_isSharedCheck_1763_ = (!crate::leanh::lean_is_exclusive(v_x_1714_)) as u8;
                        if v_isSharedCheck_1763_ == 0 {
                            v_unused_1764_ = crate::leanh::lean_ctor_get(v_x_1714_, 0);
                            crate::leanh::lean_dec(v_unused_1764_);
                            v___x_1728_ = v_x_1714_;
                            v_isShared_1729_ = v_isSharedCheck_1763_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1714_);
                            v___x_1728_ = crate::leanh::lean_box(0);
                            v_isShared_1729_ = v_isSharedCheck_1763_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1765_ = crate::leanh::lean_ctor_get(v_x_1714_, 0);
                    v_vs_1766_ = crate::leanh::lean_ctor_get(v_x_1714_, 1);
                    v_isSharedCheck_1786_ = (!crate::leanh::lean_is_exclusive(v_x_1714_)) as u8;
                    if v_isSharedCheck_1786_ == 0 {
                        v___x_1768_ = v_x_1714_;
                        v_isShared_1769_ = v_isSharedCheck_1786_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1766_);
                        crate::leanh::lean_inc(v_ks_1765_);
                        crate::leanh::lean_dec(v_x_1714_);
                        v___x_1768_ = crate::leanh::lean_box(0);
                        v_isShared_1769_ = v_isSharedCheck_1786_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1730_ = lean_array_fget(v_es_1719_, v_j_1724_);
                v___x_1731_ = crate::leanh::lean_box(0);
                v_xs_x27_1732_ = lean_array_fset(v_es_1719_, v_j_1724_, v___x_1731_);
                match crate::leanh::lean_obj_tag(v_v_1730_) {
                    0 => {
                        v_key_1739_ = crate::leanh::lean_ctor_get(v_v_1730_, 0);
                        v_val_1740_ = crate::leanh::lean_ctor_get(v_v_1730_, 1);
                        v_isSharedCheck_1750_ = (!crate::leanh::lean_is_exclusive(v_v_1730_)) as u8;
                        if v_isSharedCheck_1750_ == 0 {
                            v___x_1742_ = v_v_1730_;
                            v_isShared_1743_ = v_isSharedCheck_1750_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1740_);
                            crate::leanh::lean_inc(v_key_1739_);
                            crate::leanh::lean_dec(v_v_1730_);
                            v___x_1742_ = crate::leanh::lean_box(0);
                            v_isShared_1743_ = v_isSharedCheck_1750_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1751_ = crate::leanh::lean_ctor_get(v_v_1730_, 0);
                        v_isSharedCheck_1761_ = (!crate::leanh::lean_is_exclusive(v_v_1730_)) as u8;
                        if v_isSharedCheck_1761_ == 0 {
                            v___x_1753_ = v_v_1730_;
                            v_isShared_1754_ = v_isSharedCheck_1761_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1751_);
                            crate::leanh::lean_dec(v_v_1730_);
                            v___x_1753_ = crate::leanh::lean_box(0);
                            v_isShared_1754_ = v_isSharedCheck_1761_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1762_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1762_, 0, v_x_1717_);
                        crate::leanh::lean_ctor_set(v___x_1762_, 1, v_x_1718_);
                        v___y_1734_ = v___x_1762_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1735_ = lean_array_fset(v_xs_x27_1732_, v_j_1724_, v___y_1734_);
                crate::leanh::lean_dec(v_j_1724_);
                if v_isShared_1729_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1728_, 0, v___x_1735_);
                    v___x_1737_ = v___x_1728_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
                    v___x_1737_ = v_reuseFailAlloc_1738_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1737_;
            }
            4 => {
                v___x_1744_ = lean_name_eq(v_x_1717_, v_key_1739_);
                if v___x_1744_ == 0 {
                    crate::leanh::lean_del_object(v___x_1742_);
                    v___x_1745_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1739_,
                        v_val_1740_,
                        v_x_1717_,
                        v_x_1718_,
                    );
                    v___x_1746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1746_, 0, v___x_1745_);
                    v___y_1734_ = v___x_1746_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1740_);
                    crate::leanh::lean_dec(v_key_1739_);
                    if v_isShared_1743_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1742_, 1, v_x_1718_);
                        crate::leanh::lean_ctor_set(v___x_1742_, 0, v_x_1717_);
                        v___x_1748_ = v___x_1742_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1749_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_x_1717_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_x_1718_);
                        v___x_1748_ = v_reuseFailAlloc_1749_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1734_ = v___x_1748_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1755_ = lean_usize_shift_right(v_x_1715_, v___x_1720_);
                v___x_1756_ = lean_usize_add(v_x_1716_, v___x_1721_);
                v___x_1757_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_node_1751_, v___x_1755_, v___x_1756_, v_x_1717_, v_x_1718_);
                if v_isShared_1754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1753_, 0, v___x_1757_);
                    v___x_1759_ = v___x_1753_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
                    v___x_1759_ = v_reuseFailAlloc_1760_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1734_ = v___x_1759_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1769_ == 0 {
                    v___x_1771_ = v___x_1768_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1785_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_ks_1765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_vs_1766_);
                    v___x_1771_ = v_reuseFailAlloc_1785_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1772_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__10___redArg(v___x_1771_, v_x_1717_, v_x_1718_);
                v___x_1780_ = 7usize;
                v___x_1781_ = lean_usize_dec_le(v___x_1780_, v_x_1716_);
                if v___x_1781_ == 0 {
                    v___x_1782_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1772_);
                    v___x_1783_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1784_ = lean_nat_dec_lt(v___x_1782_, v___x_1783_);
                    crate::leanh::lean_dec(v___x_1782_);
                    v___y_1774_ = v___x_1784_;
                    state = 10;
                    continue;
                } else {
                    v___y_1774_ = v___x_1781_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1774_ == 0 {
                    v_ks_1775_ = crate::leanh::lean_ctor_get(v_newNode_1772_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1775_);
                    v_vs_1776_ = crate::leanh::lean_ctor_get(v_newNode_1772_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1776_);
                    crate::leanh::lean_dec_ref(v_newNode_1772_);
                    v___x_1777_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1778_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_1779_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__11___redArg(v_x_1716_, v_ks_1775_, v_vs_1776_, v___x_1777_, v___x_1778_);
                    crate::leanh::lean_dec_ref(v_vs_1776_);
                    crate::leanh::lean_dec_ref(v_ks_1775_);
                    return v___x_1779_;
                } else {
                    return v_newNode_1772_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__11___redArg(
    mut v_depth_1787_: usize,
    mut v_keys_1788_: *mut crate::leanh::LeanObject,
    mut v_vals_1789_: *mut crate::leanh::LeanObject,
    mut v_i_1790_: *mut crate::leanh::LeanObject,
    mut v_entries_1791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v_k_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1797_: u64 = 0;
    let mut v_h_1798_: usize = 0;
    let mut v___x_1799_: usize = 0;
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: usize = 0;
    let mut v___x_1802_: usize = 0;
    let mut v___x_1803_: usize = 0;
    let mut v_h_1804_: usize = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: u64 = 0;
    let mut v_hash_1809_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1792_ = lean_array_get_size(v_keys_1788_);
                v___x_1793_ = lean_nat_dec_lt(v_i_1790_, v___x_1792_);
                if v___x_1793_ == 0 {
                    crate::leanh::lean_dec(v_i_1790_);
                    return v_entries_1791_;
                } else {
                    v_k_1794_ = lean_array_fget_borrowed(v_keys_1788_, v_i_1790_);
                    v_v_1795_ = lean_array_fget_borrowed(v_vals_1789_, v_i_1790_);
                    if crate::leanh::lean_obj_tag(v_k_1794_) == 0 {
                        v___x_1808_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0);
                        v___y_1797_ = v___x_1808_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_1809_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_1794_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_1797_ = v_hash_1809_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_1798_ = lean_uint64_to_usize(v___y_1797_);
                v___x_1799_ = 5usize;
                v___x_1800_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1801_ = 1usize;
                v___x_1802_ = lean_usize_sub(v_depth_1787_, v___x_1801_);
                v___x_1803_ = lean_usize_mul(v___x_1799_, v___x_1802_);
                v_h_1804_ = lean_usize_shift_right(v_h_1798_, v___x_1803_);
                v___x_1805_ = lean_nat_add(v_i_1790_, v___x_1800_);
                crate::leanh::lean_dec(v_i_1790_);
                crate::leanh::lean_inc(v_v_1795_);
                crate::leanh::lean_inc(v_k_1794_);
                v___x_1806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_entries_1791_, v_h_1804_, v_depth_1787_, v_k_1794_, v_v_1795_);
                v_i_1790_ = v___x_1805_;
                v_entries_1791_ = v___x_1806_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__11___redArg___boxed(
    mut v_depth_1810_: *mut crate::leanh::LeanObject,
    mut v_keys_1811_: *mut crate::leanh::LeanObject,
    mut v_vals_1812_: *mut crate::leanh::LeanObject,
    mut v_i_1813_: *mut crate::leanh::LeanObject,
    mut v_entries_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1815_: usize = 0;
    let mut v_res_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1815_ = crate::leanh::lean_unbox_usize(v_depth_1810_);
    crate::leanh::lean_dec(v_depth_1810_);
    v_res_1816_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__11___redArg(v_depth_boxed_1815_, v_keys_1811_, v_vals_1812_, v_i_1813_, v_entries_1814_);
    crate::leanh::lean_dec_ref(v_vals_1812_);
    crate::leanh::lean_dec_ref(v_keys_1811_);
    return v_res_1816_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_1817_: *mut crate::leanh::LeanObject,
    mut v_x_1818_: *mut crate::leanh::LeanObject,
    mut v_x_1819_: *mut crate::leanh::LeanObject,
    mut v_x_1820_: *mut crate::leanh::LeanObject,
    mut v_x_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4807__boxed_1822_: usize = 0;
    let mut v_x_4808__boxed_1823_: usize = 0;
    let mut v_res_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4807__boxed_1822_ = crate::leanh::lean_unbox_usize(v_x_1818_);
    crate::leanh::lean_dec(v_x_1818_);
    v_x_4808__boxed_1823_ = crate::leanh::lean_unbox_usize(v_x_1819_);
    crate::leanh::lean_dec(v_x_1819_);
    v_res_1824_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_x_1817_, v_x_4807__boxed_1822_, v_x_4808__boxed_1823_, v_x_1820_, v_x_1821_);
    return v_res_1824_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_1825_: *mut crate::leanh::LeanObject,
    mut v_x_1826_: *mut crate::leanh::LeanObject,
    mut v_x_1827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1829_: u64 = 0;
    let mut v___x_1830_: usize = 0;
    let mut v___x_1831_: usize = 0;
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: u64 = 0;
    let mut v_hash_1834_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1826_) == 0 {
                    v___x_1833_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0);
                    v___y_1829_ = v___x_1833_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1834_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_1826_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1829_ = v_hash_1834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1830_ = lean_uint64_to_usize(v___y_1829_);
                v___x_1831_ = 1usize;
                v___x_1832_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_x_1825_, v___x_1830_, v___x_1831_, v_x_1826_, v_x_1827_);
                return v___x_1832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0___redArg(
    mut v_x_1835_: *mut crate::leanh::LeanObject,
    mut v_x_1836_: *mut crate::leanh::LeanObject,
    mut v_x_1837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_1838_: u8 = 0;
    let mut v_map_u2081_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1848_: u8 = 0;
    let mut v_map_u2081_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_1838_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_1835_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_1838_ == 0 {
                    v_map_u2081_1839_ = crate::leanh::lean_ctor_get(v_x_1835_, 0);
                    v_map_u2082_1840_ = crate::leanh::lean_ctor_get(v_x_1835_, 1);
                    v_isSharedCheck_1848_ = (!crate::leanh::lean_is_exclusive(v_x_1835_)) as u8;
                    if v_isSharedCheck_1848_ == 0 {
                        v___x_1842_ = v_x_1835_;
                        v_isShared_1843_ = v_isSharedCheck_1848_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_1840_);
                        crate::leanh::lean_inc(v_map_u2081_1839_);
                        crate::leanh::lean_dec(v_x_1835_);
                        v___x_1842_ = crate::leanh::lean_box(0);
                        v_isShared_1843_ = v_isSharedCheck_1848_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_1849_ = crate::leanh::lean_ctor_get(v_x_1835_, 0);
                    v_map_u2082_1850_ = crate::leanh::lean_ctor_get(v_x_1835_, 1);
                    v_isSharedCheck_1858_ = (!crate::leanh::lean_is_exclusive(v_x_1835_)) as u8;
                    if v_isSharedCheck_1858_ == 0 {
                        v___x_1852_ = v_x_1835_;
                        v_isShared_1853_ = v_isSharedCheck_1858_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_u2082_1850_);
                        crate::leanh::lean_inc(v_map_u2081_1849_);
                        crate::leanh::lean_dec(v_x_1835_);
                        v___x_1852_ = crate::leanh::lean_box(0);
                        v_isShared_1853_ = v_isSharedCheck_1858_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1844_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_u2082_1840_, v_x_1836_, v_x_1837_);
                if v_isShared_1843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1842_, 1, v___x_1844_);
                    v___x_1846_ = v___x_1842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1847_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_map_u2081_1839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1844_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1847_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_1838_,
                    );
                    v___x_1846_ = v_reuseFailAlloc_1847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1846_;
            }
            3 => {
                v___x_1854_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__1___redArg(v_map_u2081_1849_, v_x_1836_, v_x_1837_);
                if v_isShared_1853_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1852_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1852_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_map_u2082_1850_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1857_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_1838_,
                    );
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1856_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(
    mut v_s_1859_: *mut crate::leanh::LeanObject,
    mut v_n_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1861_: u8 = 0;
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = 1;
    v___x_1862_ = crate::leanh::lean_box((v___x_1861_) as usize);
    v___x_1863_ = l_Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0___redArg(v_s_1859_, v_n_1860_, v___x_1862_);
    return v___x_1863_;
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(
    mut v_x_1864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1865_ = crate::leanh::lean_box(0);
    return v___x_1865_;
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed(
    mut v_x_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l___private_Lean_Namespace_0__Lean_initFn___lam__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(v_x_1866_);
    crate::leanh::lean_dec_ref(v_x_1866_);
    return v_res_1867_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___lam__0(
    mut v_ps_1868_: *mut crate::leanh::LeanObject,
    mut v_k_1869_: *mut crate::leanh::LeanObject,
    mut v_v_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1871_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1871_, 0, v_k_1869_);
    crate::leanh::lean_ctor_set(v___x_1871_, 1, v_v_1870_);
    v___x_1872_ = lean_array_push(v_ps_1868_, v___x_1871_);
    return v___x_1872_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__25___redArg(
    mut v_f_1873_: *mut crate::leanh::LeanObject,
    mut v_keys_1874_: *mut crate::leanh::LeanObject,
    mut v_vals_1875_: *mut crate::leanh::LeanObject,
    mut v_i_1876_: *mut crate::leanh::LeanObject,
    mut v_acc_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v_k_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1878_ = lean_array_get_size(v_keys_1874_);
                v___x_1879_ = lean_nat_dec_lt(v_i_1876_, v___x_1878_);
                if v___x_1879_ == 0 {
                    crate::leanh::lean_dec(v_i_1876_);
                    crate::leanh::lean_dec(v_f_1873_);
                    return v_acc_1877_;
                } else {
                    v_k_1880_ = lean_array_fget_borrowed(v_keys_1874_, v_i_1876_);
                    v_v_1881_ = lean_array_fget_borrowed(v_vals_1875_, v_i_1876_);
                    crate::leanh::lean_inc(v_f_1873_);
                    crate::leanh::lean_inc(v_v_1881_);
                    crate::leanh::lean_inc(v_k_1880_);
                    v___x_1882_ =
                        crate::leanh::lean_apply_3(v_f_1873_, v_acc_1877_, v_k_1880_, v_v_1881_);
                    v___x_1883_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1884_ = lean_nat_add(v_i_1876_, v___x_1883_);
                    crate::leanh::lean_dec(v_i_1876_);
                    v_i_1876_ = v___x_1884_;
                    v_acc_1877_ = v___x_1882_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__25___redArg___boxed(
    mut v_f_1886_: *mut crate::leanh::LeanObject,
    mut v_keys_1887_: *mut crate::leanh::LeanObject,
    mut v_vals_1888_: *mut crate::leanh::LeanObject,
    mut v_i_1889_: *mut crate::leanh::LeanObject,
    mut v_acc_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1891_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__25___redArg(v_f_1886_, v_keys_1887_, v_vals_1888_, v_i_1889_, v_acc_1890_);
    crate::leanh::lean_dec_ref(v_vals_1888_);
    crate::leanh::lean_dec_ref(v_keys_1887_);
    return v_res_1891_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21___redArg(
    mut v_f_1892_: *mut crate::leanh::LeanObject,
    mut v_x_1893_: *mut crate::leanh::LeanObject,
    mut v_x_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1893_) == 0 {
        let mut v_es_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: u8 = 0;
        v_es_1895_ = crate::leanh::lean_ctor_get(v_x_1893_, 0);
        v___x_1896_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1897_ = lean_array_get_size(v_es_1895_);
        v___x_1898_ = lean_nat_dec_lt(v___x_1896_, v___x_1897_);
        if v___x_1898_ == 0 {
            crate::leanh::lean_dec(v_f_1892_);
            return v_x_1894_;
        } else {
            let mut v___x_1899_: u8 = 0;
            v___x_1899_ = lean_nat_dec_le(v___x_1897_, v___x_1897_);
            if v___x_1899_ == 0 {
                if v___x_1898_ == 0 {
                    crate::leanh::lean_dec(v_f_1892_);
                    return v_x_1894_;
                } else {
                    let mut v___x_1900_: usize = 0;
                    let mut v___x_1901_: usize = 0;
                    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1900_ = 0usize;
                    v___x_1901_ = lean_usize_of_nat(v___x_1897_);
                    v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__24___redArg(v_f_1892_, v_es_1895_, v___x_1900_, v___x_1901_, v_x_1894_);
                    return v___x_1902_;
                }
            } else {
                let mut v___x_1903_: usize = 0;
                let mut v___x_1904_: usize = 0;
                let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1903_ = 0usize;
                v___x_1904_ = lean_usize_of_nat(v___x_1897_);
                v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__24___redArg(v_f_1892_, v_es_1895_, v___x_1903_, v___x_1904_, v_x_1894_);
                return v___x_1905_;
            }
        }
    } else {
        let mut v_ks_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_1906_ = crate::leanh::lean_ctor_get(v_x_1893_, 0);
        v_vs_1907_ = crate::leanh::lean_ctor_get(v_x_1893_, 1);
        v___x_1908_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1909_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__25___redArg(v_f_1892_, v_ks_1906_, v_vs_1907_, v___x_1908_, v_x_1894_);
        return v___x_1909_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__24___redArg(
    mut v_f_1910_: *mut crate::leanh::LeanObject,
    mut v_as_1911_: *mut crate::leanh::LeanObject,
    mut v_i_1912_: usize,
    mut v_stop_1913_: usize,
    mut v_b_1914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: usize = 0;
    let mut v___x_1918_: usize = 0;
    let mut v___x_1920_: u8 = 0;
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1920_ = lean_usize_dec_eq(v_i_1912_, v_stop_1913_);
                if v___x_1920_ == 0 {
                    v___x_1921_ = lean_array_uget_borrowed(v_as_1911_, v_i_1912_);
                    match crate::leanh::lean_obj_tag(v___x_1921_) {
                        0 => {
                            v_key_1922_ = crate::leanh::lean_ctor_get(v___x_1921_, 0);
                            v_val_1923_ = crate::leanh::lean_ctor_get(v___x_1921_, 1);
                            crate::leanh::lean_inc(v_f_1910_);
                            crate::leanh::lean_inc(v_val_1923_);
                            crate::leanh::lean_inc(v_key_1922_);
                            v___x_1924_ = crate::leanh::lean_apply_3(
                                v_f_1910_,
                                v_b_1914_,
                                v_key_1922_,
                                v_val_1923_,
                            );
                            v___y_1916_ = v___x_1924_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_1925_ = crate::leanh::lean_ctor_get(v___x_1921_, 0);
                            crate::leanh::lean_inc(v_f_1910_);
                            v___x_1926_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21___redArg(v_f_1910_, v_node_1925_, v_b_1914_);
                            v___y_1916_ = v___x_1926_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_1916_ = v_b_1914_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_f_1910_);
                    return v_b_1914_;
                }
            }
            1 => {
                v___x_1917_ = 1usize;
                v___x_1918_ = lean_usize_add(v_i_1912_, v___x_1917_);
                v_i_1912_ = v___x_1918_;
                v_b_1914_ = v___y_1916_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__24___redArg___boxed(
    mut v_f_1927_: *mut crate::leanh::LeanObject,
    mut v_as_1928_: *mut crate::leanh::LeanObject,
    mut v_i_1929_: *mut crate::leanh::LeanObject,
    mut v_stop_1930_: *mut crate::leanh::LeanObject,
    mut v_b_1931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1932_: usize = 0;
    let mut v_stop_boxed_1933_: usize = 0;
    let mut v_res_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1932_ = crate::leanh::lean_unbox_usize(v_i_1929_);
    crate::leanh::lean_dec(v_i_1929_);
    v_stop_boxed_1933_ = crate::leanh::lean_unbox_usize(v_stop_1930_);
    crate::leanh::lean_dec(v_stop_1930_);
    v_res_1934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__24___redArg(v_f_1927_, v_as_1928_, v_i_boxed_1932_, v_stop_boxed_1933_, v_b_1931_);
    crate::leanh::lean_dec_ref(v_as_1928_);
    return v_res_1934_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21___redArg___boxed(
    mut v_f_1935_: *mut crate::leanh::LeanObject,
    mut v_x_1936_: *mut crate::leanh::LeanObject,
    mut v_x_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1938_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21___redArg(v_f_1935_, v_x_1936_, v_x_1937_);
    crate::leanh::lean_dec_ref(v_x_1936_);
    return v_res_1938_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8___redArg___lam__0(
    mut v_f_1939_: *mut crate::leanh::LeanObject,
    mut v_x1_1940_: *mut crate::leanh::LeanObject,
    mut v_x2_1941_: *mut crate::leanh::LeanObject,
    mut v_x3_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1943_ = crate::leanh::lean_apply_3(v_f_1939_, v_x1_1940_, v_x2_1941_, v_x3_1942_);
    return v___x_1943_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8___redArg(
    mut v_map_1944_: *mut crate::leanh::LeanObject,
    mut v_f_1945_: *mut crate::leanh::LeanObject,
    mut v_init_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1947_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_1947_, 0, v_f_1945_);
    v___x_1948_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21___redArg(v___f_1947_, v_map_1944_, v_init_1946_);
    return v___x_1948_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8___redArg___boxed(
    mut v_map_1949_: *mut crate::leanh::LeanObject,
    mut v_f_1950_: *mut crate::leanh::LeanObject,
    mut v_init_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8___redArg(v_map_1949_, v_f_1950_, v_init_1951_);
    crate::leanh::lean_dec_ref(v_map_1949_);
    return v_res_1952_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg(
    mut v_m_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1957_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___closed__0;
    v___x_1958_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___closed__1;
    v___x_1959_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8___redArg(v_m_1956_, v___f_1957_, v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg___boxed(
    mut v_m_1960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1961_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg(v_m_1960_);
    crate::leanh::lean_dec_ref(v_m_1960_);
    return v_res_1961_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__4(
    mut v_sz_1962_: usize,
    mut v_i_1963_: usize,
    mut v_bs_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1965_: u8 = 0;
    let mut v_v_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: usize = 0;
    let mut v___x_1971_: usize = 0;
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1965_ = lean_usize_dec_lt(v_i_1963_, v_sz_1962_);
                if v___x_1965_ == 0 {
                    return v_bs_1964_;
                } else {
                    v_v_1966_ = lean_array_uget_borrowed(v_bs_1964_, v_i_1963_);
                    v_fst_1967_ = crate::leanh::lean_ctor_get(v_v_1966_, 0);
                    crate::leanh::lean_inc(v_fst_1967_);
                    v___x_1968_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1969_ = lean_array_uset(v_bs_1964_, v_i_1963_, v___x_1968_);
                    v___x_1970_ = 1usize;
                    v___x_1971_ = lean_usize_add(v_i_1963_, v___x_1970_);
                    v___x_1972_ = lean_array_uset(v_bs_x27_1969_, v_i_1963_, v_fst_1967_);
                    v_i_1963_ = v___x_1971_;
                    v_bs_1964_ = v___x_1972_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__4___boxed(
    mut v_sz_1974_: *mut crate::leanh::LeanObject,
    mut v_i_1975_: *mut crate::leanh::LeanObject,
    mut v_bs_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1977_: usize = 0;
    let mut v_i_boxed_1978_: usize = 0;
    let mut v_res_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1977_ = crate::leanh::lean_unbox_usize(v_sz_1974_);
    crate::leanh::lean_dec(v_sz_1974_);
    v_i_boxed_1978_ = crate::leanh::lean_unbox_usize(v_i_1975_);
    crate::leanh::lean_dec(v_i_1975_);
    v_res_1979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__4(v_sz_boxed_1977_, v_i_boxed_1978_, v_bs_1976_);
    return v_res_1979_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5_spec__11___redArg(
    mut v_hi_1980_: *mut crate::leanh::LeanObject,
    mut v_pivot_1981_: *mut crate::leanh::LeanObject,
    mut v_as_1982_: *mut crate::leanh::LeanObject,
    mut v_i_1983_: *mut crate::leanh::LeanObject,
    mut v_k_1984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: u8 = 0;
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1985_ = lean_nat_dec_lt(v_k_1984_, v_hi_1980_);
                if v___x_1985_ == 0 {
                    crate::leanh::lean_dec(v_k_1984_);
                    v___x_1986_ = lean_array_fswap(v_as_1982_, v_i_1983_, v_hi_1980_);
                    v___x_1987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1987_, 0, v_i_1983_);
                    crate::leanh::lean_ctor_set(v___x_1987_, 1, v___x_1986_);
                    return v___x_1987_;
                } else {
                    v___x_1988_ = lean_array_fget_borrowed(v_as_1982_, v_k_1984_);
                    v___x_1989_ = l_Lean_Name_quickLt(v___x_1988_, v_pivot_1981_);
                    if v___x_1989_ == 0 {
                        v___x_1990_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1991_ = lean_nat_add(v_k_1984_, v___x_1990_);
                        crate::leanh::lean_dec(v_k_1984_);
                        v_k_1984_ = v___x_1991_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1993_ = lean_array_fswap(v_as_1982_, v_i_1983_, v_k_1984_);
                        v___x_1994_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1995_ = lean_nat_add(v_i_1983_, v___x_1994_);
                        crate::leanh::lean_dec(v_i_1983_);
                        v___x_1996_ = lean_nat_add(v_k_1984_, v___x_1994_);
                        crate::leanh::lean_dec(v_k_1984_);
                        v_as_1982_ = v___x_1993_;
                        v_i_1983_ = v___x_1995_;
                        v_k_1984_ = v___x_1996_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5_spec__11___redArg___boxed(
    mut v_hi_1998_: *mut crate::leanh::LeanObject,
    mut v_pivot_1999_: *mut crate::leanh::LeanObject,
    mut v_as_2000_: *mut crate::leanh::LeanObject,
    mut v_i_2001_: *mut crate::leanh::LeanObject,
    mut v_k_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2003_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5_spec__11___redArg(v_hi_1998_, v_pivot_1999_, v_as_2000_, v_i_2001_, v_k_2002_);
    crate::leanh::lean_dec(v_pivot_1999_);
    crate::leanh::lean_dec(v_hi_1998_);
    return v_res_2003_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5___redArg(
    mut v_n_2004_: *mut crate::leanh::LeanObject,
    mut v_as_2005_: *mut crate::leanh::LeanObject,
    mut v_lo_2006_: *mut crate::leanh::LeanObject,
    mut v_hi_2007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: u8 = 0;
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: u8 = 0;
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2019_ = lean_nat_dec_lt(v_lo_2006_, v_hi_2007_);
                if v___x_2019_ == 0 {
                    crate::leanh::lean_dec(v_lo_2006_);
                    return v_as_2005_;
                } else {
                    v___x_2020_ = lean_nat_add(v_lo_2006_, v_hi_2007_);
                    v___x_2021_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_2022_ = lean_nat_shiftr(v___x_2020_, v___x_2021_);
                    crate::leanh::lean_dec(v___x_2020_);
                    v___x_2035_ = lean_array_fget_borrowed(v_as_2005_, v_mid_2022_);
                    v___x_2036_ = lean_array_fget_borrowed(v_as_2005_, v_lo_2006_);
                    v___x_2037_ = l_Lean_Name_quickLt(v___x_2035_, v___x_2036_);
                    if v___x_2037_ == 0 {
                        v___y_2030_ = v_as_2005_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2038_ = lean_array_fswap(v_as_2005_, v_lo_2006_, v_mid_2022_);
                        v___y_2030_ = v___x_2038_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2010_ = lean_array_fget(v___y_2009_, v_hi_2007_);
                crate::leanh::lean_inc_n(v_lo_2006_, 2);
                v___x_2011_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5_spec__11___redArg(v_hi_2007_, v_pivot_2010_, v___y_2009_, v_lo_2006_, v_lo_2006_);
                crate::leanh::lean_dec(v_pivot_2010_);
                v_fst_2012_ = crate::leanh::lean_ctor_get(v___x_2011_, 0);
                crate::leanh::lean_inc(v_fst_2012_);
                v_snd_2013_ = crate::leanh::lean_ctor_get(v___x_2011_, 1);
                crate::leanh::lean_inc(v_snd_2013_);
                crate::leanh::lean_dec_ref(v___x_2011_);
                v___x_2014_ = lean_nat_dec_le(v_hi_2007_, v_fst_2012_);
                if v___x_2014_ == 0 {
                    v___x_2015_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5___redArg(v_n_2004_, v_snd_2013_, v_lo_2006_, v_fst_2012_);
                    v___x_2016_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2017_ = lean_nat_add(v_fst_2012_, v___x_2016_);
                    crate::leanh::lean_dec(v_fst_2012_);
                    v_as_2005_ = v___x_2015_;
                    v_lo_2006_ = v___x_2017_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_2012_);
                    crate::leanh::lean_dec(v_lo_2006_);
                    return v_snd_2013_;
                }
            }
            2 => {
                v___x_2025_ = lean_array_fget_borrowed(v___y_2024_, v_mid_2022_);
                v___x_2026_ = lean_array_fget_borrowed(v___y_2024_, v_hi_2007_);
                v___x_2027_ = l_Lean_Name_quickLt(v___x_2025_, v___x_2026_);
                if v___x_2027_ == 0 {
                    crate::leanh::lean_dec(v_mid_2022_);
                    v___y_2009_ = v___y_2024_;
                    state = 1;
                    continue;
                } else {
                    v___x_2028_ = lean_array_fswap(v___y_2024_, v_mid_2022_, v_hi_2007_);
                    crate::leanh::lean_dec(v_mid_2022_);
                    v___y_2009_ = v___x_2028_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2031_ = lean_array_fget_borrowed(v___y_2030_, v_hi_2007_);
                v___x_2032_ = lean_array_fget_borrowed(v___y_2030_, v_lo_2006_);
                v___x_2033_ = l_Lean_Name_quickLt(v___x_2031_, v___x_2032_);
                if v___x_2033_ == 0 {
                    v___y_2024_ = v___y_2030_;
                    state = 2;
                    continue;
                } else {
                    v___x_2034_ = lean_array_fswap(v___y_2030_, v_lo_2006_, v_hi_2007_);
                    v___y_2024_ = v___x_2034_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5___redArg___boxed(
    mut v_n_2039_: *mut crate::leanh::LeanObject,
    mut v_as_2040_: *mut crate::leanh::LeanObject,
    mut v_lo_2041_: *mut crate::leanh::LeanObject,
    mut v_hi_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2043_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5___redArg(v_n_2039_, v_as_2040_, v_lo_2041_, v_hi_2042_);
    crate::leanh::lean_dec(v_hi_2042_);
    crate::leanh::lean_dec(v_n_2039_);
    return v_res_2043_;
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__2_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(
    mut v___x_2044_: *mut crate::leanh::LeanObject,
    mut v_s_2045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2082_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2048_: usize = 0;
    let mut v___x_2049_: usize = 0;
    let mut v_entries_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_u2082_2046_ = crate::leanh::lean_ctor_get(v_s_2045_, 1);
                v___x_2047_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg(v_map_u2082_2046_);
                v_sz_2048_ = lean_array_size(v___x_2047_);
                v___x_2049_ = 0usize;
                v_entries_2050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__4(v_sz_2048_, v___x_2049_, v___x_2047_);
                v___x_2051_ = lean_array_get_size(v_entries_2050_);
                v___x_2052_ = lean_nat_dec_eq(v___x_2051_, v___x_2044_);
                if v___x_2052_ == 0 {
                    v___x_2053_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2054_ = lean_nat_sub(v___x_2051_, v___x_2053_);
                    v___x_2060_ = lean_nat_dec_le(v___x_2044_, v___x_2054_);
                    if v___x_2060_ == 0 {
                        crate::leanh::lean_dec(v___x_2044_);
                        crate::leanh::lean_inc(v___x_2054_);
                        v___y_2056_ = v___x_2054_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2056_ = v___x_2044_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2044_);
                    return v_entries_2050_;
                }
            }
            1 => {
                v___x_2057_ = lean_nat_dec_le(v___y_2056_, v___x_2054_);
                if v___x_2057_ == 0 {
                    crate::leanh::lean_dec(v___x_2054_);
                    crate::leanh::lean_inc(v___y_2056_);
                    v___x_2058_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5___redArg(v___x_2051_, v_entries_2050_, v___y_2056_, v___y_2056_);
                    crate::leanh::lean_dec(v___y_2056_);
                    return v___x_2058_;
                } else {
                    v___x_2059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5___redArg(v___x_2051_, v_entries_2050_, v___y_2056_, v___x_2054_);
                    crate::leanh::lean_dec(v___x_2054_);
                    return v___x_2059_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__2_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed(
    mut v___x_2061_: *mut crate::leanh::LeanObject,
    mut v_s_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2063_ = l___private_Lean_Namespace_0__Lean_initFn___lam__2_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(v___x_2061_, v_s_2062_);
    crate::leanh::lean_dec_ref(v_s_2062_);
    return v_res_2063_;
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__3_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(
    mut v___x_2064_: *mut crate::leanh::LeanObject,
    mut v_x_2065_: *mut crate::leanh::LeanObject,
    mut v_s_2066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2082_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2069_: usize = 0;
    let mut v___x_2070_: usize = 0;
    let mut v_entries_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_u2082_2067_ = crate::leanh::lean_ctor_get(v_s_2066_, 1);
                v___x_2068_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg(v_map_u2082_2067_);
                v_sz_2069_ = lean_array_size(v___x_2068_);
                v___x_2070_ = 0usize;
                v_entries_2071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__4(v_sz_2069_, v___x_2070_, v___x_2068_);
                v___x_2072_ = lean_array_get_size(v_entries_2071_);
                v___x_2078_ = lean_nat_dec_eq(v___x_2072_, v___x_2064_);
                if v___x_2078_ == 0 {
                    v___x_2079_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2080_ = lean_nat_sub(v___x_2072_, v___x_2079_);
                    v___x_2084_ = lean_nat_dec_le(v___x_2064_, v___x_2080_);
                    if v___x_2084_ == 0 {
                        crate::leanh::lean_dec(v___x_2064_);
                        crate::leanh::lean_inc(v___x_2080_);
                        v___y_2082_ = v___x_2080_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2082_ = v___x_2064_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2064_);
                    crate::leanh::lean_inc_ref_n(v_entries_2071_, 2);
                    v___x_2085_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2085_, 0, v_entries_2071_);
                    crate::leanh::lean_ctor_set(v___x_2085_, 1, v_entries_2071_);
                    crate::leanh::lean_ctor_set(v___x_2085_, 2, v_entries_2071_);
                    return v___x_2085_;
                }
            }
            1 => {
                v___x_2076_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5___redArg(v___x_2072_, v_entries_2071_, v___y_2074_, v___y_2075_);
                crate::leanh::lean_dec(v___y_2075_);
                crate::leanh::lean_inc_ref_n(v___x_2076_, 2);
                v___x_2077_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2077_, 0, v___x_2076_);
                crate::leanh::lean_ctor_set(v___x_2077_, 1, v___x_2076_);
                crate::leanh::lean_ctor_set(v___x_2077_, 2, v___x_2076_);
                return v___x_2077_;
            }
            2 => {
                v___x_2083_ = lean_nat_dec_le(v___y_2082_, v___x_2080_);
                if v___x_2083_ == 0 {
                    crate::leanh::lean_dec(v___x_2080_);
                    crate::leanh::lean_inc(v___y_2082_);
                    v___y_2074_ = v___y_2082_;
                    v___y_2075_ = v___y_2082_;
                    state = 1;
                    continue;
                } else {
                    v___y_2074_ = v___y_2082_;
                    v___y_2075_ = v___x_2080_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__3_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed(
    mut v___x_2086_: *mut crate::leanh::LeanObject,
    mut v_x_2087_: *mut crate::leanh::LeanObject,
    mut v_s_2088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2089_ = l___private_Lean_Namespace_0__Lean_initFn___lam__3_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(v___x_2086_, v_x_2087_, v_s_2088_);
    crate::leanh::lean_dec_ref(v_s_2088_);
    crate::leanh::lean_dec_ref(v_x_2087_);
    return v_res_2089_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__5___lam__0(
    mut v___y_2090_: u8,
    mut v_x_2091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2096_: u8 = 0;
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut v_unused_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2091_) == 1 {
                    v_val_2092_ = crate::leanh::lean_ctor_get(v_x_2091_, 0);
                    v___x_2093_ = (crate::leanh::lean_unbox(v_val_2092_) as u8);
                    if v___x_2093_ == 1 {
                        return v_x_2091_;
                    } else {
                        v_isSharedCheck_2101_ = (!crate::leanh::lean_is_exclusive(v_x_2091_)) as u8;
                        if v_isSharedCheck_2101_ == 0 {
                            v_unused_2102_ = crate::leanh::lean_ctor_get(v_x_2091_, 0);
                            crate::leanh::lean_dec(v_unused_2102_);
                            v___x_2095_ = v_x_2091_;
                            v_isShared_2096_ = v_isSharedCheck_2101_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2091_);
                            v___x_2095_ = crate::leanh::lean_box(0);
                            v_isShared_2096_ = v_isSharedCheck_2101_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_2091_);
                    v___x_2103_ = crate::leanh::lean_box((v___y_2090_) as usize);
                    v___x_2104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2104_, 0, v___x_2103_);
                    return v___x_2104_;
                }
            }
            1 => {
                v___x_2097_ = crate::leanh::lean_box((v___y_2090_) as usize);
                if v_isShared_2096_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2095_, 0, v___x_2097_);
                    v___x_2099_ = v___x_2095_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
                    v___x_2099_ = v_reuseFailAlloc_2100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__5___lam__0___boxed(
    mut v___y_2105_: *mut crate::leanh::LeanObject,
    mut v_x_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5314__boxed_2107_: u8 = 0;
    let mut v_res_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_5314__boxed_2107_ = (crate::leanh::lean_unbox(v___y_2105_) as u8);
    v_res_2108_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__5___lam__0(v___y_5314__boxed_2107_, v_x_2106_);
    return v_res_2108_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__5(
    mut v___y_2109_: u8,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_x_2111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2121_: u8 = 0;
    let mut v___x_2122_: u8 = 0;
    let mut v_tail_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2111_) == 0 {
                    v___x_2112_ = crate::leanh::lean_box(0);
                    v___x_2113_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__5___lam__0(v___y_2109_, v___x_2112_);
                    if crate::leanh::lean_obj_tag(v___x_2113_) == 0 {
                        crate::leanh::lean_dec(v_a_2110_);
                        return v_x_2111_;
                    } else {
                        v_val_2114_ = crate::leanh::lean_ctor_get(v___x_2113_, 0);
                        crate::leanh::lean_inc(v_val_2114_);
                        crate::leanh::lean_dec_ref_known(v___x_2113_, 1);
                        v___x_2115_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2115_, 0, v_a_2110_);
                        crate::leanh::lean_ctor_set(v___x_2115_, 1, v_val_2114_);
                        crate::leanh::lean_ctor_set(v___x_2115_, 2, v_x_2111_);
                        return v___x_2115_;
                    }
                } else {
                    v_key_2116_ = crate::leanh::lean_ctor_get(v_x_2111_, 0);
                    v_value_2117_ = crate::leanh::lean_ctor_get(v_x_2111_, 1);
                    v_tail_2118_ = crate::leanh::lean_ctor_get(v_x_2111_, 2);
                    v_isSharedCheck_2133_ = (!crate::leanh::lean_is_exclusive(v_x_2111_)) as u8;
                    if v_isSharedCheck_2133_ == 0 {
                        v___x_2120_ = v_x_2111_;
                        v_isShared_2121_ = v_isSharedCheck_2133_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2118_);
                        crate::leanh::lean_inc(v_value_2117_);
                        crate::leanh::lean_inc(v_key_2116_);
                        crate::leanh::lean_dec(v_x_2111_);
                        v___x_2120_ = crate::leanh::lean_box(0);
                        v_isShared_2121_ = v_isSharedCheck_2133_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2122_ = lean_name_eq(v_key_2116_, v_a_2110_);
                if v___x_2122_ == 0 {
                    v_tail_2123_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__5(v___y_2109_, v_a_2110_, v_tail_2118_);
                    if v_isShared_2121_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2120_, 2, v_tail_2123_);
                        v___x_2125_ = v___x_2120_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2126_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_key_2116_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_value_2117_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 2, v_tail_2123_);
                        v___x_2125_ = v_reuseFailAlloc_2126_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_key_2116_);
                    v___x_2127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2127_, 0, v_value_2117_);
                    v___x_2128_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__5___lam__0(v___y_2109_, v___x_2127_);
                    if crate::leanh::lean_obj_tag(v___x_2128_) == 0 {
                        crate::leanh::lean_del_object(v___x_2120_);
                        crate::leanh::lean_dec(v_a_2110_);
                        return v_tail_2118_;
                    } else {
                        v_val_2129_ = crate::leanh::lean_ctor_get(v___x_2128_, 0);
                        crate::leanh::lean_inc(v_val_2129_);
                        crate::leanh::lean_dec_ref_known(v___x_2128_, 1);
                        if v_isShared_2121_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2120_, 1, v_val_2129_);
                            crate::leanh::lean_ctor_set(v___x_2120_, 0, v_a_2110_);
                            v___x_2131_ = v___x_2120_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2132_ =
                                crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2110_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_val_2129_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_tail_2118_);
                            v___x_2131_ = v_reuseFailAlloc_2132_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2125_;
            }
            3 => {
                return v___x_2131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__5___boxed(
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v_a_2135_: *mut crate::leanh::LeanObject,
    mut v_x_2136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5346__boxed_2137_: u8 = 0;
    let mut v_res_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_5346__boxed_2137_ = (crate::leanh::lean_unbox(v___y_2134_) as u8);
    v_res_2138_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__5(v___y_5346__boxed_2137_, v_a_2135_, v_x_2136_);
    return v_res_2138_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1(
    mut v___y_2139_: u8,
    mut v_m_2140_: *mut crate::leanh::LeanObject,
    mut v_a_2141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2143_: usize = 0;
    let mut v___y_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2156_: u64 = 0;
    let mut v___x_2157_: u64 = 0;
    let mut v___x_2158_: u64 = 0;
    let mut v_fold_2159_: u64 = 0;
    let mut v___x_2160_: u64 = 0;
    let mut v___x_2161_: u64 = 0;
    let mut v___x_2162_: u64 = 0;
    let mut v___x_2163_: usize = 0;
    let mut v___x_2164_: usize = 0;
    let mut v___x_2165_: usize = 0;
    let mut v___x_2166_: usize = 0;
    let mut v___x_2167_: usize = 0;
    let mut v_bkt_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: u8 = 0;
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: u8 = 0;
    let mut v_val_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bkt_x27_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u64 = 0;
    let mut v_hash_2195_: u64 = 0;
    let mut v_isSharedCheck_2196_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2149_ = crate::leanh::lean_ctor_get(v_m_2140_, 0);
                v_buckets_2150_ = crate::leanh::lean_ctor_get(v_m_2140_, 1);
                v_isSharedCheck_2196_ = (!crate::leanh::lean_is_exclusive(v_m_2140_)) as u8;
                if v_isSharedCheck_2196_ == 0 {
                    v___x_2152_ = v_m_2140_;
                    v_isShared_2153_ = v_isSharedCheck_2196_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_2150_);
                    crate::leanh::lean_inc(v_size_2149_);
                    crate::leanh::lean_dec(v_m_2140_);
                    v___x_2152_ = crate::leanh::lean_box(0);
                    v_isShared_2153_ = v_isSharedCheck_2196_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2147_ = lean_array_uset(v___y_2144_, v___y_2143_, v___y_2145_);
                v___x_2148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2148_, 0, v___y_2146_);
                crate::leanh::lean_ctor_set(v___x_2148_, 1, v___x_2147_);
                return v___x_2148_;
            }
            2 => {
                v___x_2154_ = lean_array_get_size(v_buckets_2150_);
                if crate::leanh::lean_obj_tag(v_a_2141_) == 0 {
                    v___x_2194_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0);
                    v___y_2156_ = v___x_2194_;
                    state = 3;
                    continue;
                } else {
                    v_hash_2195_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_2141_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2156_ = v_hash_2195_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2157_ = 32u64;
                v___x_2158_ = lean_uint64_shift_right(v___y_2156_, v___x_2157_);
                v_fold_2159_ = lean_uint64_xor(v___y_2156_, v___x_2158_);
                v___x_2160_ = 16u64;
                v___x_2161_ = lean_uint64_shift_right(v_fold_2159_, v___x_2160_);
                v___x_2162_ = lean_uint64_xor(v_fold_2159_, v___x_2161_);
                v___x_2163_ = lean_uint64_to_usize(v___x_2162_);
                v___x_2164_ = lean_usize_of_nat(v___x_2154_);
                v___x_2165_ = 1usize;
                v___x_2166_ = lean_usize_sub(v___x_2164_, v___x_2165_);
                v___x_2167_ = lean_usize_land(v___x_2163_, v___x_2166_);
                v_bkt_2168_ = lean_array_uget_borrowed(v_buckets_2150_, v___x_2167_);
                v___x_2169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3___redArg(v_a_2141_, v_bkt_2168_);
                if v___x_2169_ == 0 {
                    v___x_2170_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2171_ = lean_nat_add(v_size_2149_, v___x_2170_);
                    crate::leanh::lean_dec(v_size_2149_);
                    v___x_2172_ = crate::leanh::lean_box((v___y_2139_) as usize);
                    crate::leanh::lean_inc(v_bkt_2168_);
                    v___x_2173_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2173_, 0, v_a_2141_);
                    crate::leanh::lean_ctor_set(v___x_2173_, 1, v___x_2172_);
                    crate::leanh::lean_ctor_set(v___x_2173_, 2, v_bkt_2168_);
                    v_buckets_x27_2174_ =
                        lean_array_uset(v_buckets_2150_, v___x_2167_, v___x_2173_);
                    v___x_2175_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2176_ = lean_nat_mul(v_size_x27_2171_, v___x_2175_);
                    v___x_2177_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2178_ = lean_nat_div(v___x_2176_, v___x_2177_);
                    crate::leanh::lean_dec(v___x_2176_);
                    v___x_2179_ = lean_array_get_size(v_buckets_x27_2174_);
                    v___x_2180_ = lean_nat_dec_le(v___x_2178_, v___x_2179_);
                    crate::leanh::lean_dec(v___x_2178_);
                    if v___x_2180_ == 0 {
                        v_val_2181_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4___redArg(v_buckets_x27_2174_);
                        if v_isShared_2153_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2152_, 1, v_val_2181_);
                            crate::leanh::lean_ctor_set(v___x_2152_, 0, v_size_x27_2171_);
                            v___x_2183_ = v___x_2152_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2184_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2184_,
                                0,
                                v_size_x27_2171_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_val_2181_);
                            v___x_2183_ = v_reuseFailAlloc_2184_;
                            state = 4;
                            continue;
                        }
                    } else {
                        if v_isShared_2153_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2152_, 1, v_buckets_x27_2174_);
                            crate::leanh::lean_ctor_set(v___x_2152_, 0, v_size_x27_2171_);
                            v___x_2186_ = v___x_2152_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2187_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2187_,
                                0,
                                v_size_x27_2171_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2187_,
                                1,
                                v_buckets_x27_2174_,
                            );
                            v___x_2186_ = v_reuseFailAlloc_2187_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2168_);
                    crate::leanh::lean_del_object(v___x_2152_);
                    v___x_2188_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2189_ =
                        lean_array_uset(v_buckets_2150_, v___x_2167_, v___x_2188_);
                    crate::leanh::lean_inc(v_a_2141_);
                    v_bkt_x27_2190_ = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__5(v___y_2139_, v_a_2141_, v_bkt_2168_);
                    v___x_2191_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3___redArg(v_a_2141_, v_bkt_x27_2190_);
                    crate::leanh::lean_dec(v_a_2141_);
                    if v___x_2191_ == 0 {
                        v___x_2192_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2193_ = lean_nat_sub(v_size_2149_, v___x_2192_);
                        crate::leanh::lean_dec(v_size_2149_);
                        v___y_2143_ = v___x_2167_;
                        v___y_2144_ = v_buckets_x27_2189_;
                        v___y_2145_ = v_bkt_x27_2190_;
                        v___y_2146_ = v___x_2193_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2143_ = v___x_2167_;
                        v___y_2144_ = v_buckets_x27_2189_;
                        v___y_2145_ = v_bkt_x27_2190_;
                        v___y_2146_ = v_size_2149_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2183_;
            }
            5 => {
                return v___x_2186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1___boxed(
    mut v___y_2197_: *mut crate::leanh::LeanObject,
    mut v_m_2198_: *mut crate::leanh::LeanObject,
    mut v_a_2199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5396__boxed_2200_: u8 = 0;
    let mut v_res_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_5396__boxed_2200_ = (crate::leanh::lean_unbox(v___y_2197_) as u8);
    v_res_2201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1(v___y_5396__boxed_2200_, v_m_2198_, v_a_2199_);
    return v_res_2201_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__2___redArg(
    mut v___y_2202_: u8,
    mut v_as_2203_: *mut crate::leanh::LeanObject,
    mut v_sz_2204_: usize,
    mut v_i_2205_: usize,
    mut v_b_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: usize = 0;
    let mut v___x_2213_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2208_ = lean_usize_dec_lt(v_i_2205_, v_sz_2204_);
                if v___x_2208_ == 0 {
                    v___x_2209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2209_, 0, v_b_2206_);
                    return v___x_2209_;
                } else {
                    v_a_2210_ = lean_array_uget_borrowed(v_as_2203_, v_i_2205_);
                    crate::leanh::lean_inc(v_a_2210_);
                    v___x_2211_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1(v___y_2202_, v_b_2206_, v_a_2210_);
                    v___x_2212_ = 1usize;
                    v___x_2213_ = lean_usize_add(v_i_2205_, v___x_2212_);
                    v_i_2205_ = v___x_2213_;
                    v_b_2206_ = v___x_2211_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v___y_2215_: *mut crate::leanh::LeanObject,
    mut v_as_2216_: *mut crate::leanh::LeanObject,
    mut v_sz_2217_: *mut crate::leanh::LeanObject,
    mut v_i_2218_: *mut crate::leanh::LeanObject,
    mut v_b_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5496__boxed_2221_: u8 = 0;
    let mut v_sz_boxed_2222_: usize = 0;
    let mut v_i_boxed_2223_: usize = 0;
    let mut v_res_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_5496__boxed_2221_ = (crate::leanh::lean_unbox(v___y_2215_) as u8);
    v_sz_boxed_2222_ = crate::leanh::lean_unbox_usize(v_sz_2217_);
    crate::leanh::lean_dec(v_sz_2217_);
    v_i_boxed_2223_ = crate::leanh::lean_unbox_usize(v_i_2218_);
    crate::leanh::lean_dec(v_i_2218_);
    v_res_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__2___redArg(v___y_5496__boxed_2221_, v_as_2216_, v_sz_boxed_2222_, v_i_boxed_2223_, v_b_2219_);
    crate::leanh::lean_dec_ref(v_as_2216_);
    return v_res_2224_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__6(
    mut v_as_2225_: *mut crate::leanh::LeanObject,
    mut v_sz_2226_: usize,
    mut v_i_2227_: usize,
    mut v_b_2228_: *mut crate::leanh::LeanObject,
    mut v___y_2229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2237_: u8 = 0;
    let mut v_array_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2248_: u8 = 0;
    let mut v_a_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExported_2251_: u8 = 0;
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: u8 = 0;
    let mut v_sz_2259_: usize = 0;
    let mut v___x_2260_: usize = 0;
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: usize = 0;
    let mut v___x_2266_: usize = 0;
    let mut v_reuseFailAlloc_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: u8 = 0;
    let mut v_reuseFailAlloc_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut v_unused_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2231_ = lean_usize_dec_lt(v_i_2227_, v_sz_2226_);
                if v___x_2231_ == 0 {
                    v___x_2232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2232_, 0, v_b_2228_);
                    return v___x_2232_;
                } else {
                    v_snd_2233_ = crate::leanh::lean_ctor_get(v_b_2228_, 1);
                    v_fst_2234_ = crate::leanh::lean_ctor_get(v_b_2228_, 0);
                    v_isSharedCheck_2284_ = (!crate::leanh::lean_is_exclusive(v_b_2228_)) as u8;
                    if v_isSharedCheck_2284_ == 0 {
                        v___x_2236_ = v_b_2228_;
                        v_isShared_2237_ = v_isSharedCheck_2284_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2233_);
                        crate::leanh::lean_inc(v_fst_2234_);
                        crate::leanh::lean_dec(v_b_2228_);
                        v___x_2236_ = crate::leanh::lean_box(0);
                        v_isShared_2237_ = v_isSharedCheck_2284_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_2238_ = crate::leanh::lean_ctor_get(v_snd_2233_, 0);
                v_start_2239_ = crate::leanh::lean_ctor_get(v_snd_2233_, 1);
                v_stop_2240_ = crate::leanh::lean_ctor_get(v_snd_2233_, 2);
                v___x_2241_ = lean_nat_dec_lt(v_start_2239_, v_stop_2240_);
                if v___x_2241_ == 0 {
                    if v_isShared_2237_ == 0 {
                        v___x_2243_ = v___x_2236_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_fst_2234_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_snd_2233_);
                        v___x_2243_ = v_reuseFailAlloc_2245_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_2240_);
                    crate::leanh::lean_inc(v_start_2239_);
                    crate::leanh::lean_inc_ref(v_array_2238_);
                    v_isSharedCheck_2280_ = (!crate::leanh::lean_is_exclusive(v_snd_2233_)) as u8;
                    if v_isSharedCheck_2280_ == 0 {
                        v_unused_2281_ = crate::leanh::lean_ctor_get(v_snd_2233_, 2);
                        crate::leanh::lean_dec(v_unused_2281_);
                        v_unused_2282_ = crate::leanh::lean_ctor_get(v_snd_2233_, 1);
                        crate::leanh::lean_dec(v_unused_2282_);
                        v_unused_2283_ = crate::leanh::lean_ctor_get(v_snd_2233_, 0);
                        crate::leanh::lean_dec(v_unused_2283_);
                        v___x_2247_ = v_snd_2233_;
                        v_isShared_2248_ = v_isSharedCheck_2280_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_2233_);
                        v___x_2247_ = crate::leanh::lean_box(0);
                        v_isShared_2248_ = v_isSharedCheck_2280_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2244_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2244_, 0, v___x_2243_);
                return v___x_2244_;
            }
            3 => {
                v_a_2249_ = lean_array_uget_borrowed(v_as_2225_, v_i_2227_);
                v_toImport_2250_ = crate::leanh::lean_ctor_get(v_a_2249_, 0);
                v_isExported_2251_ = crate::leanh::lean_ctor_get_uint8(
                    v_toImport_2250_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                );
                v___x_2252_ = lean_array_fget(v_array_2238_, v_start_2239_);
                v___x_2253_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2254_ = lean_nat_add(v_start_2239_, v___x_2253_);
                crate::leanh::lean_dec(v_start_2239_);
                if v_isShared_2248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2247_, 1, v___x_2254_);
                    v___x_2256_ = v___x_2247_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2279_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_array_2238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 1, v___x_2254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_stop_2240_);
                    v___x_2256_ = v_reuseFailAlloc_2279_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isExported_2251_ == 0 {
                    v___x_2277_ = 0;
                    v___y_2258_ = v___x_2277_;
                    state = 5;
                    continue;
                } else {
                    v___x_2278_ = 1;
                    v___y_2258_ = v___x_2278_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_sz_2259_ = lean_array_size(v___x_2252_);
                v___x_2260_ = 0usize;
                v___x_2261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__2___redArg(v___y_2258_, v___x_2252_, v_sz_2259_, v___x_2260_, v_fst_2234_);
                crate::leanh::lean_dec(v___x_2252_);
                if crate::leanh::lean_obj_tag(v___x_2261_) == 0 {
                    v_a_2262_ = crate::leanh::lean_ctor_get(v___x_2261_, 0);
                    crate::leanh::lean_inc(v_a_2262_);
                    crate::leanh::lean_dec_ref_known(v___x_2261_, 1);
                    if v_isShared_2237_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2236_, 1, v___x_2256_);
                        crate::leanh::lean_ctor_set(v___x_2236_, 0, v_a_2262_);
                        v___x_2264_ = v___x_2236_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2268_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2256_);
                        v___x_2264_ = v_reuseFailAlloc_2268_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2256_);
                    crate::leanh::lean_del_object(v___x_2236_);
                    v_a_2269_ = crate::leanh::lean_ctor_get(v___x_2261_, 0);
                    v_isSharedCheck_2276_ = (!crate::leanh::lean_is_exclusive(v___x_2261_)) as u8;
                    if v_isSharedCheck_2276_ == 0 {
                        v___x_2271_ = v___x_2261_;
                        v_isShared_2272_ = v_isSharedCheck_2276_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2269_);
                        crate::leanh::lean_dec(v___x_2261_);
                        v___x_2271_ = crate::leanh::lean_box(0);
                        v_isShared_2272_ = v_isSharedCheck_2276_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2265_ = 1usize;
                v___x_2266_ = lean_usize_add(v_i_2227_, v___x_2265_);
                v_i_2227_ = v___x_2266_;
                v_b_2228_ = v___x_2264_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_2272_ == 0 {
                    v___x_2274_ = v___x_2271_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
                    v___x_2274_ = v_reuseFailAlloc_2275_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__6___boxed(
    mut v_as_2285_: *mut crate::leanh::LeanObject,
    mut v_sz_2286_: *mut crate::leanh::LeanObject,
    mut v_i_2287_: *mut crate::leanh::LeanObject,
    mut v_b_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2291_: usize = 0;
    let mut v_i_boxed_2292_: usize = 0;
    let mut v_res_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2291_ = crate::leanh::lean_unbox_usize(v_sz_2286_);
    crate::leanh::lean_dec(v_sz_2286_);
    v_i_boxed_2292_ = crate::leanh::lean_unbox_usize(v_i_2287_);
    crate::leanh::lean_dec(v_i_2287_);
    v_res_2293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__6(v_as_2285_, v_sz_boxed_2291_, v_i_boxed_2292_, v_b_2288_, v___y_2289_);
    crate::leanh::lean_dec_ref(v___y_2289_);
    crate::leanh::lean_dec_ref(v_as_2285_);
    return v_res_2293_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__8(
    mut v_as_2294_: *mut crate::leanh::LeanObject,
    mut v_i_2295_: usize,
    mut v_stop_2296_: usize,
    mut v_b_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2298_: u8 = 0;
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: usize = 0;
    let mut v___x_2303_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2298_ = lean_usize_dec_eq(v_i_2295_, v_stop_2296_);
                if v___x_2298_ == 0 {
                    v___x_2299_ = lean_array_uget_borrowed(v_as_2294_, v_i_2295_);
                    v___x_2300_ = lean_array_get_size(v___x_2299_);
                    v___x_2301_ = lean_nat_add(v_b_2297_, v___x_2300_);
                    crate::leanh::lean_dec(v_b_2297_);
                    v___x_2302_ = 1usize;
                    v___x_2303_ = lean_usize_add(v_i_2295_, v___x_2302_);
                    v_i_2295_ = v___x_2303_;
                    v_b_2297_ = v___x_2301_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2297_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__8___boxed(
    mut v_as_2305_: *mut crate::leanh::LeanObject,
    mut v_i_2306_: *mut crate::leanh::LeanObject,
    mut v_stop_2307_: *mut crate::leanh::LeanObject,
    mut v_b_2308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2309_: usize = 0;
    let mut v_stop_boxed_2310_: usize = 0;
    let mut v_res_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2309_ = crate::leanh::lean_unbox_usize(v_i_2306_);
    crate::leanh::lean_dec(v_i_2306_);
    v_stop_boxed_2310_ = crate::leanh::lean_unbox_usize(v_stop_2307_);
    crate::leanh::lean_dec(v_stop_2307_);
    v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__8(v_as_2305_, v_i_boxed_2309_, v_stop_boxed_2310_, v_b_2308_);
    crate::leanh::lean_dec_ref(v_as_2305_);
    return v_res_2311_;
}
pub unsafe fn _init_l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2312_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2312_;
}
pub unsafe fn _init_l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2313_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once), _init_l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_);
    v___x_2314_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2314_, 0, v___x_2313_);
    return v___x_2314_;
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__4_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(
    mut v___x_2315_: *mut crate::leanh::LeanObject,
    mut v___x_2316_: u8,
    mut v_as_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_env_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2336_: usize = 0;
    let mut v___x_2337_: usize = 0;
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v_fst_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2350_: u8 = 0;
    let mut v_a_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2354_: u8 = 0;
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2358_: u8 = 0;
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: u8 = 0;
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: usize = 0;
    let mut v___x_2363_: usize = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: usize = 0;
    let mut v___x_2366_: usize = 0;
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_env_2320_ = crate::leanh::lean_ctor_get(v___y_2318_, 0);
                v___x_2359_ = lean_array_get_size(v_as_2317_);
                v___x_2360_ = lean_nat_dec_lt(v___x_2315_, v___x_2359_);
                if v___x_2360_ == 0 {
                    crate::leanh::lean_inc(v___x_2315_);
                    v___y_2322_ = v___x_2315_;
                    state = 1;
                    continue;
                } else {
                    v___x_2361_ = lean_nat_dec_le(v___x_2359_, v___x_2359_);
                    if v___x_2361_ == 0 {
                        if v___x_2360_ == 0 {
                            crate::leanh::lean_inc(v___x_2315_);
                            v___y_2322_ = v___x_2315_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2362_ = 0usize;
                            v___x_2363_ = lean_usize_of_nat(v___x_2359_);
                            crate::leanh::lean_inc(v___x_2315_);
                            v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__8(v_as_2317_, v___x_2362_, v___x_2363_, v___x_2315_);
                            v___y_2322_ = v___x_2364_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2365_ = 0usize;
                        v___x_2366_ = lean_usize_of_nat(v___x_2359_);
                        crate::leanh::lean_inc(v___x_2315_);
                        v___x_2367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__8(v_as_2317_, v___x_2365_, v___x_2366_, v___x_2315_);
                        v___y_2322_ = v___x_2367_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2323_ = l_Lean_Environment_header(v_env_2320_);
                v_modules_2324_ = crate::leanh::lean_ctor_get(v___x_2323_, 3);
                crate::leanh::lean_inc_ref(v_modules_2324_);
                crate::leanh::lean_dec_ref(v___x_2323_);
                v___x_2325_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2326_ = lean_nat_mul(v___y_2322_, v___x_2325_);
                crate::leanh::lean_dec(v___y_2322_);
                v___x_2327_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2328_ = lean_nat_div(v___x_2326_, v___x_2327_);
                crate::leanh::lean_dec(v___x_2326_);
                v___x_2329_ = l_Nat_nextPowerOfTwo(v___x_2328_);
                crate::leanh::lean_dec(v___x_2328_);
                v___x_2330_ = crate::leanh::lean_box(0);
                v___x_2331_ = lean_mk_array(v___x_2329_, v___x_2330_);
                crate::leanh::lean_inc(v___x_2315_);
                v___x_2332_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2332_, 0, v___x_2315_);
                crate::leanh::lean_ctor_set(v___x_2332_, 1, v___x_2331_);
                v___x_2333_ = lean_array_get_size(v_as_2317_);
                v___x_2334_ = l_Array_toSubarray___redArg(v_as_2317_, v___x_2315_, v___x_2333_);
                v___x_2335_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2335_, 0, v___x_2332_);
                crate::leanh::lean_ctor_set(v___x_2335_, 1, v___x_2334_);
                v_sz_2336_ = lean_array_size(v_modules_2324_);
                v___x_2337_ = 0usize;
                v___x_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__6(v_modules_2324_, v_sz_2336_, v___x_2337_, v___x_2335_, v___y_2318_);
                crate::leanh::lean_dec_ref(v_modules_2324_);
                if crate::leanh::lean_obj_tag(v___x_2338_) == 0 {
                    v_a_2339_ = crate::leanh::lean_ctor_get(v___x_2338_, 0);
                    v_isSharedCheck_2350_ = (!crate::leanh::lean_is_exclusive(v___x_2338_)) as u8;
                    if v_isSharedCheck_2350_ == 0 {
                        v___x_2341_ = v___x_2338_;
                        v_isShared_2342_ = v_isSharedCheck_2350_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2339_);
                        crate::leanh::lean_dec(v___x_2338_);
                        v___x_2341_ = crate::leanh::lean_box(0);
                        v_isShared_2342_ = v_isSharedCheck_2350_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2351_ = crate::leanh::lean_ctor_get(v___x_2338_, 0);
                    v_isSharedCheck_2358_ = (!crate::leanh::lean_is_exclusive(v___x_2338_)) as u8;
                    if v_isSharedCheck_2358_ == 0 {
                        v___x_2353_ = v___x_2338_;
                        v_isShared_2354_ = v_isSharedCheck_2358_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2351_);
                        crate::leanh::lean_dec(v___x_2338_);
                        v___x_2353_ = crate::leanh::lean_box(0);
                        v_isShared_2354_ = v_isSharedCheck_2358_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_2343_ = crate::leanh::lean_ctor_get(v_a_2339_, 0);
                crate::leanh::lean_inc(v_fst_2343_);
                crate::leanh::lean_dec(v_a_2339_);
                v___x_2344_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once), _init_l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_);
                v___x_2345_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2345_, 0, v_fst_2343_);
                crate::leanh::lean_ctor_set(v___x_2345_, 1, v___x_2344_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2345_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2316_,
                );
                v___x_2346_ = l_Lean_SMap_switch___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__7___redArg(v___x_2345_);
                if v_isShared_2342_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2341_, 0, v___x_2346_);
                    v___x_2348_ = v___x_2341_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2349_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2346_);
                    v___x_2348_ = v_reuseFailAlloc_2349_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2348_;
            }
            4 => {
                if v_isShared_2354_ == 0 {
                    v___x_2356_ = v___x_2353_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
                    v___x_2356_ = v_reuseFailAlloc_2357_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__4_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed(
    mut v___x_2368_: *mut crate::leanh::LeanObject,
    mut v___x_2369_: *mut crate::leanh::LeanObject,
    mut v_as_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5631__boxed_2373_: u8 = 0;
    let mut v_res_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5631__boxed_2373_ = (crate::leanh::lean_unbox(v___x_2369_) as u8);
    v_res_2374_ = l___private_Lean_Namespace_0__Lean_initFn___lam__4_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(v___x_2368_, v___x_5631__boxed_2373_, v_as_2370_, v___y_2371_);
    crate::leanh::lean_dec_ref(v___y_2371_);
    return v_res_2374_;
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__5_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(
    mut v___x_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2377_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2377_, 0, v___x_2375_);
    return v___x_2377_;
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn___lam__5_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed(
    mut v___x_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2380_ = l___private_Lean_Namespace_0__Lean_initFn___lam__5_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_(v___x_2378_);
    return v_res_2380_;
}
pub unsafe fn _init_l___private_Lean_Namespace_0__Lean_initFn___closed__15_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2413_ = crate::leanh::lean_box(0);
    v___x_2414_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2415_ = lean_mk_array(v___x_2414_, v___x_2413_);
    return v___x_2415_;
}
pub unsafe fn _init_l___private_Lean_Namespace_0__Lean_initFn___closed__16_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__15_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__15_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once), _init_l___private_Lean_Namespace_0__Lean_initFn___closed__15_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_);
    v___x_2417_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2418_, 0, v___x_2417_);
    crate::leanh::lean_ctor_set(v___x_2418_, 1, v___x_2416_);
    return v___x_2418_;
}
pub unsafe fn _init_l___private_Lean_Namespace_0__Lean_initFn___closed__17_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2419_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once), _init_l___private_Lean_Namespace_0__Lean_initFn___lam__4___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_);
    v___x_2420_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__16_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__16_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once), _init_l___private_Lean_Namespace_0__Lean_initFn___closed__16_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_);
    v___x_2421_ = 1;
    v___x_2422_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2422_, 0, v___x_2420_);
    crate::leanh::lean_ctor_set(v___x_2422_, 1, v___x_2419_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2422_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_2421_,
    );
    return v___x_2422_;
}
pub unsafe fn _init_l___private_Lean_Namespace_0__Lean_initFn___closed__18_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2423_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__17_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__17_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once), _init_l___private_Lean_Namespace_0__Lean_initFn___closed__17_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_);
    v___f_2424_ = crate::leanh::lean_alloc_closure(l___private_Lean_Namespace_0__Lean_initFn___lam__5_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_2424_, 0, v___x_2423_);
    return v___f_2424_;
}
pub unsafe fn _init_l___private_Lean_Namespace_0__Lean_initFn___closed__19_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2425_ = crate::leanh::lean_box(0);
    v___x_2426_ = crate::leanh::lean_box(1);
    v___f_2427_ = l___private_Lean_Namespace_0__Lean_initFn___closed__1_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_;
    v___f_2428_ = l___private_Lean_Namespace_0__Lean_initFn___closed__9_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_;
    v___f_2429_ = l___private_Lean_Namespace_0__Lean_initFn___closed__0_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_;
    v___f_2430_ = l___private_Lean_Namespace_0__Lean_initFn___closed__14_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_;
    v___f_2431_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__18_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__18_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once), _init_l___private_Lean_Namespace_0__Lean_initFn___closed__18_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_);
    v___x_2432_ = l___private_Lean_Namespace_0__Lean_initFn___closed__13_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_;
    v___x_2433_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2433_, 0, v___x_2432_);
    crate::leanh::lean_ctor_set(v___x_2433_, 1, v___f_2431_);
    crate::leanh::lean_ctor_set(v___x_2433_, 2, v___f_2430_);
    crate::leanh::lean_ctor_set(v___x_2433_, 3, v___f_2429_);
    crate::leanh::lean_ctor_set(v___x_2433_, 4, v___f_2428_);
    crate::leanh::lean_ctor_set(v___x_2433_, 5, v___f_2427_);
    crate::leanh::lean_ctor_set(v___x_2433_, 6, v___x_2426_);
    crate::leanh::lean_ctor_set(v___x_2433_, 7, v___x_2425_);
    return v___x_2433_;
}
pub unsafe fn _init_l___private_Lean_Namespace_0__Lean_initFn___closed__20_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2434_ = l___private_Lean_Namespace_0__Lean_initFn___closed__8_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_;
    v___x_2435_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__19_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__19_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once), _init_l___private_Lean_Namespace_0__Lean_initFn___closed__19_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_);
    v___x_2436_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2436_, 0, v___x_2435_);
    crate::leanh::lean_ctor_set(v___x_2436_, 1, v___f_2434_);
    return v___x_2436_;
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2438_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__20_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Namespace_0__Lean_initFn___closed__20_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__once), _init_l___private_Lean_Namespace_0__Lean_initFn___closed__20_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_);
    v___x_2439_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2438_);
    return v___x_2439_;
}
pub unsafe fn l___private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2____boxed(
    mut v_a_2440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2441_ = l___private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_();
    return v_res_2441_;
}
pub unsafe fn l_Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_2442_: *mut crate::leanh::LeanObject,
    mut v_x_2443_: *mut crate::leanh::LeanObject,
    mut v_x_2444_: *mut crate::leanh::LeanObject,
    mut v_x_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2446_ = l_Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0___redArg(v_x_2443_, v_x_2444_, v_x_2445_);
    return v___x_2446_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__2(
    mut v___y_2447_: u8,
    mut v_as_2448_: *mut crate::leanh::LeanObject,
    mut v_sz_2449_: usize,
    mut v_i_2450_: usize,
    mut v_b_2451_: *mut crate::leanh::LeanObject,
    mut v___y_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__2___redArg(v___y_2447_, v_as_2448_, v_sz_2449_, v_i_2450_, v_b_2451_);
    return v___x_2454_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__2___boxed(
    mut v___y_2455_: *mut crate::leanh::LeanObject,
    mut v_as_2456_: *mut crate::leanh::LeanObject,
    mut v_sz_2457_: *mut crate::leanh::LeanObject,
    mut v_i_2458_: *mut crate::leanh::LeanObject,
    mut v_b_2459_: *mut crate::leanh::LeanObject,
    mut v___y_2460_: *mut crate::leanh::LeanObject,
    mut v___y_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5926__boxed_2462_: u8 = 0;
    let mut v_sz_boxed_2463_: usize = 0;
    let mut v_i_boxed_2464_: usize = 0;
    let mut v_res_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_5926__boxed_2462_ = (crate::leanh::lean_unbox(v___y_2455_) as u8);
    v_sz_boxed_2463_ = crate::leanh::lean_unbox_usize(v_sz_2457_);
    crate::leanh::lean_dec(v_sz_2457_);
    v_i_boxed_2464_ = crate::leanh::lean_unbox_usize(v_i_2458_);
    crate::leanh::lean_dec(v_i_2458_);
    v_res_2465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__2(v___y_5926__boxed_2462_, v_as_2456_, v_sz_boxed_2463_, v_i_boxed_2464_, v_b_2459_, v___y_2460_);
    crate::leanh::lean_dec_ref(v___y_2460_);
    crate::leanh::lean_dec_ref(v_as_2456_);
    return v_res_2465_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3(
    mut v_00_u03b2_2466_: *mut crate::leanh::LeanObject,
    mut v_m_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___redArg(v_m_2467_);
    return v___x_2468_;
}
pub unsafe fn l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3___boxed(
    mut v_00_u03b2_2469_: *mut crate::leanh::LeanObject,
    mut v_m_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2471_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3(v_00_u03b2_2469_, v_m_2470_);
    crate::leanh::lean_dec_ref(v_m_2470_);
    return v_res_2471_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5(
    mut v_n_2472_: *mut crate::leanh::LeanObject,
    mut v_as_2473_: *mut crate::leanh::LeanObject,
    mut v_lo_2474_: *mut crate::leanh::LeanObject,
    mut v_hi_2475_: *mut crate::leanh::LeanObject,
    mut v_w_2476_: *mut crate::leanh::LeanObject,
    mut v_hlo_2477_: *mut crate::leanh::LeanObject,
    mut v_hhi_2478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5___redArg(v_n_2472_, v_as_2473_, v_lo_2474_, v_hi_2475_);
    return v___x_2479_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5___boxed(
    mut v_n_2480_: *mut crate::leanh::LeanObject,
    mut v_as_2481_: *mut crate::leanh::LeanObject,
    mut v_lo_2482_: *mut crate::leanh::LeanObject,
    mut v_hi_2483_: *mut crate::leanh::LeanObject,
    mut v_w_2484_: *mut crate::leanh::LeanObject,
    mut v_hlo_2485_: *mut crate::leanh::LeanObject,
    mut v_hhi_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2487_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5(v_n_2480_, v_as_2481_, v_lo_2482_, v_hi_2483_, v_w_2484_, v_hlo_2485_, v_hhi_2486_);
    crate::leanh::lean_dec(v_hi_2483_);
    crate::leanh::lean_dec(v_n_2480_);
    return v_res_2487_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_2488_: *mut crate::leanh::LeanObject,
    mut v_x_2489_: *mut crate::leanh::LeanObject,
    mut v_x_2490_: *mut crate::leanh::LeanObject,
    mut v_x_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2489_, v_x_2490_, v_x_2491_);
    return v___x_2492_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_2493_: *mut crate::leanh::LeanObject,
    mut v_m_2494_: *mut crate::leanh::LeanObject,
    mut v_a_2495_: *mut crate::leanh::LeanObject,
    mut v_b_2496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2497_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__1___redArg(v_m_2494_, v_a_2495_, v_b_2496_);
    return v___x_2497_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3(
    mut v_00_u03b2_2498_: *mut crate::leanh::LeanObject,
    mut v_a_2499_: *mut crate::leanh::LeanObject,
    mut v_x_2500_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2501_: u8 = 0;
    v___x_2501_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3___redArg(v_a_2499_, v_x_2500_);
    return v___x_2501_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3___boxed(
    mut v_00_u03b2_2502_: *mut crate::leanh::LeanObject,
    mut v_a_2503_: *mut crate::leanh::LeanObject,
    mut v_x_2504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2505_: u8 = 0;
    let mut v_r_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2505_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b2_2502_, v_a_2503_, v_x_2504_);
    crate::leanh::lean_dec(v_x_2504_);
    crate::leanh::lean_dec(v_a_2503_);
    v_r_2506_ = crate::leanh::lean_box((v_res_2505_) as usize);
    return v_r_2506_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4(
    mut v_00_u03b2_2507_: *mut crate::leanh::LeanObject,
    mut v_data_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4___redArg(v_data_2508_);
    return v___x_2509_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8(
    mut v_00_u03c3_2510_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2511_: *mut crate::leanh::LeanObject,
    mut v_map_2512_: *mut crate::leanh::LeanObject,
    mut v_f_2513_: *mut crate::leanh::LeanObject,
    mut v_init_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8___redArg(v_map_2512_, v_f_2513_, v_init_2514_);
    return v___x_2515_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8___boxed(
    mut v_00_u03c3_2516_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2517_: *mut crate::leanh::LeanObject,
    mut v_map_2518_: *mut crate::leanh::LeanObject,
    mut v_f_2519_: *mut crate::leanh::LeanObject,
    mut v_init_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8(v_00_u03c3_2516_, v_00_u03b2_2517_, v_map_2518_, v_f_2519_, v_init_2520_);
    crate::leanh::lean_dec_ref(v_map_2518_);
    return v_res_2521_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5_spec__11(
    mut v_n_2522_: *mut crate::leanh::LeanObject,
    mut v_lo_2523_: *mut crate::leanh::LeanObject,
    mut v_hi_2524_: *mut crate::leanh::LeanObject,
    mut v_hhi_2525_: *mut crate::leanh::LeanObject,
    mut v_pivot_2526_: *mut crate::leanh::LeanObject,
    mut v_as_2527_: *mut crate::leanh::LeanObject,
    mut v_i_2528_: *mut crate::leanh::LeanObject,
    mut v_k_2529_: *mut crate::leanh::LeanObject,
    mut v_ilo_2530_: *mut crate::leanh::LeanObject,
    mut v_ik_2531_: *mut crate::leanh::LeanObject,
    mut v_w_2532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5_spec__11___redArg(v_hi_2524_, v_pivot_2526_, v_as_2527_, v_i_2528_, v_k_2529_);
    return v___x_2533_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5_spec__11___boxed(
    mut v_n_2534_: *mut crate::leanh::LeanObject,
    mut v_lo_2535_: *mut crate::leanh::LeanObject,
    mut v_hi_2536_: *mut crate::leanh::LeanObject,
    mut v_hhi_2537_: *mut crate::leanh::LeanObject,
    mut v_pivot_2538_: *mut crate::leanh::LeanObject,
    mut v_as_2539_: *mut crate::leanh::LeanObject,
    mut v_i_2540_: *mut crate::leanh::LeanObject,
    mut v_k_2541_: *mut crate::leanh::LeanObject,
    mut v_ilo_2542_: *mut crate::leanh::LeanObject,
    mut v_ik_2543_: *mut crate::leanh::LeanObject,
    mut v_w_2544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__5_spec__11(v_n_2534_, v_lo_2535_, v_hi_2536_, v_hhi_2537_, v_pivot_2538_, v_as_2539_, v_i_2540_, v_k_2541_, v_ilo_2542_, v_ik_2543_, v_w_2544_);
    crate::leanh::lean_dec(v_pivot_2538_);
    crate::leanh::lean_dec(v_hi_2536_);
    crate::leanh::lean_dec(v_lo_2535_);
    crate::leanh::lean_dec(v_n_2534_);
    return v_res_2545_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2(
    mut v_00_u03b2_2546_: *mut crate::leanh::LeanObject,
    mut v_x_2547_: *mut crate::leanh::LeanObject,
    mut v_x_2548_: usize,
    mut v_x_2549_: usize,
    mut v_x_2550_: *mut crate::leanh::LeanObject,
    mut v_x_2551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2552_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_x_2547_, v_x_2548_, v_x_2549_, v_x_2550_, v_x_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2553_: *mut crate::leanh::LeanObject,
    mut v_x_2554_: *mut crate::leanh::LeanObject,
    mut v_x_2555_: *mut crate::leanh::LeanObject,
    mut v_x_2556_: *mut crate::leanh::LeanObject,
    mut v_x_2557_: *mut crate::leanh::LeanObject,
    mut v_x_2558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5963__boxed_2559_: usize = 0;
    let mut v_x_5964__boxed_2560_: usize = 0;
    let mut v_res_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5963__boxed_2559_ = crate::leanh::lean_unbox_usize(v_x_2555_);
    crate::leanh::lean_dec(v_x_2555_);
    v_x_5964__boxed_2560_ = crate::leanh::lean_unbox_usize(v_x_2556_);
    crate::leanh::lean_dec(v_x_2556_);
    v_res_2561_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_00_u03b2_2553_, v_x_2554_, v_x_5963__boxed_2559_, v_x_5964__boxed_2560_, v_x_2557_, v_x_2558_);
    return v_res_2561_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__1_spec__4(
    mut v_00_u03b2_2562_: *mut crate::leanh::LeanObject,
    mut v_a_2563_: *mut crate::leanh::LeanObject,
    mut v_b_2564_: *mut crate::leanh::LeanObject,
    mut v_x_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2566_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__1_spec__4___redArg(v_a_2563_, v_b_2564_, v_x_2565_);
    return v___x_2566_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8(
    mut v_00_u03b2_2567_: *mut crate::leanh::LeanObject,
    mut v_i_2568_: *mut crate::leanh::LeanObject,
    mut v_source_2569_: *mut crate::leanh::LeanObject,
    mut v_target_2570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2571_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8___redArg(v_i_2568_, v_source_2569_, v_target_2570_);
    return v___x_2571_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13___redArg(
    mut v_map_2572_: *mut crate::leanh::LeanObject,
    mut v_f_2573_: *mut crate::leanh::LeanObject,
    mut v_init_2574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2575_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21___redArg(v_f_2573_, v_map_2572_, v_init_2574_);
    return v___x_2575_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13___redArg___boxed(
    mut v_map_2576_: *mut crate::leanh::LeanObject,
    mut v_f_2577_: *mut crate::leanh::LeanObject,
    mut v_init_2578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2579_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13___redArg(v_map_2576_, v_f_2577_, v_init_2578_);
    crate::leanh::lean_dec_ref(v_map_2576_);
    return v_res_2579_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13(
    mut v_00_u03c3_2580_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2581_: *mut crate::leanh::LeanObject,
    mut v_map_2582_: *mut crate::leanh::LeanObject,
    mut v_f_2583_: *mut crate::leanh::LeanObject,
    mut v_init_2584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2585_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21___redArg(v_f_2583_, v_map_2582_, v_init_2584_);
    return v___x_2585_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13___boxed(
    mut v_00_u03c3_2586_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2587_: *mut crate::leanh::LeanObject,
    mut v_map_2588_: *mut crate::leanh::LeanObject,
    mut v_f_2589_: *mut crate::leanh::LeanObject,
    mut v_init_2590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2591_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13(v_00_u03c3_2586_, v_00_u03b2_2587_, v_map_2588_, v_f_2589_, v_init_2590_);
    crate::leanh::lean_dec_ref(v_map_2588_);
    return v_res_2591_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__10(
    mut v_00_u03b2_2592_: *mut crate::leanh::LeanObject,
    mut v_n_2593_: *mut crate::leanh::LeanObject,
    mut v_k_2594_: *mut crate::leanh::LeanObject,
    mut v_v_2595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2596_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__10___redArg(v_n_2593_, v_k_2594_, v_v_2595_);
    return v___x_2596_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__11(
    mut v_00_u03b2_2597_: *mut crate::leanh::LeanObject,
    mut v_depth_2598_: usize,
    mut v_keys_2599_: *mut crate::leanh::LeanObject,
    mut v_vals_2600_: *mut crate::leanh::LeanObject,
    mut v_heq_2601_: *mut crate::leanh::LeanObject,
    mut v_i_2602_: *mut crate::leanh::LeanObject,
    mut v_entries_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__11___redArg(v_depth_2598_, v_keys_2599_, v_vals_2600_, v_i_2602_, v_entries_2603_);
    return v___x_2604_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__11___boxed(
    mut v_00_u03b2_2605_: *mut crate::leanh::LeanObject,
    mut v_depth_2606_: *mut crate::leanh::LeanObject,
    mut v_keys_2607_: *mut crate::leanh::LeanObject,
    mut v_vals_2608_: *mut crate::leanh::LeanObject,
    mut v_heq_2609_: *mut crate::leanh::LeanObject,
    mut v_i_2610_: *mut crate::leanh::LeanObject,
    mut v_entries_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2612_: usize = 0;
    let mut v_res_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2612_ = crate::leanh::lean_unbox_usize(v_depth_2606_);
    crate::leanh::lean_dec(v_depth_2606_);
    v_res_2613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__11(v_00_u03b2_2605_, v_depth_boxed_2612_, v_keys_2607_, v_vals_2608_, v_heq_2609_, v_i_2610_, v_entries_2611_);
    crate::leanh::lean_dec_ref(v_vals_2608_);
    crate::leanh::lean_dec_ref(v_keys_2607_);
    return v_res_2613_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17(
    mut v_00_u03b2_2614_: *mut crate::leanh::LeanObject,
    mut v_x_2615_: *mut crate::leanh::LeanObject,
    mut v_x_2616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2617_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg(v_x_2615_, v_x_2616_);
    return v___x_2617_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21(
    mut v_00_u03c3_2618_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2619_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2620_: *mut crate::leanh::LeanObject,
    mut v_f_2621_: *mut crate::leanh::LeanObject,
    mut v_x_2622_: *mut crate::leanh::LeanObject,
    mut v_x_2623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2624_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21___redArg(v_f_2621_, v_x_2622_, v_x_2623_);
    return v___x_2624_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21___boxed(
    mut v_00_u03c3_2625_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2626_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2627_: *mut crate::leanh::LeanObject,
    mut v_f_2628_: *mut crate::leanh::LeanObject,
    mut v_x_2629_: *mut crate::leanh::LeanObject,
    mut v_x_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2631_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21(v_00_u03c3_2625_, v_00_u03b1_2626_, v_00_u03b2_2627_, v_f_2628_, v_x_2629_, v_x_2630_);
    crate::leanh::lean_dec_ref(v_x_2629_);
    return v_res_2631_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__10_spec__17(
    mut v_00_u03b2_2632_: *mut crate::leanh::LeanObject,
    mut v_x_2633_: *mut crate::leanh::LeanObject,
    mut v_x_2634_: *mut crate::leanh::LeanObject,
    mut v_x_2635_: *mut crate::leanh::LeanObject,
    mut v_x_2636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2637_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__10_spec__17___redArg(v_x_2633_, v_x_2634_, v_x_2635_, v_x_2636_);
    return v___x_2637_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__24(
    mut v_00_u03b1_2638_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2639_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2640_: *mut crate::leanh::LeanObject,
    mut v_f_2641_: *mut crate::leanh::LeanObject,
    mut v_as_2642_: *mut crate::leanh::LeanObject,
    mut v_i_2643_: usize,
    mut v_stop_2644_: usize,
    mut v_b_2645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__24___redArg(v_f_2641_, v_as_2642_, v_i_2643_, v_stop_2644_, v_b_2645_);
    return v___x_2646_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__24___boxed(
    mut v_00_u03b1_2647_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2648_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2649_: *mut crate::leanh::LeanObject,
    mut v_f_2650_: *mut crate::leanh::LeanObject,
    mut v_as_2651_: *mut crate::leanh::LeanObject,
    mut v_i_2652_: *mut crate::leanh::LeanObject,
    mut v_stop_2653_: *mut crate::leanh::LeanObject,
    mut v_b_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2655_: usize = 0;
    let mut v_stop_boxed_2656_: usize = 0;
    let mut v_res_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2655_ = crate::leanh::lean_unbox_usize(v_i_2652_);
    crate::leanh::lean_dec(v_i_2652_);
    v_stop_boxed_2656_ = crate::leanh::lean_unbox_usize(v_stop_2653_);
    crate::leanh::lean_dec(v_stop_2653_);
    v_res_2657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__24(v_00_u03b1_2647_, v_00_u03b2_2648_, v_00_u03c3_2649_, v_f_2650_, v_as_2651_, v_i_boxed_2655_, v_stop_boxed_2656_, v_b_2654_);
    crate::leanh::lean_dec_ref(v_as_2651_);
    return v_res_2657_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__25(
    mut v_00_u03c3_2658_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2659_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2660_: *mut crate::leanh::LeanObject,
    mut v_f_2661_: *mut crate::leanh::LeanObject,
    mut v_keys_2662_: *mut crate::leanh::LeanObject,
    mut v_vals_2663_: *mut crate::leanh::LeanObject,
    mut v_heq_2664_: *mut crate::leanh::LeanObject,
    mut v_i_2665_: *mut crate::leanh::LeanObject,
    mut v_acc_2666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__25___redArg(v_f_2661_, v_keys_2662_, v_vals_2663_, v_i_2665_, v_acc_2666_);
    return v___x_2667_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__25___boxed(
    mut v_00_u03c3_2668_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2669_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2670_: *mut crate::leanh::LeanObject,
    mut v_f_2671_: *mut crate::leanh::LeanObject,
    mut v_keys_2672_: *mut crate::leanh::LeanObject,
    mut v_vals_2673_: *mut crate::leanh::LeanObject,
    mut v_heq_2674_: *mut crate::leanh::LeanObject,
    mut v_i_2675_: *mut crate::leanh::LeanObject,
    mut v_acc_2676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2677_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__3_spec__8_spec__13_spec__21_spec__25(v_00_u03c3_2668_, v_00_u03b1_2669_, v_00_u03b2_2670_, v_f_2671_, v_keys_2672_, v_vals_2673_, v_heq_2674_, v_i_2675_, v_acc_2676_);
    crate::leanh::lean_dec_ref(v_vals_2673_);
    crate::leanh::lean_dec_ref(v_keys_2672_);
    return v_res_2677_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__3___redArg(
    mut v_a_2678_: *mut crate::leanh::LeanObject,
    mut v_x_2679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: u8 = 0;
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2679_) == 0 {
                    v___x_2680_ = crate::leanh::lean_box(0);
                    return v___x_2680_;
                } else {
                    v_key_2681_ = crate::leanh::lean_ctor_get(v_x_2679_, 0);
                    v_value_2682_ = crate::leanh::lean_ctor_get(v_x_2679_, 1);
                    v_tail_2683_ = crate::leanh::lean_ctor_get(v_x_2679_, 2);
                    v___x_2684_ = lean_name_eq(v_key_2681_, v_a_2678_);
                    if v___x_2684_ == 0 {
                        v_x_2679_ = v_tail_2683_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2682_);
                        v___x_2686_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2686_, 0, v_value_2682_);
                        return v___x_2686_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_2687_: *mut crate::leanh::LeanObject,
    mut v_x_2688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__3___redArg(v_a_2687_, v_x_2688_);
    crate::leanh::lean_dec(v_x_2688_);
    crate::leanh::lean_dec(v_a_2687_);
    return v_res_2689_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg(
    mut v_m_2690_: *mut crate::leanh::LeanObject,
    mut v_a_2691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2695_: u64 = 0;
    let mut v___x_2696_: u64 = 0;
    let mut v___x_2697_: u64 = 0;
    let mut v_fold_2698_: u64 = 0;
    let mut v___x_2699_: u64 = 0;
    let mut v___x_2700_: u64 = 0;
    let mut v___x_2701_: u64 = 0;
    let mut v___x_2702_: usize = 0;
    let mut v___x_2703_: usize = 0;
    let mut v___x_2704_: usize = 0;
    let mut v___x_2705_: usize = 0;
    let mut v___x_2706_: usize = 0;
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: u64 = 0;
    let mut v_hash_2710_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2692_ = crate::leanh::lean_ctor_get(v_m_2690_, 1);
                v___x_2693_ = lean_array_get_size(v_buckets_2692_);
                if crate::leanh::lean_obj_tag(v_a_2691_) == 0 {
                    v___x_2709_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0);
                    v___y_2695_ = v___x_2709_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2710_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_2691_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2695_ = v_hash_2710_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2696_ = 32u64;
                v___x_2697_ = lean_uint64_shift_right(v___y_2695_, v___x_2696_);
                v_fold_2698_ = lean_uint64_xor(v___y_2695_, v___x_2697_);
                v___x_2699_ = 16u64;
                v___x_2700_ = lean_uint64_shift_right(v_fold_2698_, v___x_2699_);
                v___x_2701_ = lean_uint64_xor(v_fold_2698_, v___x_2700_);
                v___x_2702_ = lean_uint64_to_usize(v___x_2701_);
                v___x_2703_ = lean_usize_of_nat(v___x_2693_);
                v___x_2704_ = 1usize;
                v___x_2705_ = lean_usize_sub(v___x_2703_, v___x_2704_);
                v___x_2706_ = lean_usize_land(v___x_2702_, v___x_2705_);
                v___x_2707_ = lean_array_uget_borrowed(v_buckets_2692_, v___x_2706_);
                v___x_2708_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__3___redArg(v_a_2691_, v___x_2707_);
                return v___x_2708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg___boxed(
    mut v_m_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg(v_m_2711_, v_a_2712_);
    crate::leanh::lean_dec(v_a_2712_);
    crate::leanh::lean_dec_ref(v_m_2711_);
    return v_res_2713_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_keys_2714_: *mut crate::leanh::LeanObject,
    mut v_vals_2715_: *mut crate::leanh::LeanObject,
    mut v_i_2716_: *mut crate::leanh::LeanObject,
    mut v_k_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: u8 = 0;
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: u8 = 0;
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2718_ = lean_array_get_size(v_keys_2714_);
                v___x_2719_ = lean_nat_dec_lt(v_i_2716_, v___x_2718_);
                if v___x_2719_ == 0 {
                    crate::leanh::lean_dec(v_i_2716_);
                    v___x_2720_ = crate::leanh::lean_box(0);
                    return v___x_2720_;
                } else {
                    v_k_x27_2721_ = lean_array_fget_borrowed(v_keys_2714_, v_i_2716_);
                    v___x_2722_ = lean_name_eq(v_k_2717_, v_k_x27_2721_);
                    if v___x_2722_ == 0 {
                        v___x_2723_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2724_ = lean_nat_add(v_i_2716_, v___x_2723_);
                        crate::leanh::lean_dec(v_i_2716_);
                        v_i_2716_ = v___x_2724_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2726_ = lean_array_fget_borrowed(v_vals_2715_, v_i_2716_);
                        crate::leanh::lean_dec(v_i_2716_);
                        crate::leanh::lean_inc(v___x_2726_);
                        v___x_2727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2727_, 0, v___x_2726_);
                        return v___x_2727_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_keys_2728_: *mut crate::leanh::LeanObject,
    mut v_vals_2729_: *mut crate::leanh::LeanObject,
    mut v_i_2730_: *mut crate::leanh::LeanObject,
    mut v_k_2731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2732_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2728_, v_vals_2729_, v_i_2730_, v_k_2731_);
    crate::leanh::lean_dec(v_k_2731_);
    crate::leanh::lean_dec_ref(v_vals_2729_);
    crate::leanh::lean_dec_ref(v_keys_2728_);
    return v_res_2732_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1___redArg(
    mut v_x_2733_: *mut crate::leanh::LeanObject,
    mut v_x_2734_: usize,
    mut v_x_2735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: usize = 0;
    let mut v___x_2739_: usize = 0;
    let mut v___x_2740_: usize = 0;
    let mut v_j_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: u8 = 0;
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: usize = 0;
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2733_) == 0 {
                    v_es_2736_ = crate::leanh::lean_ctor_get(v_x_2733_, 0);
                    v___x_2737_ = crate::leanh::lean_box(2);
                    v___x_2738_ = 5usize;
                    v___x_2739_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_2740_ = lean_usize_land(v_x_2734_, v___x_2739_);
                    v_j_2741_ = lean_usize_to_nat(v___x_2740_);
                    v___x_2742_ = lean_array_get_borrowed(v___x_2737_, v_es_2736_, v_j_2741_);
                    crate::leanh::lean_dec(v_j_2741_);
                    match crate::leanh::lean_obj_tag(v___x_2742_) {
                        0 => {
                            v_key_2743_ = crate::leanh::lean_ctor_get(v___x_2742_, 0);
                            v_val_2744_ = crate::leanh::lean_ctor_get(v___x_2742_, 1);
                            v___x_2745_ = lean_name_eq(v_x_2735_, v_key_2743_);
                            if v___x_2745_ == 0 {
                                v___x_2746_ = crate::leanh::lean_box(0);
                                return v___x_2746_;
                            } else {
                                crate::leanh::lean_inc(v_val_2744_);
                                v___x_2747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2747_, 0, v_val_2744_);
                                return v___x_2747_;
                            }
                        }
                        1 => {
                            v_node_2748_ = crate::leanh::lean_ctor_get(v___x_2742_, 0);
                            v___x_2749_ = lean_usize_shift_right(v_x_2734_, v___x_2738_);
                            v_x_2733_ = v_node_2748_;
                            v_x_2734_ = v___x_2749_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2751_ = crate::leanh::lean_box(0);
                            return v___x_2751_;
                        }
                    }
                } else {
                    v_ks_2752_ = crate::leanh::lean_ctor_get(v_x_2733_, 0);
                    v_vs_2753_ = crate::leanh::lean_ctor_get(v_x_2733_, 1);
                    v___x_2754_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2755_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_2752_, v_vs_2753_, v___x_2754_, v_x_2735_);
                    return v___x_2755_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2756_: *mut crate::leanh::LeanObject,
    mut v_x_2757_: *mut crate::leanh::LeanObject,
    mut v_x_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_363__boxed_2759_: usize = 0;
    let mut v_res_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_363__boxed_2759_ = crate::leanh::lean_unbox_usize(v_x_2757_);
    crate::leanh::lean_dec(v_x_2757_);
    v_res_2760_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1___redArg(v_x_2756_, v_x_363__boxed_2759_, v_x_2758_);
    crate::leanh::lean_dec(v_x_2758_);
    crate::leanh::lean_dec_ref(v_x_2756_);
    return v_res_2760_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg(
    mut v_x_2761_: *mut crate::leanh::LeanObject,
    mut v_x_2762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2764_: u64 = 0;
    let mut v___x_2765_: usize = 0;
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: u64 = 0;
    let mut v_hash_2768_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2762_) == 0 {
                    v___x_2767_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0);
                    v___y_2764_ = v___x_2767_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2768_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_2762_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2764_ = v_hash_2768_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2765_ = lean_uint64_to_usize(v___y_2764_);
                v___x_2766_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1___redArg(v_x_2761_, v___x_2765_, v_x_2762_);
                return v___x_2766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg___boxed(
    mut v_x_2769_: *mut crate::leanh::LeanObject,
    mut v_x_2770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2771_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg(v_x_2769_, v_x_2770_);
    crate::leanh::lean_dec(v_x_2770_);
    crate::leanh::lean_dec_ref(v_x_2769_);
    return v_res_2771_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0___redArg(
    mut v_x_2772_: *mut crate::leanh::LeanObject,
    mut v_x_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stage_u2081_2774_: u8 = 0;
    v_stage_u2081_2774_ = crate::leanh::lean_ctor_get_uint8(
        v_x_2772_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_2774_ == 0 {
        let mut v_map_u2081_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_2775_ = crate::leanh::lean_ctor_get(v_x_2772_, 0);
        v_map_u2082_2776_ = crate::leanh::lean_ctor_get(v_x_2772_, 1);
        v___x_2777_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg(v_map_u2082_2776_, v_x_2773_);
        if crate::leanh::lean_obj_tag(v___x_2777_) == 0 {
            let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2778_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg(v_map_u2081_2775_, v_x_2773_);
            return v___x_2778_;
        } else {
            return v___x_2777_;
        }
    } else {
        let mut v_map_u2081_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_2779_ = crate::leanh::lean_ctor_get(v_x_2772_, 0);
        v___x_2780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg(v_map_u2081_2779_, v_x_2773_);
        return v___x_2780_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0___redArg___boxed(
    mut v_x_2781_: *mut crate::leanh::LeanObject,
    mut v_x_2782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2783_ = l_Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0___redArg(
        v_x_2781_, v_x_2782_,
    );
    crate::leanh::lean_dec(v_x_2782_);
    crate::leanh::lean_dec_ref(v_x_2781_);
    return v_res_2783_;
}
pub unsafe fn _init_l_Lean_Environment_registerNamespace___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2786_ = l_Lean_Environment_registerNamespace___closed__1;
    v___x_2787_ = l_Lean_Environment_registerNamespace___closed__0;
    v___x_2788_ = l_Lean_SMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2787_,
        v___x_2786_,
    );
    return v___x_2788_;
}
pub unsafe fn l_Lean_Environment_registerNamespace(
    mut v_env_2789_: *mut crate::leanh::LeanObject,
    mut v_n_2790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2791_ = l___private_Lean_Namespace_0__Lean_namespacesExt;
    v_toEnvExtension_2792_ = crate::leanh::lean_ctor_get(v___x_2791_, 0);
    v_asyncMode_2793_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2792_, 2);
    v___x_2794_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Environment_registerNamespace___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Environment_registerNamespace___closed__2_once),
        _init_l_Lean_Environment_registerNamespace___closed__2,
    );
    v___x_2795_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc_ref(v_env_2789_);
    v___x_2796_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_2794_,
        v___x_2791_,
        v_env_2789_,
        v_asyncMode_2793_,
        v___x_2795_,
    );
    v___x_2797_ = l_Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0___redArg(
        v___x_2796_,
        v_n_2790_,
    );
    crate::leanh::lean_dec(v___x_2796_);
    if crate::leanh::lean_obj_tag(v___x_2797_) == 0 {
        let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2798_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
            v___x_2791_,
            v_env_2789_,
            v_n_2790_,
            v_asyncMode_2793_,
            v___x_2795_,
        );
        return v___x_2798_;
    } else {
        let mut v_val_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2800_: u8 = 0;
        let mut v___x_2801_: u8 = 0;
        let mut v___x_2802_: u8 = 0;
        v_val_2799_ = crate::leanh::lean_ctor_get(v___x_2797_, 0);
        crate::leanh::lean_inc(v_val_2799_);
        crate::leanh::lean_dec_ref_known(v___x_2797_, 1);
        v___x_2800_ = 1;
        v___x_2801_ = (crate::leanh::lean_unbox(v_val_2799_) as u8);
        crate::leanh::lean_dec(v_val_2799_);
        v___x_2802_ = l_Lean_Environment_instBEqVisibility_beq(v___x_2801_, v___x_2800_);
        if v___x_2802_ == 0 {
            let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2803_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                v___x_2791_,
                v_env_2789_,
                v_n_2790_,
                v_asyncMode_2793_,
                v___x_2795_,
            );
            return v___x_2803_;
        } else {
            crate::leanh::lean_dec(v_n_2790_);
            return v_env_2789_;
        }
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0(
    mut v_00_u03b2_2804_: *mut crate::leanh::LeanObject,
    mut v_x_2805_: *mut crate::leanh::LeanObject,
    mut v_x_2806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2807_ = l_Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0___redArg(
        v_x_2805_, v_x_2806_,
    );
    return v___x_2807_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0___boxed(
    mut v_00_u03b2_2808_: *mut crate::leanh::LeanObject,
    mut v_x_2809_: *mut crate::leanh::LeanObject,
    mut v_x_2810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2811_ = l_Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0(
        v_00_u03b2_2808_,
        v_x_2809_,
        v_x_2810_,
    );
    crate::leanh::lean_dec(v_x_2810_);
    crate::leanh::lean_dec_ref(v_x_2809_);
    return v_res_2811_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0(
    mut v_00_u03b2_2812_: *mut crate::leanh::LeanObject,
    mut v_x_2813_: *mut crate::leanh::LeanObject,
    mut v_x_2814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2815_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0___redArg(v_x_2813_, v_x_2814_);
    return v___x_2815_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0___boxed(
    mut v_00_u03b2_2816_: *mut crate::leanh::LeanObject,
    mut v_x_2817_: *mut crate::leanh::LeanObject,
    mut v_x_2818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2819_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0(v_00_u03b2_2816_, v_x_2817_, v_x_2818_);
    crate::leanh::lean_dec(v_x_2818_);
    crate::leanh::lean_dec_ref(v_x_2817_);
    return v_res_2819_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1(
    mut v_00_u03b2_2820_: *mut crate::leanh::LeanObject,
    mut v_m_2821_: *mut crate::leanh::LeanObject,
    mut v_a_2822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2823_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1___redArg(v_m_2821_, v_a_2822_);
    return v___x_2823_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1___boxed(
    mut v_00_u03b2_2824_: *mut crate::leanh::LeanObject,
    mut v_m_2825_: *mut crate::leanh::LeanObject,
    mut v_a_2826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1(v_00_u03b2_2824_, v_m_2825_, v_a_2826_);
    crate::leanh::lean_dec(v_a_2826_);
    crate::leanh::lean_dec_ref(v_m_2825_);
    return v_res_2827_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2828_: *mut crate::leanh::LeanObject,
    mut v_x_2829_: *mut crate::leanh::LeanObject,
    mut v_x_2830_: usize,
    mut v_x_2831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2832_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1___redArg(v_x_2829_, v_x_2830_, v_x_2831_);
    return v___x_2832_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2833_: *mut crate::leanh::LeanObject,
    mut v_x_2834_: *mut crate::leanh::LeanObject,
    mut v_x_2835_: *mut crate::leanh::LeanObject,
    mut v_x_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_507__boxed_2837_: usize = 0;
    let mut v_res_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_507__boxed_2837_ = crate::leanh::lean_unbox_usize(v_x_2835_);
    crate::leanh::lean_dec(v_x_2835_);
    v_res_2838_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1(v_00_u03b2_2833_, v_x_2834_, v_x_507__boxed_2837_, v_x_2836_);
    crate::leanh::lean_dec(v_x_2836_);
    crate::leanh::lean_dec_ref(v_x_2834_);
    return v_res_2838_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2839_: *mut crate::leanh::LeanObject,
    mut v_a_2840_: *mut crate::leanh::LeanObject,
    mut v_x_2841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2842_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__3___redArg(v_a_2840_, v_x_2841_);
    return v___x_2842_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2843_: *mut crate::leanh::LeanObject,
    mut v_a_2844_: *mut crate::leanh::LeanObject,
    mut v_x_2845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2846_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__1_spec__3(v_00_u03b2_2843_, v_a_2844_, v_x_2845_);
    crate::leanh::lean_dec(v_x_2845_);
    crate::leanh::lean_dec(v_a_2844_);
    return v_res_2846_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2847_: *mut crate::leanh::LeanObject,
    mut v_keys_2848_: *mut crate::leanh::LeanObject,
    mut v_vals_2849_: *mut crate::leanh::LeanObject,
    mut v_heq_2850_: *mut crate::leanh::LeanObject,
    mut v_i_2851_: *mut crate::leanh::LeanObject,
    mut v_k_2852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2853_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_2848_, v_vals_2849_, v_i_2851_, v_k_2852_);
    return v___x_2853_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_2854_: *mut crate::leanh::LeanObject,
    mut v_keys_2855_: *mut crate::leanh::LeanObject,
    mut v_vals_2856_: *mut crate::leanh::LeanObject,
    mut v_heq_2857_: *mut crate::leanh::LeanObject,
    mut v_i_2858_: *mut crate::leanh::LeanObject,
    mut v_k_2859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2860_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Environment_registerNamespace_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2854_, v_keys_2855_, v_vals_2856_, v_heq_2857_, v_i_2858_, v_k_2859_);
    crate::leanh::lean_dec(v_k_2859_);
    crate::leanh::lean_dec_ref(v_vals_2856_);
    crate::leanh::lean_dec_ref(v_keys_2855_);
    return v_res_2860_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__0___redArg(
    mut v_m_2861_: *mut crate::leanh::LeanObject,
    mut v_a_2862_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2866_: u64 = 0;
    let mut v___x_2867_: u64 = 0;
    let mut v___x_2868_: u64 = 0;
    let mut v_fold_2869_: u64 = 0;
    let mut v___x_2870_: u64 = 0;
    let mut v___x_2871_: u64 = 0;
    let mut v___x_2872_: u64 = 0;
    let mut v___x_2873_: usize = 0;
    let mut v___x_2874_: usize = 0;
    let mut v___x_2875_: usize = 0;
    let mut v___x_2876_: usize = 0;
    let mut v___x_2877_: usize = 0;
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: u8 = 0;
    let mut v___x_2880_: u64 = 0;
    let mut v_hash_2881_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2863_ = crate::leanh::lean_ctor_get(v_m_2861_, 1);
                v___x_2864_ = lean_array_get_size(v_buckets_2863_);
                if crate::leanh::lean_obj_tag(v_a_2862_) == 0 {
                    v___x_2880_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0);
                    v___y_2866_ = v___x_2880_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2881_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_2862_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2866_ = v_hash_2881_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2867_ = 32u64;
                v___x_2868_ = lean_uint64_shift_right(v___y_2866_, v___x_2867_);
                v_fold_2869_ = lean_uint64_xor(v___y_2866_, v___x_2868_);
                v___x_2870_ = 16u64;
                v___x_2871_ = lean_uint64_shift_right(v_fold_2869_, v___x_2870_);
                v___x_2872_ = lean_uint64_xor(v_fold_2869_, v___x_2871_);
                v___x_2873_ = lean_uint64_to_usize(v___x_2872_);
                v___x_2874_ = lean_usize_of_nat(v___x_2864_);
                v___x_2875_ = 1usize;
                v___x_2876_ = lean_usize_sub(v___x_2874_, v___x_2875_);
                v___x_2877_ = lean_usize_land(v___x_2873_, v___x_2876_);
                v___x_2878_ = lean_array_uget_borrowed(v_buckets_2863_, v___x_2877_);
                v___x_2879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__3___redArg(v_a_2862_, v___x_2878_);
                return v___x_2879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__0___redArg___boxed(
    mut v_m_2882_: *mut crate::leanh::LeanObject,
    mut v_a_2883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2884_: u8 = 0;
    let mut v_r_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2884_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__0___redArg(v_m_2882_, v_a_2883_);
    crate::leanh::lean_dec(v_a_2883_);
    crate::leanh::lean_dec_ref(v_m_2882_);
    v_r_2885_ = crate::leanh::lean_box((v_res_2884_) as usize);
    return v_r_2885_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_keys_2886_: *mut crate::leanh::LeanObject,
    mut v_i_2887_: *mut crate::leanh::LeanObject,
    mut v_k_2888_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: u8 = 0;
    let mut v_k_x27_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2889_ = lean_array_get_size(v_keys_2886_);
                v___x_2890_ = lean_nat_dec_lt(v_i_2887_, v___x_2889_);
                if v___x_2890_ == 0 {
                    crate::leanh::lean_dec(v_i_2887_);
                    return v___x_2890_;
                } else {
                    v_k_x27_2891_ = lean_array_fget_borrowed(v_keys_2886_, v_i_2887_);
                    v___x_2892_ = lean_name_eq(v_k_2888_, v_k_x27_2891_);
                    if v___x_2892_ == 0 {
                        v___x_2893_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2894_ = lean_nat_add(v_i_2887_, v___x_2893_);
                        crate::leanh::lean_dec(v_i_2887_);
                        v_i_2887_ = v___x_2894_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_2887_);
                        return v___x_2892_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_2896_: *mut crate::leanh::LeanObject,
    mut v_i_2897_: *mut crate::leanh::LeanObject,
    mut v_k_2898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2899_: u8 = 0;
    let mut v_r_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2899_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2896_, v_i_2897_, v_k_2898_);
    crate::leanh::lean_dec(v_k_2898_);
    crate::leanh::lean_dec_ref(v_keys_2896_);
    v_r_2900_ = crate::leanh::lean_box((v_res_2899_) as usize);
    return v_r_2900_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2___redArg(
    mut v_x_2901_: *mut crate::leanh::LeanObject,
    mut v_x_2902_: usize,
    mut v_x_2903_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: usize = 0;
    let mut v___x_2907_: usize = 0;
    let mut v___x_2908_: usize = 0;
    let mut v_j_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: u8 = 0;
    let mut v_node_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: usize = 0;
    let mut v___x_2916_: u8 = 0;
    let mut v_ks_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2901_) == 0 {
                    v_es_2904_ = crate::leanh::lean_ctor_get(v_x_2901_, 0);
                    v___x_2905_ = crate::leanh::lean_box(2);
                    v___x_2906_ = 5usize;
                    v___x_2907_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_2908_ = lean_usize_land(v_x_2902_, v___x_2907_);
                    v_j_2909_ = lean_usize_to_nat(v___x_2908_);
                    v___x_2910_ = lean_array_get_borrowed(v___x_2905_, v_es_2904_, v_j_2909_);
                    crate::leanh::lean_dec(v_j_2909_);
                    match crate::leanh::lean_obj_tag(v___x_2910_) {
                        0 => {
                            v_key_2911_ = crate::leanh::lean_ctor_get(v___x_2910_, 0);
                            v___x_2912_ = lean_name_eq(v_x_2903_, v_key_2911_);
                            return v___x_2912_;
                        }
                        1 => {
                            v_node_2913_ = crate::leanh::lean_ctor_get(v___x_2910_, 0);
                            v___x_2914_ = lean_usize_shift_right(v_x_2902_, v___x_2906_);
                            v_x_2901_ = v_node_2913_;
                            v_x_2902_ = v___x_2914_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2916_ = 0;
                            return v___x_2916_;
                        }
                    }
                } else {
                    v_ks_2917_ = crate::leanh::lean_ctor_get(v_x_2901_, 0);
                    v___x_2918_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2919_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_2917_, v___x_2918_, v_x_2903_);
                    return v___x_2919_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_x_2920_: *mut crate::leanh::LeanObject,
    mut v_x_2921_: *mut crate::leanh::LeanObject,
    mut v_x_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_266__boxed_2923_: usize = 0;
    let mut v_res_2924_: u8 = 0;
    let mut v_r_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_266__boxed_2923_ = crate::leanh::lean_unbox_usize(v_x_2921_);
    crate::leanh::lean_dec(v_x_2921_);
    v_res_2924_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2___redArg(v_x_2920_, v_x_266__boxed_2923_, v_x_2922_);
    crate::leanh::lean_dec(v_x_2922_);
    crate::leanh::lean_dec_ref(v_x_2920_);
    v_r_2925_ = crate::leanh::lean_box((v_res_2924_) as usize);
    return v_r_2925_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1___redArg(
    mut v_x_2926_: *mut crate::leanh::LeanObject,
    mut v_x_2927_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2929_: u64 = 0;
    let mut v___x_2930_: usize = 0;
    let mut v___x_2931_: u8 = 0;
    let mut v___x_2932_: u64 = 0;
    let mut v_hash_2933_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2927_) == 0 {
                    v___x_2932_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00__private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2__spec__1_spec__4_spec__8_spec__17___redArg___closed__0);
                    v___y_2929_ = v___x_2932_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2933_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_2927_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2929_ = v_hash_2933_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2930_ = lean_uint64_to_usize(v___y_2929_);
                v___x_2931_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2___redArg(v_x_2926_, v___x_2930_, v_x_2927_);
                return v___x_2931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1___redArg___boxed(
    mut v_x_2934_: *mut crate::leanh::LeanObject,
    mut v_x_2935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2936_: u8 = 0;
    let mut v_r_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2936_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1___redArg(v_x_2934_, v_x_2935_);
    crate::leanh::lean_dec(v_x_2935_);
    crate::leanh::lean_dec_ref(v_x_2934_);
    v_r_2937_ = crate::leanh::lean_box((v_res_2936_) as usize);
    return v_r_2937_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0___redArg(
    mut v_x_2938_: *mut crate::leanh::LeanObject,
    mut v_x_2939_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_stage_u2081_2940_: u8 = 0;
    v_stage_u2081_2940_ = crate::leanh::lean_ctor_get_uint8(
        v_x_2938_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_2940_ == 0 {
        let mut v_map_u2081_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2943_: u8 = 0;
        v_map_u2081_2941_ = crate::leanh::lean_ctor_get(v_x_2938_, 0);
        v_map_u2082_2942_ = crate::leanh::lean_ctor_get(v_x_2938_, 1);
        v___x_2943_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__0___redArg(v_map_u2081_2941_, v_x_2939_);
        if v___x_2943_ == 0 {
            let mut v___x_2944_: u8 = 0;
            v___x_2944_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1___redArg(v_map_u2082_2942_, v_x_2939_);
            return v___x_2944_;
        } else {
            return v___x_2943_;
        }
    } else {
        let mut v_map_u2081_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2946_: u8 = 0;
        v_map_u2081_2945_ = crate::leanh::lean_ctor_get(v_x_2938_, 0);
        v___x_2946_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__0___redArg(v_map_u2081_2945_, v_x_2939_);
        return v___x_2946_;
    }
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0___redArg___boxed(
    mut v_x_2947_: *mut crate::leanh::LeanObject,
    mut v_x_2948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2949_: u8 = 0;
    let mut v_r_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2949_ = l_Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0___redArg(
        v_x_2947_, v_x_2948_,
    );
    crate::leanh::lean_dec(v_x_2948_);
    crate::leanh::lean_dec_ref(v_x_2947_);
    v_r_2950_ = crate::leanh::lean_box((v_res_2949_) as usize);
    return v_r_2950_;
}
pub unsafe fn l_Lean_Environment_isNamespace(
    mut v_env_2951_: *mut crate::leanh::LeanObject,
    mut v_n_2952_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    v___x_2953_ = l___private_Lean_Namespace_0__Lean_namespacesExt;
    v_toEnvExtension_2954_ = crate::leanh::lean_ctor_get(v___x_2953_, 0);
    v_asyncMode_2955_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2954_, 2);
    v___x_2956_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Environment_registerNamespace___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Environment_registerNamespace___closed__2_once),
        _init_l_Lean_Environment_registerNamespace___closed__2,
    );
    v___x_2957_ = crate::leanh::lean_box(0);
    v___x_2958_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_2956_,
        v___x_2953_,
        v_env_2951_,
        v_asyncMode_2955_,
        v___x_2957_,
    );
    v___x_2959_ = l_Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0___redArg(
        v___x_2958_,
        v_n_2952_,
    );
    crate::leanh::lean_dec(v___x_2958_);
    return v___x_2959_;
}
pub unsafe fn l_Lean_Environment_isNamespace___boxed(
    mut v_env_2960_: *mut crate::leanh::LeanObject,
    mut v_n_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2962_: u8 = 0;
    let mut v_r_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2962_ = l_Lean_Environment_isNamespace(v_env_2960_, v_n_2961_);
    crate::leanh::lean_dec(v_n_2961_);
    v_r_2963_ = crate::leanh::lean_box((v_res_2962_) as usize);
    return v_r_2963_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0(
    mut v_00_u03b2_2964_: *mut crate::leanh::LeanObject,
    mut v_x_2965_: *mut crate::leanh::LeanObject,
    mut v_x_2966_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2967_: u8 = 0;
    v___x_2967_ = l_Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0___redArg(
        v_x_2965_, v_x_2966_,
    );
    return v___x_2967_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0___boxed(
    mut v_00_u03b2_2968_: *mut crate::leanh::LeanObject,
    mut v_x_2969_: *mut crate::leanh::LeanObject,
    mut v_x_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2971_: u8 = 0;
    let mut v_r_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0(
        v_00_u03b2_2968_,
        v_x_2969_,
        v_x_2970_,
    );
    crate::leanh::lean_dec(v_x_2970_);
    crate::leanh::lean_dec_ref(v_x_2969_);
    v_r_2972_ = crate::leanh::lean_box((v_res_2971_) as usize);
    return v_r_2972_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__0(
    mut v_00_u03b2_2973_: *mut crate::leanh::LeanObject,
    mut v_m_2974_: *mut crate::leanh::LeanObject,
    mut v_a_2975_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2976_: u8 = 0;
    v___x_2976_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__0___redArg(v_m_2974_, v_a_2975_);
    return v___x_2976_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__0___boxed(
    mut v_00_u03b2_2977_: *mut crate::leanh::LeanObject,
    mut v_m_2978_: *mut crate::leanh::LeanObject,
    mut v_a_2979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2980_: u8 = 0;
    let mut v_r_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2980_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__0(v_00_u03b2_2977_, v_m_2978_, v_a_2979_);
    crate::leanh::lean_dec(v_a_2979_);
    crate::leanh::lean_dec_ref(v_m_2978_);
    v_r_2981_ = crate::leanh::lean_box((v_res_2980_) as usize);
    return v_r_2981_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1(
    mut v_00_u03b2_2982_: *mut crate::leanh::LeanObject,
    mut v_x_2983_: *mut crate::leanh::LeanObject,
    mut v_x_2984_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2985_: u8 = 0;
    v___x_2985_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1___redArg(v_x_2983_, v_x_2984_);
    return v___x_2985_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1___boxed(
    mut v_00_u03b2_2986_: *mut crate::leanh::LeanObject,
    mut v_x_2987_: *mut crate::leanh::LeanObject,
    mut v_x_2988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2989_: u8 = 0;
    let mut v_r_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2989_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1(v_00_u03b2_2986_, v_x_2987_, v_x_2988_);
    crate::leanh::lean_dec(v_x_2988_);
    crate::leanh::lean_dec_ref(v_x_2987_);
    v_r_2990_ = crate::leanh::lean_box((v_res_2989_) as usize);
    return v_r_2990_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2991_: *mut crate::leanh::LeanObject,
    mut v_x_2992_: *mut crate::leanh::LeanObject,
    mut v_x_2993_: usize,
    mut v_x_2994_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2995_: u8 = 0;
    v___x_2995_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2___redArg(v_x_2992_, v_x_2993_, v_x_2994_);
    return v___x_2995_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_2996_: *mut crate::leanh::LeanObject,
    mut v_x_2997_: *mut crate::leanh::LeanObject,
    mut v_x_2998_: *mut crate::leanh::LeanObject,
    mut v_x_2999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_383__boxed_3000_: usize = 0;
    let mut v_res_3001_: u8 = 0;
    let mut v_r_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_383__boxed_3000_ = crate::leanh::lean_unbox_usize(v_x_2998_);
    crate::leanh::lean_dec(v_x_2998_);
    v_res_3001_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2(v_00_u03b2_2996_, v_x_2997_, v_x_383__boxed_3000_, v_x_2999_);
    crate::leanh::lean_dec(v_x_2999_);
    crate::leanh::lean_dec_ref(v_x_2997_);
    v_r_3002_ = crate::leanh::lean_box((v_res_3001_) as usize);
    return v_r_3002_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3003_: *mut crate::leanh::LeanObject,
    mut v_keys_3004_: *mut crate::leanh::LeanObject,
    mut v_vals_3005_: *mut crate::leanh::LeanObject,
    mut v_heq_3006_: *mut crate::leanh::LeanObject,
    mut v_i_3007_: *mut crate::leanh::LeanObject,
    mut v_k_3008_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3009_: u8 = 0;
    v___x_3009_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_3004_, v_i_3007_, v_k_3008_);
    return v___x_3009_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_3010_: *mut crate::leanh::LeanObject,
    mut v_keys_3011_: *mut crate::leanh::LeanObject,
    mut v_vals_3012_: *mut crate::leanh::LeanObject,
    mut v_heq_3013_: *mut crate::leanh::LeanObject,
    mut v_i_3014_: *mut crate::leanh::LeanObject,
    mut v_k_3015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3016_: u8 = 0;
    let mut v_r_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3016_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Environment_isNamespace_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_3010_, v_keys_3011_, v_vals_3012_, v_heq_3013_, v_i_3014_, v_k_3015_);
    crate::leanh::lean_dec(v_k_3015_);
    crate::leanh::lean_dec_ref(v_vals_3012_);
    crate::leanh::lean_dec_ref(v_keys_3011_);
    v_r_3017_ = crate::leanh::lean_box((v_res_3016_) as usize);
    return v_r_3017_;
}
pub unsafe fn l_Lean_SMap_iter___at___00Lean_Environment_getNamespaces_spec__0___redArg(
    mut v_s_3018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_u2081_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3034_: u8 = 0;
    let mut v_unused_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_u2081_3019_ = crate::leanh::lean_ctor_get(v_s_3018_, 0);
                crate::leanh::lean_inc_ref(v_map_u2081_3019_);
                v_map_u2082_3020_ = crate::leanh::lean_ctor_get(v_s_3018_, 1);
                crate::leanh::lean_inc_ref(v_map_u2082_3020_);
                crate::leanh::lean_dec_ref(v_s_3018_);
                v_buckets_3021_ = crate::leanh::lean_ctor_get(v_map_u2081_3019_, 1);
                v_isSharedCheck_3034_ = (!crate::leanh::lean_is_exclusive(v_map_u2081_3019_)) as u8;
                if v_isSharedCheck_3034_ == 0 {
                    v_unused_3035_ = crate::leanh::lean_ctor_get(v_map_u2081_3019_, 0);
                    crate::leanh::lean_dec(v_unused_3035_);
                    v___x_3023_ = v_map_u2081_3019_;
                    v_isShared_3024_ = v_isSharedCheck_3034_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3021_);
                    crate::leanh::lean_dec(v_map_u2081_3019_);
                    v___x_3023_ = crate::leanh::lean_box(0);
                    v_isShared_3024_ = v_isSharedCheck_3034_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3025_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_3024_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3023_, 1, v___x_3025_);
                    crate::leanh::lean_ctor_set(v___x_3023_, 0, v_buckets_3021_);
                    v___x_3027_ = v___x_3023_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3033_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_buckets_3021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3025_);
                    v___x_3027_ = v_reuseFailAlloc_3033_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3028_ = crate::leanh::lean_box(0);
                v___x_3029_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3029_, 0, v___x_3027_);
                crate::leanh::lean_ctor_set(v___x_3029_, 1, v___x_3028_);
                v___x_3030_ = crate::leanh::lean_box(0);
                v___x_3031_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(
                    v_map_u2082_3020_,
                    v___x_3030_,
                );
                v___x_3032_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3032_, 0, v___x_3029_);
                crate::leanh::lean_ctor_set(v___x_3032_, 1, v___x_3031_);
                return v___x_3032_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_iter___at___00Lean_Environment_getNamespaces_spec__0(
    mut v_00_u03b2_3036_: *mut crate::leanh::LeanObject,
    mut v_s_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3038_ =
        l_Lean_SMap_iter___at___00Lean_Environment_getNamespaces_spec__0___redArg(v_s_3037_);
    return v___x_3038_;
}
pub unsafe fn l_Lean_Environment_getNamespaces(
    mut v_env_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3040_ = l___private_Lean_Namespace_0__Lean_namespacesExt;
    v_toEnvExtension_3041_ = crate::leanh::lean_ctor_get(v___x_3040_, 0);
    v_asyncMode_3042_ = crate::leanh::lean_ctor_get(v_toEnvExtension_3041_, 2);
    v___x_3043_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Environment_registerNamespace___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Environment_registerNamespace___closed__2_once),
        _init_l_Lean_Environment_registerNamespace___closed__2,
    );
    v___x_3044_ = crate::leanh::lean_box(0);
    v___x_3045_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_3043_,
        v___x_3040_,
        v_env_3039_,
        v_asyncMode_3042_,
        v___x_3044_,
    );
    v___x_3046_ =
        l_Lean_SMap_iter___at___00Lean_Environment_getNamespaces_spec__0___redArg(v___x_3045_);
    return v___x_3046_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Namespace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Namespace_0__Lean_initFn_00___x40_Lean_Namespace_1373626441____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Namespace_0__Lean_namespacesExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Namespace_0__Lean_namespacesExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Namespace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Namespace(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_EnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Namespace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Namespace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Namespace(builtin);
}
