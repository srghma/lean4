// Lean compiler output
// Module: Lean.Meta.Sym.AbstractS
// Imports: Lean.Meta.Sym.SymM Lean.Meta.Sym.ReplaceS Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_uget_borrowed, lean_mk_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub, lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_mix_hash, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
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
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instMonad___redArg, l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_find_x3f___redArg, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_bvar___override, l_Lean_Expr_forallE___override,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasFVar, l_Lean_Expr_lam___override,
    l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override,
    l_Lean_instBEqFVarId_beq, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_binderInfo, l_Lean_LocalDecl_index, l_Lean_LocalDecl_type,
    l_Lean_LocalDecl_userName, l_Lean_instInhabitedLocalDecl_default, lean_local_ctx_find,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_FVarId_getDecl___redArg;
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    l_Lean_Meta_Sym_Internal_Builder_assertShared,
    l_Lean_Meta_Sym_Internal_Builder_share1___redArg, l_Lean_Meta_Sym_Internal_Sym_assertShared,
    l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
    l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM,
    l_Lean_Meta_Sym_Internal_mkBVarS___redArg,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1, l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed,
};
use crate::r#gen::Lean::Meta::Sym::ReplaceS::{
    initialize_Lean_Meta_Sym_ReplaceS, l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save,
    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit,
    runtime_initialize_Lean_Meta_Sym_ReplaceS,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
pub static l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1: usize = 0;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1449_ =
        l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2;
    v___x_1450_ = leanh::lean_unsigned_to_nat(14);
    v___x_1451_ = leanh::lean_unsigned_to_nat(22);
    v___x_1452_ =
        l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1;
    v___x_1453_ =
        l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0;
    v___x_1454_ = l_mkPanicMessageWithDecl(
        v___x_1453_,
        v___x_1452_,
        v___x_1451_,
        v___x_1450_,
        v___x_1449_,
    );
    return v___x_1454_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(
    mut v_toDeBruijn_x3f_1457_: *mut leanh::LeanObject,
    mut v___x_1458_: *mut leanh::LeanObject,
    mut v_maxFVar_1459_: *mut leanh::LeanObject,
    mut v_minIndex_1460_: *mut leanh::LeanObject,
    mut v_lctx_1461_: *mut leanh::LeanObject,
    mut v___x_1462_: *mut leanh::LeanObject,
    mut v_e_1463_: *mut leanh::LeanObject,
    mut v_offset_1464_: *mut leanh::LeanObject,
    mut v___y_1465_: u8,
    mut v___y_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxIndex_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: u8 = 0;
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1486_: u8 = 0;
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873__overap_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1495_: u8 = 0;
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1502_: u8 = 0;
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_1463_) {
                1 => {
                    leanh::lean_dec_ref(v_lctx_1461_);
                    v_fvarId_1481_ = leanh::lean_ctor_get(v_e_1463_, 0);
                    leanh::lean_inc(v_fvarId_1481_);
                    v___x_1482_ =
                        leanh::lean_apply_1(v_toDeBruijn_x3f_1457_, v_fvarId_1481_);
                    if leanh::lean_obj_tag(v___x_1482_) == 1 {
                        leanh::lean_dec_ref_known(v_e_1463_, 1);
                        v_val_1483_ = leanh::lean_ctor_get(v___x_1482_, 0);
                        v_isSharedCheck_1503_ =
                            (!leanh::lean_is_exclusive(v___x_1482_)) as u8;
                        if v_isSharedCheck_1503_ == 0 {
                            v___x_1485_ = v___x_1482_;
                            v_isShared_1486_ = v_isSharedCheck_1503_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1483_);
                            leanh::lean_dec(v___x_1482_);
                            v___x_1485_ = leanh::lean_box(0);
                            v_isShared_1486_ = v_isSharedCheck_1503_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1482_);
                        leanh::lean_dec_ref(v___x_1458_);
                        v___x_1504_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1504_, 0, v_e_1463_);
                        v___x_1505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
                        leanh::lean_ctor_set(v___x_1505_, 1, v___y_1466_);
                        return v___x_1505_;
                    }
                }
                9 => {
                    leanh::lean_dec_ref(v_lctx_1461_);
                    leanh::lean_dec_ref(v___x_1458_);
                    leanh::lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1506_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1506_, 0, v_e_1463_);
                    v___x_1507_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1507_, 0, v___x_1506_);
                    leanh::lean_ctor_set(v___x_1507_, 1, v___y_1466_);
                    return v___x_1507_;
                }
                2 => {
                    leanh::lean_dec_ref(v_lctx_1461_);
                    leanh::lean_dec_ref(v___x_1458_);
                    leanh::lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1508_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1508_, 0, v_e_1463_);
                    v___x_1509_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1509_, 0, v___x_1508_);
                    leanh::lean_ctor_set(v___x_1509_, 1, v___y_1466_);
                    return v___x_1509_;
                }
                0 => {
                    leanh::lean_dec_ref(v_lctx_1461_);
                    leanh::lean_dec_ref(v___x_1458_);
                    leanh::lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1510_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1510_, 0, v_e_1463_);
                    v___x_1511_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1511_, 0, v___x_1510_);
                    leanh::lean_ctor_set(v___x_1511_, 1, v___y_1466_);
                    return v___x_1511_;
                }
                4 => {
                    leanh::lean_dec_ref(v_lctx_1461_);
                    leanh::lean_dec_ref(v___x_1458_);
                    leanh::lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1512_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1512_, 0, v_e_1463_);
                    v___x_1513_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
                    leanh::lean_ctor_set(v___x_1513_, 1, v___y_1466_);
                    return v___x_1513_;
                }
                3 => {
                    leanh::lean_dec_ref(v_lctx_1461_);
                    leanh::lean_dec_ref(v___x_1458_);
                    leanh::lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1514_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1514_, 0, v_e_1463_);
                    v___x_1515_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1515_, 0, v___x_1514_);
                    leanh::lean_ctor_set(v___x_1515_, 1, v___y_1466_);
                    return v___x_1515_;
                }
                _ => {
                    leanh::lean_dec_ref(v___x_1458_);
                    leanh::lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1516_ = l_Lean_Expr_hasFVar(v_e_1463_);
                    if v___x_1516_ == 0 {
                        leanh::lean_dec_ref(v_lctx_1461_);
                        v___x_1517_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1517_, 0, v_e_1463_);
                        v___x_1518_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1518_, 0, v___x_1517_);
                        leanh::lean_ctor_set(v___x_1518_, 1, v___y_1466_);
                        return v___x_1518_;
                    } else {
                        v___f_1519_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4;
                        v___f_1520_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5;
                        leanh::lean_inc_ref(v_e_1463_);
                        v___x_1521_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                            v___f_1519_,
                            v___f_1520_,
                            v_maxFVar_1459_,
                            v_e_1463_,
                        );
                        if leanh::lean_obj_tag(v___x_1521_) == 1 {
                            v_val_1522_ = leanh::lean_ctor_get(v___x_1521_, 0);
                            leanh::lean_inc(v_val_1522_);
                            leanh::lean_dec_ref_known(v___x_1521_, 1);
                            if leanh::lean_obj_tag(v_val_1522_) == 0 {
                                v___x_1523_ = leanh::lean_box(0);
                                v___x_1524_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                                v___x_1525_ = l_panic___redArg(v___x_1523_, v___x_1524_);
                                v___y_1476_ = v___x_1525_;
                                state = 2;
                                continue;
                            } else {
                                v_val_1526_ = leanh::lean_ctor_get(v_val_1522_, 0);
                                leanh::lean_inc(v_val_1526_);
                                leanh::lean_dec_ref_known(v_val_1522_, 1);
                                v___y_1476_ = v_val_1526_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_1521_);
                            leanh::lean_dec_ref(v_e_1463_);
                            leanh::lean_dec_ref(v_lctx_1461_);
                            v___x_1527_ = leanh::lean_box(0);
                            v___x_1528_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1528_, 0, v___x_1527_);
                            leanh::lean_ctor_set(v___x_1528_, 1, v___y_1466_);
                            return v___x_1528_;
                        }
                    }
                }
            },
            1 => {
                v_maxIndex_1469_ = l_Lean_LocalDecl_index(v___y_1468_);
                leanh::lean_dec_ref(v___y_1468_);
                v___x_1470_ = lean_nat_dec_lt(v_maxIndex_1469_, v_minIndex_1460_);
                leanh::lean_dec(v_maxIndex_1469_);
                if v___x_1470_ == 0 {
                    leanh::lean_dec_ref(v_e_1463_);
                    v___x_1471_ = leanh::lean_box(0);
                    v___x_1472_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1472_, 0, v___x_1471_);
                    leanh::lean_ctor_set(v___x_1472_, 1, v___y_1466_);
                    return v___x_1472_;
                } else {
                    v___x_1473_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1473_, 0, v_e_1463_);
                    v___x_1474_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1474_, 0, v___x_1473_);
                    leanh::lean_ctor_set(v___x_1474_, 1, v___y_1466_);
                    return v___x_1474_;
                }
            }
            2 => {
                v___x_1477_ = lean_local_ctx_find(v_lctx_1461_, v___y_1476_);
                if leanh::lean_obj_tag(v___x_1477_) == 0 {
                    v___x_1478_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                    v___x_1479_ = l_panic___redArg(v___x_1462_, v___x_1478_);
                    v___y_1468_ = v___x_1479_;
                    state = 1;
                    continue;
                } else {
                    v_val_1480_ = leanh::lean_ctor_get(v___x_1477_, 0);
                    leanh::lean_inc(v_val_1480_);
                    leanh::lean_dec_ref_known(v___x_1477_, 1);
                    v___y_1468_ = v_val_1480_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1487_ = lean_nat_add(v_offset_1464_, v_val_1483_);
                leanh::lean_dec(v_val_1483_);
                v___x_2873__overap_1488_ =
                    l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v___x_1458_, v___x_1487_);
                v___x_1489_ = leanh::lean_box((v___y_1465_) as usize);
                v___x_1490_ =
                    leanh::lean_apply_2(v___x_2873__overap_1488_, v___x_1489_, v___y_1466_);
                v_fst_1491_ = leanh::lean_ctor_get(v___x_1490_, 0);
                v_snd_1492_ = leanh::lean_ctor_get(v___x_1490_, 1);
                v_isSharedCheck_1502_ = (!leanh::lean_is_exclusive(v___x_1490_)) as u8;
                if v_isSharedCheck_1502_ == 0 {
                    v___x_1494_ = v___x_1490_;
                    v_isShared_1495_ = v_isSharedCheck_1502_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1492_);
                    leanh::lean_inc(v_fst_1491_);
                    leanh::lean_dec(v___x_1490_);
                    v___x_1494_ = leanh::lean_box(0);
                    v_isShared_1495_ = v_isSharedCheck_1502_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1486_ == 0 {
                    leanh::lean_ctor_set(v___x_1485_, 0, v_fst_1491_);
                    v___x_1497_ = v___x_1485_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1501_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_fst_1491_);
                    v___x_1497_ = v_reuseFailAlloc_1501_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1495_ == 0 {
                    leanh::lean_ctor_set(v___x_1494_, 0, v___x_1497_);
                    v___x_1499_ = v___x_1494_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_snd_1492_);
                    v___x_1499_ = v_reuseFailAlloc_1500_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed(
    mut v_toDeBruijn_x3f_1529_: *mut leanh::LeanObject,
    mut v___x_1530_: *mut leanh::LeanObject,
    mut v_maxFVar_1531_: *mut leanh::LeanObject,
    mut v_minIndex_1532_: *mut leanh::LeanObject,
    mut v_lctx_1533_: *mut leanh::LeanObject,
    mut v___x_1534_: *mut leanh::LeanObject,
    mut v_e_1535_: *mut leanh::LeanObject,
    mut v_offset_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
    mut v___y_1538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2965__boxed_1539_: u8 = 0;
    let mut v_res_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_2965__boxed_1539_ = (leanh::lean_unbox(v___y_1537_) as u8);
    v_res_1540_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(
        v_toDeBruijn_x3f_1529_,
        v___x_1530_,
        v_maxFVar_1531_,
        v_minIndex_1532_,
        v_lctx_1533_,
        v___x_1534_,
        v_e_1535_,
        v_offset_1536_,
        v___y_2965__boxed_1539_,
        v___y_1538_,
    );
    leanh::lean_dec(v_offset_1536_);
    leanh::lean_dec_ref(v___x_1534_);
    leanh::lean_dec(v_minIndex_1532_);
    leanh::lean_dec_ref(v_maxFVar_1531_);
    return v_res_1540_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1541_ = leanh::lean_box(0);
    v___x_1542_ = leanh::lean_unsigned_to_nat(16);
    v___x_1543_ = lean_mk_array(v___x_1542_, v___x_1541_);
    return v___x_1543_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1544_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once
        ),
        _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0,
    );
    v___x_1545_ = leanh::lean_unsigned_to_nat(0);
    v___x_1546_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1546_, 0, v___x_1545_);
    leanh::lean_ctor_set(v___x_1546_, 1, v___x_1544_);
    return v___x_1546_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(
    mut v_e_1547_: *mut leanh::LeanObject,
    mut v_lctx_1548_: *mut leanh::LeanObject,
    mut v_maxFVar_1549_: *mut leanh::LeanObject,
    mut v_minFVarId_1550_: *mut leanh::LeanObject,
    mut v_toDeBruijn_x3f_1551_: *mut leanh::LeanObject,
    mut v_a_1552_: u8,
    mut v_a_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minIndex_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1566_: u8 = 0;
    let mut v_val_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut v_unused_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1580_: u8 = 0;
    let mut v_unused_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1585_: u8 = 0;
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1589_: u8 = 0;
    let mut v_unused_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1594_: u8 = 0;
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v_unused_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_unused_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut v_unused_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut v_unused_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1635_: u8 = 0;
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut v_unused_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1554_ = l_Lean_instInhabitedLocalDecl_default;
                v___x_1555_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
                leanh::lean_inc_ref(v_lctx_1548_);
                v___x_1641_ = lean_local_ctx_find(v_lctx_1548_, v_minFVarId_1550_);
                if leanh::lean_obj_tag(v___x_1641_) == 0 {
                    v___x_1642_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                    v___x_1643_ = l_panic___redArg(v___x_1554_, v___x_1642_);
                    v___y_1557_ = v___x_1643_;
                    state = 1;
                    continue;
                } else {
                    v_val_1644_ = leanh::lean_ctor_get(v___x_1641_, 0);
                    leanh::lean_inc(v_val_1644_);
                    leanh::lean_dec_ref_known(v___x_1641_, 1);
                    v___y_1557_ = v_val_1644_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_minIndex_1558_ = l_Lean_LocalDecl_index(v___y_1557_);
                leanh::lean_dec_ref(v___y_1557_);
                leanh::lean_inc_ref(v_lctx_1548_);
                leanh::lean_inc(v_minIndex_1558_);
                leanh::lean_inc_ref(v_maxFVar_1549_);
                leanh::lean_inc_ref(v_toDeBruijn_x3f_1551_);
                v___f_1559_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed as *mut core::ffi::c_void, 10, 6);
                leanh::lean_closure_set(v___f_1559_, 0, v_toDeBruijn_x3f_1551_);
                leanh::lean_closure_set(v___f_1559_, 1, v___x_1555_);
                leanh::lean_closure_set(v___f_1559_, 2, v_maxFVar_1549_);
                leanh::lean_closure_set(v___f_1559_, 3, v_minIndex_1558_);
                leanh::lean_closure_set(v___f_1559_, 4, v_lctx_1548_);
                leanh::lean_closure_set(v___f_1559_, 5, v___x_1554_);
                v___x_1560_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_e_1547_);
                v___x_1561_ =
                    l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0(
                        v_toDeBruijn_x3f_1551_,
                        v___x_1555_,
                        v_maxFVar_1549_,
                        v_minIndex_1558_,
                        v_lctx_1548_,
                        v___x_1554_,
                        v_e_1547_,
                        v___x_1560_,
                        v_a_1552_,
                        v_a_1553_,
                    );
                leanh::lean_dec(v_minIndex_1558_);
                leanh::lean_dec_ref(v_maxFVar_1549_);
                v_fst_1562_ = leanh::lean_ctor_get(v___x_1561_, 0);
                leanh::lean_inc(v_fst_1562_);
                if leanh::lean_obj_tag(v_fst_1562_) == 1 {
                    leanh::lean_dec_ref(v___f_1559_);
                    leanh::lean_dec_ref(v_e_1547_);
                    v_snd_1563_ = leanh::lean_ctor_get(v___x_1561_, 1);
                    v_isSharedCheck_1571_ = (!leanh::lean_is_exclusive(v___x_1561_)) as u8;
                    if v_isSharedCheck_1571_ == 0 {
                        v_unused_1572_ = leanh::lean_ctor_get(v___x_1561_, 0);
                        leanh::lean_dec(v_unused_1572_);
                        v___x_1565_ = v___x_1561_;
                        v_isShared_1566_ = v_isSharedCheck_1571_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1563_);
                        leanh::lean_dec(v___x_1561_);
                        v___x_1565_ = leanh::lean_box(0);
                        v_isShared_1566_ = v_isSharedCheck_1571_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_1562_);
                    match leanh::lean_obj_tag(v_e_1547_) {
                        9 => {
                            leanh::lean_dec_ref(v___f_1559_);
                            v_snd_1573_ = leanh::lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1580_ =
                                (!leanh::lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1580_ == 0 {
                                v_unused_1581_ = leanh::lean_ctor_get(v___x_1561_, 0);
                                leanh::lean_dec(v_unused_1581_);
                                v___x_1575_ = v___x_1561_;
                                v_isShared_1576_ = v_isSharedCheck_1580_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1573_);
                                leanh::lean_dec(v___x_1561_);
                                v___x_1575_ = leanh::lean_box(0);
                                v_isShared_1576_ = v_isSharedCheck_1580_;
                                state = 4;
                                continue;
                            }
                        }
                        2 => {
                            leanh::lean_dec_ref(v___f_1559_);
                            v_snd_1582_ = leanh::lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1589_ =
                                (!leanh::lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1589_ == 0 {
                                v_unused_1590_ = leanh::lean_ctor_get(v___x_1561_, 0);
                                leanh::lean_dec(v_unused_1590_);
                                v___x_1584_ = v___x_1561_;
                                v_isShared_1585_ = v_isSharedCheck_1589_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1582_);
                                leanh::lean_dec(v___x_1561_);
                                v___x_1584_ = leanh::lean_box(0);
                                v_isShared_1585_ = v_isSharedCheck_1589_;
                                state = 6;
                                continue;
                            }
                        }
                        0 => {
                            leanh::lean_dec_ref(v___f_1559_);
                            v_snd_1591_ = leanh::lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1598_ =
                                (!leanh::lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1598_ == 0 {
                                v_unused_1599_ = leanh::lean_ctor_get(v___x_1561_, 0);
                                leanh::lean_dec(v_unused_1599_);
                                v___x_1593_ = v___x_1561_;
                                v_isShared_1594_ = v_isSharedCheck_1598_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1591_);
                                leanh::lean_dec(v___x_1561_);
                                v___x_1593_ = leanh::lean_box(0);
                                v_isShared_1594_ = v_isSharedCheck_1598_;
                                state = 8;
                                continue;
                            }
                        }
                        1 => {
                            leanh::lean_dec_ref(v___f_1559_);
                            v_snd_1600_ = leanh::lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1607_ =
                                (!leanh::lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1607_ == 0 {
                                v_unused_1608_ = leanh::lean_ctor_get(v___x_1561_, 0);
                                leanh::lean_dec(v_unused_1608_);
                                v___x_1602_ = v___x_1561_;
                                v_isShared_1603_ = v_isSharedCheck_1607_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1600_);
                                leanh::lean_dec(v___x_1561_);
                                v___x_1602_ = leanh::lean_box(0);
                                v_isShared_1603_ = v_isSharedCheck_1607_;
                                state = 10;
                                continue;
                            }
                        }
                        4 => {
                            leanh::lean_dec_ref(v___f_1559_);
                            v_snd_1609_ = leanh::lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1616_ =
                                (!leanh::lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1616_ == 0 {
                                v_unused_1617_ = leanh::lean_ctor_get(v___x_1561_, 0);
                                leanh::lean_dec(v_unused_1617_);
                                v___x_1611_ = v___x_1561_;
                                v_isShared_1612_ = v_isSharedCheck_1616_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1609_);
                                leanh::lean_dec(v___x_1561_);
                                v___x_1611_ = leanh::lean_box(0);
                                v_isShared_1612_ = v_isSharedCheck_1616_;
                                state = 12;
                                continue;
                            }
                        }
                        3 => {
                            leanh::lean_dec_ref(v___f_1559_);
                            v_snd_1618_ = leanh::lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1625_ =
                                (!leanh::lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1625_ == 0 {
                                v_unused_1626_ = leanh::lean_ctor_get(v___x_1561_, 0);
                                leanh::lean_dec(v_unused_1626_);
                                v___x_1620_ = v___x_1561_;
                                v_isShared_1621_ = v_isSharedCheck_1625_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_1618_);
                                leanh::lean_dec(v___x_1561_);
                                v___x_1620_ = leanh::lean_box(0);
                                v_isShared_1621_ = v_isSharedCheck_1625_;
                                state = 14;
                                continue;
                            }
                        }
                        _ => {
                            v_snd_1627_ = leanh::lean_ctor_get(v___x_1561_, 1);
                            leanh::lean_inc(v_snd_1627_);
                            leanh::lean_dec_ref(v___x_1561_);
                            v___x_1628_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1);
                            v___x_1629_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(
                                v_e_1547_,
                                v___x_1560_,
                                v___f_1559_,
                                v___x_1628_,
                                v_a_1552_,
                                v_snd_1627_,
                            );
                            v_fst_1630_ = leanh::lean_ctor_get(v___x_1629_, 0);
                            leanh::lean_inc(v_fst_1630_);
                            v_snd_1631_ = leanh::lean_ctor_get(v___x_1629_, 1);
                            leanh::lean_inc(v_snd_1631_);
                            leanh::lean_dec_ref(v___x_1629_);
                            v_fst_1632_ = leanh::lean_ctor_get(v_fst_1630_, 0);
                            v_isSharedCheck_1639_ =
                                (!leanh::lean_is_exclusive(v_fst_1630_)) as u8;
                            if v_isSharedCheck_1639_ == 0 {
                                v_unused_1640_ = leanh::lean_ctor_get(v_fst_1630_, 1);
                                leanh::lean_dec(v_unused_1640_);
                                v___x_1634_ = v_fst_1630_;
                                v_isShared_1635_ = v_isSharedCheck_1639_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_fst_1632_);
                                leanh::lean_dec(v_fst_1630_);
                                v___x_1634_ = leanh::lean_box(0);
                                v_isShared_1635_ = v_isSharedCheck_1639_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v_val_1567_ = leanh::lean_ctor_get(v_fst_1562_, 0);
                leanh::lean_inc(v_val_1567_);
                leanh::lean_dec_ref_known(v_fst_1562_, 1);
                if v_isShared_1566_ == 0 {
                    leanh::lean_ctor_set(v___x_1565_, 0, v_val_1567_);
                    v___x_1569_ = v___x_1565_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_val_1567_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_snd_1563_);
                    v___x_1569_ = v_reuseFailAlloc_1570_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1569_;
            }
            4 => {
                if v_isShared_1576_ == 0 {
                    leanh::lean_ctor_set(v___x_1575_, 0, v_e_1547_);
                    v___x_1578_ = v___x_1575_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1579_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_e_1547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_snd_1573_);
                    v___x_1578_ = v_reuseFailAlloc_1579_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1578_;
            }
            6 => {
                if v_isShared_1585_ == 0 {
                    leanh::lean_ctor_set(v___x_1584_, 0, v_e_1547_);
                    v___x_1587_ = v___x_1584_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1588_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_e_1547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_snd_1582_);
                    v___x_1587_ = v_reuseFailAlloc_1588_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1587_;
            }
            8 => {
                if v_isShared_1594_ == 0 {
                    leanh::lean_ctor_set(v___x_1593_, 0, v_e_1547_);
                    v___x_1596_ = v___x_1593_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1597_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_e_1547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_snd_1591_);
                    v___x_1596_ = v_reuseFailAlloc_1597_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1596_;
            }
            10 => {
                if v_isShared_1603_ == 0 {
                    leanh::lean_ctor_set(v___x_1602_, 0, v_e_1547_);
                    v___x_1605_ = v___x_1602_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_e_1547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_snd_1600_);
                    v___x_1605_ = v_reuseFailAlloc_1606_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1605_;
            }
            12 => {
                if v_isShared_1612_ == 0 {
                    leanh::lean_ctor_set(v___x_1611_, 0, v_e_1547_);
                    v___x_1614_ = v___x_1611_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1615_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_e_1547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_snd_1609_);
                    v___x_1614_ = v_reuseFailAlloc_1615_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1614_;
            }
            14 => {
                if v_isShared_1621_ == 0 {
                    leanh::lean_ctor_set(v___x_1620_, 0, v_e_1547_);
                    v___x_1623_ = v___x_1620_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_e_1547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_snd_1618_);
                    v___x_1623_ = v_reuseFailAlloc_1624_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1623_;
            }
            16 => {
                if v_isShared_1635_ == 0 {
                    leanh::lean_ctor_set(v___x_1634_, 1, v_snd_1631_);
                    v___x_1637_ = v___x_1634_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1638_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_fst_1632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_snd_1631_);
                    v___x_1637_ = v_reuseFailAlloc_1638_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___boxed(
    mut v_e_1645_: *mut leanh::LeanObject,
    mut v_lctx_1646_: *mut leanh::LeanObject,
    mut v_maxFVar_1647_: *mut leanh::LeanObject,
    mut v_minFVarId_1648_: *mut leanh::LeanObject,
    mut v_toDeBruijn_x3f_1649_: *mut leanh::LeanObject,
    mut v_a_1650_: *mut leanh::LeanObject,
    mut v_a_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_1652_: u8 = 0;
    let mut v_res_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_1652_ = (leanh::lean_unbox(v_a_1650_) as u8);
    v_res_1653_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(
        v_e_1645_,
        v_lctx_1646_,
        v_maxFVar_1647_,
        v_minFVarId_1648_,
        v_toDeBruijn_x3f_1649_,
        v_a_boxed_1652_,
        v_a_1651_,
    );
    return v_res_1653_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(
    mut v_start_1654_: *mut leanh::LeanObject,
    mut v_xs_1655_: *mut leanh::LeanObject,
    mut v_fvarId_1656_: *mut leanh::LeanObject,
    mut v_bidx_1657_: *mut leanh::LeanObject,
    mut v_i_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1659_ = lean_array_fget_borrowed(v_xs_1655_, v_i_1658_);
                v___x_1660_ = l_Lean_Expr_fvarId_x21(v___x_1659_);
                v___x_1661_ = l_Lean_instBEqFVarId_beq(v___x_1660_, v_fvarId_1656_);
                leanh::lean_dec(v___x_1660_);
                if v___x_1661_ == 0 {
                    v___x_1662_ = lean_nat_dec_lt(v_start_1654_, v_i_1658_);
                    if v___x_1662_ == 0 {
                        leanh::lean_dec(v_i_1658_);
                        leanh::lean_dec(v_bidx_1657_);
                        v___x_1663_ = leanh::lean_box(0);
                        return v___x_1663_;
                    } else {
                        v___x_1664_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1665_ = lean_nat_add(v_bidx_1657_, v___x_1664_);
                        leanh::lean_dec(v_bidx_1657_);
                        v___x_1666_ = lean_nat_sub(v_i_1658_, v___x_1664_);
                        leanh::lean_dec(v_i_1658_);
                        v_bidx_1657_ = v___x_1665_;
                        v_i_1658_ = v___x_1666_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_i_1658_);
                    v___x_1668_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1668_, 0, v_bidx_1657_);
                    return v___x_1668_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg___boxed(
    mut v_start_1669_: *mut leanh::LeanObject,
    mut v_xs_1670_: *mut leanh::LeanObject,
    mut v_fvarId_1671_: *mut leanh::LeanObject,
    mut v_bidx_1672_: *mut leanh::LeanObject,
    mut v_i_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1674_ =
        l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(
            v_start_1669_,
            v_xs_1670_,
            v_fvarId_1671_,
            v_bidx_1672_,
            v_i_1673_,
        );
    leanh::lean_dec(v_fvarId_1671_);
    leanh::lean_dec_ref(v_xs_1670_);
    leanh::lean_dec(v_start_1669_);
    return v_res_1674_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(
    mut v_start_1675_: *mut leanh::LeanObject,
    mut v_xs_1676_: *mut leanh::LeanObject,
    mut v_fvarId_1677_: *mut leanh::LeanObject,
    mut v_bidx_1678_: *mut leanh::LeanObject,
    mut v_i_1679_: *mut leanh::LeanObject,
    mut v_h_1680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1681_ =
        l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(
            v_start_1675_,
            v_xs_1676_,
            v_fvarId_1677_,
            v_bidx_1678_,
            v_i_1679_,
        );
    return v___x_1681_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___boxed(
    mut v_start_1682_: *mut leanh::LeanObject,
    mut v_xs_1683_: *mut leanh::LeanObject,
    mut v_fvarId_1684_: *mut leanh::LeanObject,
    mut v_bidx_1685_: *mut leanh::LeanObject,
    mut v_i_1686_: *mut leanh::LeanObject,
    mut v_h_1687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1688_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(
        v_start_1682_,
        v_xs_1683_,
        v_fvarId_1684_,
        v_bidx_1685_,
        v_i_1686_,
        v_h_1687_,
    );
    leanh::lean_dec(v_fvarId_1684_);
    leanh::lean_dec_ref(v_xs_1683_);
    leanh::lean_dec(v_start_1682_);
    return v_res_1688_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1689_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1689_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0);
    v___x_1691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1691_, 0, v___x_1690_);
    return v___x_1691_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(
    mut v_00_u03b2_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1693_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1);
    return v___x_1693_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(
    mut v_msg_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1695_ = l_Lean_instInhabitedLocalDecl_default;
    v___x_1696_ = lean_panic_fn_borrowed(v___x_1695_, v_msg_1694_);
    return v___x_1696_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(
    mut v_idx_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1699_ = l_Lean_Expr_bvar___override(v_idx_1697_);
    v___x_1700_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1699_, v___y_1698_);
    return v___x_1700_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(
    mut v_idx_1701_: *mut leanh::LeanObject,
    mut v___y_1702_: u8,
    mut v___y_1703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1704_ =
        l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(
            v_idx_1701_,
            v___y_1703_,
        );
    return v___x_1704_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(
    mut v_idx_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_25263__boxed_1708_: u8 = 0;
    let mut v_res_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_25263__boxed_1708_ = (leanh::lean_unbox(v___y_1706_) as u8);
    v_res_1709_ =
        l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(
            v_idx_1705_,
            v___y_25263__boxed_1708_,
            v___y_1707_,
        );
    return v_res_1709_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(
    mut v_msg_1710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1711_ = leanh::lean_box(0);
    v___x_1712_ = lean_panic_fn_borrowed(v___x_1711_, v_msg_1710_);
    return v___x_1712_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(
    mut v_structName_1713_: *mut leanh::LeanObject,
    mut v_idx_1714_: *mut leanh::LeanObject,
    mut v_struct_1715_: *mut leanh::LeanObject,
    mut v___y_1716_: *mut leanh::LeanObject,
    mut v___y_1717_: u8,
    mut v___y_1718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1728_: u8 = 0;
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1733_: u8 = 0;
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1717_ == 0 {
                    v___y_1720_ = v___y_1716_;
                    v___y_1721_ = v___y_1718_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_struct_1715_);
                    v___x_1734_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_struct_1715_,
                        v___y_1717_,
                        v___y_1718_,
                    );
                    v_snd_1735_ = leanh::lean_ctor_get(v___x_1734_, 1);
                    leanh::lean_inc(v_snd_1735_);
                    leanh::lean_dec_ref(v___x_1734_);
                    v___y_1720_ = v___y_1716_;
                    v___y_1721_ = v_snd_1735_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1722_ =
                    l_Lean_Expr_proj___override(v_structName_1713_, v_idx_1714_, v_struct_1715_);
                v___x_1723_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1722_, v___y_1721_);
                v_fst_1724_ = leanh::lean_ctor_get(v___x_1723_, 0);
                v_snd_1725_ = leanh::lean_ctor_get(v___x_1723_, 1);
                v_isSharedCheck_1733_ = (!leanh::lean_is_exclusive(v___x_1723_)) as u8;
                if v_isSharedCheck_1733_ == 0 {
                    v___x_1727_ = v___x_1723_;
                    v_isShared_1728_ = v_isSharedCheck_1733_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1725_);
                    leanh::lean_inc(v_fst_1724_);
                    leanh::lean_dec(v___x_1723_);
                    v___x_1727_ = leanh::lean_box(0);
                    v_isShared_1728_ = v_isSharedCheck_1733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1728_ == 0 {
                    leanh::lean_ctor_set(v___x_1727_, 1, v___y_1720_);
                    v___x_1730_ = v___x_1727_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1732_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_fst_1724_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___y_1720_);
                    v___x_1730_ = v_reuseFailAlloc_1732_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1731_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1731_, 0, v___x_1730_);
                leanh::lean_ctor_set(v___x_1731_, 1, v_snd_1725_);
                return v___x_1731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12___boxed(
    mut v_structName_1736_: *mut leanh::LeanObject,
    mut v_idx_1737_: *mut leanh::LeanObject,
    mut v_struct_1738_: *mut leanh::LeanObject,
    mut v___y_1739_: *mut leanh::LeanObject,
    mut v___y_1740_: *mut leanh::LeanObject,
    mut v___y_1741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_25276__boxed_1742_: u8 = 0;
    let mut v_res_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_25276__boxed_1742_ = (leanh::lean_unbox(v___y_1740_) as u8);
    v_res_1743_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(v_structName_1736_, v_idx_1737_, v_struct_1738_, v___y_1739_, v___y_25276__boxed_1742_, v___y_1741_);
    return v_res_1743_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(
    mut v_d_1744_: *mut leanh::LeanObject,
    mut v_e_1745_: *mut leanh::LeanObject,
    mut v___y_1746_: *mut leanh::LeanObject,
    mut v___y_1747_: u8,
    mut v___y_1748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1747_ == 0 {
                    v___y_1750_ = v___y_1746_;
                    v___y_1751_ = v___y_1748_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_e_1745_);
                    v___x_1764_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_e_1745_,
                        v___y_1747_,
                        v___y_1748_,
                    );
                    v_snd_1765_ = leanh::lean_ctor_get(v___x_1764_, 1);
                    leanh::lean_inc(v_snd_1765_);
                    leanh::lean_dec_ref(v___x_1764_);
                    v___y_1750_ = v___y_1746_;
                    v___y_1751_ = v_snd_1765_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1752_ = l_Lean_Expr_mdata___override(v_d_1744_, v_e_1745_);
                v___x_1753_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1752_, v___y_1751_);
                v_fst_1754_ = leanh::lean_ctor_get(v___x_1753_, 0);
                v_snd_1755_ = leanh::lean_ctor_get(v___x_1753_, 1);
                v_isSharedCheck_1763_ = (!leanh::lean_is_exclusive(v___x_1753_)) as u8;
                if v_isSharedCheck_1763_ == 0 {
                    v___x_1757_ = v___x_1753_;
                    v_isShared_1758_ = v_isSharedCheck_1763_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1755_);
                    leanh::lean_inc(v_fst_1754_);
                    leanh::lean_dec(v___x_1753_);
                    v___x_1757_ = leanh::lean_box(0);
                    v_isShared_1758_ = v_isSharedCheck_1763_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1758_ == 0 {
                    leanh::lean_ctor_set(v___x_1757_, 1, v___y_1750_);
                    v___x_1760_ = v___x_1757_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1762_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_fst_1754_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___y_1750_);
                    v___x_1760_ = v_reuseFailAlloc_1762_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1761_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1761_, 0, v___x_1760_);
                leanh::lean_ctor_set(v___x_1761_, 1, v_snd_1755_);
                return v___x_1761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11___boxed(
    mut v_d_1766_: *mut leanh::LeanObject,
    mut v_e_1767_: *mut leanh::LeanObject,
    mut v___y_1768_: *mut leanh::LeanObject,
    mut v___y_1769_: *mut leanh::LeanObject,
    mut v___y_1770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_25320__boxed_1771_: u8 = 0;
    let mut v_res_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_25320__boxed_1771_ = (leanh::lean_unbox(v___y_1769_) as u8);
    v_res_1772_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(v_d_1766_, v_e_1767_, v___y_1768_, v___y_25320__boxed_1771_, v___y_1770_);
    return v_res_1772_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(
    mut v_x_1773_: *mut leanh::LeanObject,
    mut v_bi_1774_: u8,
    mut v_t_1775_: *mut leanh::LeanObject,
    mut v_b_1776_: *mut leanh::LeanObject,
    mut v___y_1777_: *mut leanh::LeanObject,
    mut v___y_1778_: u8,
    mut v___y_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1794_: u8 = 0;
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1778_ == 0 {
                    v___y_1781_ = v___y_1777_;
                    v___y_1782_ = v___y_1779_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_t_1775_);
                    v___x_1795_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1775_,
                        v___y_1778_,
                        v___y_1779_,
                    );
                    v_snd_1796_ = leanh::lean_ctor_get(v___x_1795_, 1);
                    leanh::lean_inc(v_snd_1796_);
                    leanh::lean_dec_ref(v___x_1795_);
                    leanh::lean_inc_ref(v_b_1776_);
                    v___x_1797_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1776_,
                        v___y_1778_,
                        v_snd_1796_,
                    );
                    v_snd_1798_ = leanh::lean_ctor_get(v___x_1797_, 1);
                    leanh::lean_inc(v_snd_1798_);
                    leanh::lean_dec_ref(v___x_1797_);
                    v___y_1781_ = v___y_1777_;
                    v___y_1782_ = v_snd_1798_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1783_ =
                    l_Lean_Expr_forallE___override(v_x_1773_, v_t_1775_, v_b_1776_, v_bi_1774_);
                v___x_1784_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1783_, v___y_1782_);
                v_fst_1785_ = leanh::lean_ctor_get(v___x_1784_, 0);
                v_snd_1786_ = leanh::lean_ctor_get(v___x_1784_, 1);
                v_isSharedCheck_1794_ = (!leanh::lean_is_exclusive(v___x_1784_)) as u8;
                if v_isSharedCheck_1794_ == 0 {
                    v___x_1788_ = v___x_1784_;
                    v_isShared_1789_ = v_isSharedCheck_1794_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1786_);
                    leanh::lean_inc(v_fst_1785_);
                    leanh::lean_dec(v___x_1784_);
                    v___x_1788_ = leanh::lean_box(0);
                    v_isShared_1789_ = v_isSharedCheck_1794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1789_ == 0 {
                    leanh::lean_ctor_set(v___x_1788_, 1, v___y_1781_);
                    v___x_1791_ = v___x_1788_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_fst_1785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___y_1781_);
                    v___x_1791_ = v_reuseFailAlloc_1793_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1792_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1792_, 0, v___x_1791_);
                leanh::lean_ctor_set(v___x_1792_, 1, v_snd_1786_);
                return v___x_1792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9___boxed(
    mut v_x_1799_: *mut leanh::LeanObject,
    mut v_bi_1800_: *mut leanh::LeanObject,
    mut v_t_1801_: *mut leanh::LeanObject,
    mut v_b_1802_: *mut leanh::LeanObject,
    mut v___y_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
    mut v___y_1805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_1806_: u8 = 0;
    let mut v___y_25364__boxed_1807_: u8 = 0;
    let mut v_res_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1806_ = (leanh::lean_unbox(v_bi_1800_) as u8);
    v___y_25364__boxed_1807_ = (leanh::lean_unbox(v___y_1804_) as u8);
    v_res_1808_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(v_x_1799_, v_bi_boxed_1806_, v_t_1801_, v_b_1802_, v___y_1803_, v___y_25364__boxed_1807_, v___y_1805_);
    return v_res_1808_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(
    mut v_x_1809_: *mut leanh::LeanObject,
    mut v_bi_1810_: u8,
    mut v_t_1811_: *mut leanh::LeanObject,
    mut v_b_1812_: *mut leanh::LeanObject,
    mut v___y_1813_: *mut leanh::LeanObject,
    mut v___y_1814_: u8,
    mut v___y_1815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1825_: u8 = 0;
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1814_ == 0 {
                    v___y_1817_ = v___y_1813_;
                    v___y_1818_ = v___y_1815_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_t_1811_);
                    v___x_1831_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1811_,
                        v___y_1814_,
                        v___y_1815_,
                    );
                    v_snd_1832_ = leanh::lean_ctor_get(v___x_1831_, 1);
                    leanh::lean_inc(v_snd_1832_);
                    leanh::lean_dec_ref(v___x_1831_);
                    leanh::lean_inc_ref(v_b_1812_);
                    v___x_1833_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1812_,
                        v___y_1814_,
                        v_snd_1832_,
                    );
                    v_snd_1834_ = leanh::lean_ctor_get(v___x_1833_, 1);
                    leanh::lean_inc(v_snd_1834_);
                    leanh::lean_dec_ref(v___x_1833_);
                    v___y_1817_ = v___y_1813_;
                    v___y_1818_ = v_snd_1834_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1819_ =
                    l_Lean_Expr_lam___override(v_x_1809_, v_t_1811_, v_b_1812_, v_bi_1810_);
                v___x_1820_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1819_, v___y_1818_);
                v_fst_1821_ = leanh::lean_ctor_get(v___x_1820_, 0);
                v_snd_1822_ = leanh::lean_ctor_get(v___x_1820_, 1);
                v_isSharedCheck_1830_ = (!leanh::lean_is_exclusive(v___x_1820_)) as u8;
                if v_isSharedCheck_1830_ == 0 {
                    v___x_1824_ = v___x_1820_;
                    v_isShared_1825_ = v_isSharedCheck_1830_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1822_);
                    leanh::lean_inc(v_fst_1821_);
                    leanh::lean_dec(v___x_1820_);
                    v___x_1824_ = leanh::lean_box(0);
                    v_isShared_1825_ = v_isSharedCheck_1830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1825_ == 0 {
                    leanh::lean_ctor_set(v___x_1824_, 1, v___y_1817_);
                    v___x_1827_ = v___x_1824_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1829_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_fst_1821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___y_1817_);
                    v___x_1827_ = v_reuseFailAlloc_1829_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1828_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1828_, 0, v___x_1827_);
                leanh::lean_ctor_set(v___x_1828_, 1, v_snd_1822_);
                return v___x_1828_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8___boxed(
    mut v_x_1835_: *mut leanh::LeanObject,
    mut v_bi_1836_: *mut leanh::LeanObject,
    mut v_t_1837_: *mut leanh::LeanObject,
    mut v_b_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_1842_: u8 = 0;
    let mut v___y_25413__boxed_1843_: u8 = 0;
    let mut v_res_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_1842_ = (leanh::lean_unbox(v_bi_1836_) as u8);
    v___y_25413__boxed_1843_ = (leanh::lean_unbox(v___y_1840_) as u8);
    v_res_1844_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(v_x_1835_, v_bi_boxed_1842_, v_t_1837_, v_b_1838_, v___y_1839_, v___y_25413__boxed_1843_, v___y_1841_);
    return v_res_1844_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(
    mut v_x_1845_: *mut leanh::LeanObject,
    mut v_t_1846_: *mut leanh::LeanObject,
    mut v_v_1847_: *mut leanh::LeanObject,
    mut v_b_1848_: *mut leanh::LeanObject,
    mut v_nondep_1849_: u8,
    mut v___y_1850_: *mut leanh::LeanObject,
    mut v___y_1851_: u8,
    mut v___y_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1867_: u8 = 0;
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1851_ == 0 {
                    v___y_1854_ = v___y_1850_;
                    v___y_1855_ = v___y_1852_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_t_1846_);
                    v___x_1868_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1846_,
                        v___y_1851_,
                        v___y_1852_,
                    );
                    v_snd_1869_ = leanh::lean_ctor_get(v___x_1868_, 1);
                    leanh::lean_inc(v_snd_1869_);
                    leanh::lean_dec_ref(v___x_1868_);
                    leanh::lean_inc_ref(v_v_1847_);
                    v___x_1870_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_v_1847_,
                        v___y_1851_,
                        v_snd_1869_,
                    );
                    v_snd_1871_ = leanh::lean_ctor_get(v___x_1870_, 1);
                    leanh::lean_inc(v_snd_1871_);
                    leanh::lean_dec_ref(v___x_1870_);
                    leanh::lean_inc_ref(v_b_1848_);
                    v___x_1872_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1848_,
                        v___y_1851_,
                        v_snd_1871_,
                    );
                    v_snd_1873_ = leanh::lean_ctor_get(v___x_1872_, 1);
                    leanh::lean_inc(v_snd_1873_);
                    leanh::lean_dec_ref(v___x_1872_);
                    v___y_1854_ = v___y_1850_;
                    v___y_1855_ = v_snd_1873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1856_ = l_Lean_Expr_letE___override(
                    v_x_1845_,
                    v_t_1846_,
                    v_v_1847_,
                    v_b_1848_,
                    v_nondep_1849_,
                );
                v___x_1857_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1856_, v___y_1855_);
                v_fst_1858_ = leanh::lean_ctor_get(v___x_1857_, 0);
                v_snd_1859_ = leanh::lean_ctor_get(v___x_1857_, 1);
                v_isSharedCheck_1867_ = (!leanh::lean_is_exclusive(v___x_1857_)) as u8;
                if v_isSharedCheck_1867_ == 0 {
                    v___x_1861_ = v___x_1857_;
                    v_isShared_1862_ = v_isSharedCheck_1867_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1859_);
                    leanh::lean_inc(v_fst_1858_);
                    leanh::lean_dec(v___x_1857_);
                    v___x_1861_ = leanh::lean_box(0);
                    v_isShared_1862_ = v_isSharedCheck_1867_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1862_ == 0 {
                    leanh::lean_ctor_set(v___x_1861_, 1, v___y_1854_);
                    v___x_1864_ = v___x_1861_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1866_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_fst_1858_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 1, v___y_1854_);
                    v___x_1864_ = v_reuseFailAlloc_1866_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1865_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1865_, 0, v___x_1864_);
                leanh::lean_ctor_set(v___x_1865_, 1, v_snd_1859_);
                return v___x_1865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10___boxed(
    mut v_x_1874_: *mut leanh::LeanObject,
    mut v_t_1875_: *mut leanh::LeanObject,
    mut v_v_1876_: *mut leanh::LeanObject,
    mut v_b_1877_: *mut leanh::LeanObject,
    mut v_nondep_1878_: *mut leanh::LeanObject,
    mut v___y_1879_: *mut leanh::LeanObject,
    mut v___y_1880_: *mut leanh::LeanObject,
    mut v___y_1881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_1882_: u8 = 0;
    let mut v___y_25462__boxed_1883_: u8 = 0;
    let mut v_res_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_1882_ = (leanh::lean_unbox(v_nondep_1878_) as u8);
    v___y_25462__boxed_1883_ = (leanh::lean_unbox(v___y_1880_) as u8);
    v_res_1884_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_x_1874_, v_t_1875_, v_v_1876_, v_b_1877_, v_nondep_boxed_1882_, v___y_1879_, v___y_25462__boxed_1883_, v___y_1881_);
    return v_res_1884_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(
    mut v_f_1885_: *mut leanh::LeanObject,
    mut v_a_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: u8,
    mut v___y_1889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1899_: u8 = 0;
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_1888_ == 0 {
                    v___y_1891_ = v___y_1887_;
                    v___y_1892_ = v___y_1889_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_f_1885_);
                    v___x_1905_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_f_1885_,
                        v___y_1888_,
                        v___y_1889_,
                    );
                    v_snd_1906_ = leanh::lean_ctor_get(v___x_1905_, 1);
                    leanh::lean_inc(v_snd_1906_);
                    leanh::lean_dec_ref(v___x_1905_);
                    leanh::lean_inc_ref(v_a_1886_);
                    v___x_1907_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_a_1886_,
                        v___y_1888_,
                        v_snd_1906_,
                    );
                    v_snd_1908_ = leanh::lean_ctor_get(v___x_1907_, 1);
                    leanh::lean_inc(v_snd_1908_);
                    leanh::lean_dec_ref(v___x_1907_);
                    v___y_1891_ = v___y_1887_;
                    v___y_1892_ = v_snd_1908_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1893_ = l_Lean_Expr_app___override(v_f_1885_, v_a_1886_);
                v___x_1894_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1893_, v___y_1892_);
                v_fst_1895_ = leanh::lean_ctor_get(v___x_1894_, 0);
                v_snd_1896_ = leanh::lean_ctor_get(v___x_1894_, 1);
                v_isSharedCheck_1904_ = (!leanh::lean_is_exclusive(v___x_1894_)) as u8;
                if v_isSharedCheck_1904_ == 0 {
                    v___x_1898_ = v___x_1894_;
                    v_isShared_1899_ = v_isSharedCheck_1904_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1896_);
                    leanh::lean_inc(v_fst_1895_);
                    leanh::lean_dec(v___x_1894_);
                    v___x_1898_ = leanh::lean_box(0);
                    v_isShared_1899_ = v_isSharedCheck_1904_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1899_ == 0 {
                    leanh::lean_ctor_set(v___x_1898_, 1, v___y_1891_);
                    v___x_1901_ = v___x_1898_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1903_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_fst_1895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1903_, 1, v___y_1891_);
                    v___x_1901_ = v_reuseFailAlloc_1903_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1902_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1902_, 0, v___x_1901_);
                leanh::lean_ctor_set(v___x_1902_, 1, v_snd_1896_);
                return v___x_1902_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7___boxed(
    mut v_f_1909_: *mut leanh::LeanObject,
    mut v_a_1910_: *mut leanh::LeanObject,
    mut v___y_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
    mut v___y_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_25516__boxed_1914_: u8 = 0;
    let mut v_res_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_25516__boxed_1914_ = (leanh::lean_unbox(v___y_1912_) as u8);
    v_res_1915_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(v_f_1909_, v_a_1910_, v___y_1911_, v___y_25516__boxed_1914_, v___y_1913_);
    return v_res_1915_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(
    mut v_a_1916_: *mut leanh::LeanObject,
    mut v_x_1917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: u8 = 0;
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u8 = 0;
    let mut v___x_1931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1917_) == 0 {
                    v___x_1918_ = leanh::lean_box(0);
                    return v___x_1918_;
                } else {
                    v_key_1919_ = leanh::lean_ctor_get(v_x_1917_, 0);
                    v_value_1920_ = leanh::lean_ctor_get(v_x_1917_, 1);
                    v_tail_1921_ = leanh::lean_ctor_get(v_x_1917_, 2);
                    v_fst_1926_ = leanh::lean_ctor_get(v_key_1919_, 0);
                    v_snd_1927_ = leanh::lean_ctor_get(v_key_1919_, 1);
                    v_fst_1928_ = leanh::lean_ctor_get(v_a_1916_, 0);
                    v_snd_1929_ = leanh::lean_ctor_get(v_a_1916_, 1);
                    v___x_1930_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_1926_,
                            v_fst_1928_,
                        );
                    if v___x_1930_ == 0 {
                        v___y_1923_ = v___x_1930_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1931_ = lean_nat_dec_eq(v_snd_1927_, v_snd_1929_);
                        v___y_1923_ = v___x_1931_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1923_ == 0 {
                    v_x_1917_ = v_tail_1921_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc(v_value_1920_);
                    v___x_1925_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1925_, 0, v_value_1920_);
                    return v___x_1925_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg___boxed(
    mut v_a_1932_: *mut leanh::LeanObject,
    mut v_x_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(v_a_1932_, v_x_1933_);
    leanh::lean_dec(v_x_1933_);
    leanh::lean_dec_ref(v_a_1932_);
    return v_res_1934_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(
    mut v_m_1935_: *mut leanh::LeanObject,
    mut v_a_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u64 = 0;
    let mut v___x_1942_: u64 = 0;
    let mut v___x_1943_: u64 = 0;
    let mut v___x_1944_: u64 = 0;
    let mut v___x_1945_: u64 = 0;
    let mut v_fold_1946_: u64 = 0;
    let mut v___x_1947_: u64 = 0;
    let mut v___x_1948_: u64 = 0;
    let mut v___x_1949_: u64 = 0;
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: usize = 0;
    let mut v___x_1952_: usize = 0;
    let mut v___x_1953_: usize = 0;
    let mut v___x_1954_: usize = 0;
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1937_ = leanh::lean_ctor_get(v_m_1935_, 1);
    v_fst_1938_ = leanh::lean_ctor_get(v_a_1936_, 0);
    v_snd_1939_ = leanh::lean_ctor_get(v_a_1936_, 1);
    v___x_1940_ = lean_array_get_size(v_buckets_1937_);
    v___x_1941_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_1938_);
    v___x_1942_ = lean_uint64_of_nat(v_snd_1939_);
    v___x_1943_ = lean_uint64_mix_hash(v___x_1941_, v___x_1942_);
    v___x_1944_ = 32u64;
    v___x_1945_ = lean_uint64_shift_right(v___x_1943_, v___x_1944_);
    v_fold_1946_ = lean_uint64_xor(v___x_1943_, v___x_1945_);
    v___x_1947_ = 16u64;
    v___x_1948_ = lean_uint64_shift_right(v_fold_1946_, v___x_1947_);
    v___x_1949_ = lean_uint64_xor(v_fold_1946_, v___x_1948_);
    v___x_1950_ = lean_uint64_to_usize(v___x_1949_);
    v___x_1951_ = lean_usize_of_nat(v___x_1940_);
    v___x_1952_ = 1usize;
    v___x_1953_ = lean_usize_sub(v___x_1951_, v___x_1952_);
    v___x_1954_ = lean_usize_land(v___x_1950_, v___x_1953_);
    v___x_1955_ = lean_array_uget_borrowed(v_buckets_1937_, v___x_1954_);
    v___x_1956_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(v_a_1936_, v___x_1955_);
    return v___x_1956_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg___boxed(
    mut v_m_1957_: *mut leanh::LeanObject,
    mut v_a_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1959_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_m_1957_, v_a_1958_);
    leanh::lean_dec_ref(v_a_1958_);
    leanh::lean_dec_ref(v_m_1957_);
    return v_res_1959_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(
    mut v_keys_1960_: *mut leanh::LeanObject,
    mut v_vals_1961_: *mut leanh::LeanObject,
    mut v_i_1962_: *mut leanh::LeanObject,
    mut v_k_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1964_ = lean_array_get_size(v_keys_1960_);
                v___x_1965_ = lean_nat_dec_lt(v_i_1962_, v___x_1964_);
                if v___x_1965_ == 0 {
                    leanh::lean_dec(v_i_1962_);
                    v___x_1966_ = leanh::lean_box(0);
                    return v___x_1966_;
                } else {
                    v_k_x27_1967_ = lean_array_fget_borrowed(v_keys_1960_, v_i_1962_);
                    v___x_1968_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1963_,
                            v_k_x27_1967_,
                        );
                    if v___x_1968_ == 0 {
                        v___x_1969_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1970_ = lean_nat_add(v_i_1962_, v___x_1969_);
                        leanh::lean_dec(v_i_1962_);
                        v_i_1962_ = v___x_1970_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1972_ = lean_array_fget_borrowed(v_vals_1961_, v_i_1962_);
                        leanh::lean_dec(v_i_1962_);
                        leanh::lean_inc(v___x_1972_);
                        v___x_1973_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1973_, 0, v___x_1972_);
                        return v___x_1973_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg___boxed(
    mut v_keys_1974_: *mut leanh::LeanObject,
    mut v_vals_1975_: *mut leanh::LeanObject,
    mut v_i_1976_: *mut leanh::LeanObject,
    mut v_k_1977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1978_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_keys_1974_, v_vals_1975_, v_i_1976_, v_k_1977_);
    leanh::lean_dec_ref(v_k_1977_);
    leanh::lean_dec_ref(v_vals_1975_);
    leanh::lean_dec_ref(v_keys_1974_);
    return v_res_1978_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_1979_: usize = 0;
    let mut v___x_1980_: usize = 0;
    let mut v___x_1981_: usize = 0;
    v___x_1979_ = 5usize;
    v___x_1980_ = 1usize;
    v___x_1981_ = lean_usize_shift_left(v___x_1980_, v___x_1979_);
    return v___x_1981_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_1982_: usize = 0;
    let mut v___x_1983_: usize = 0;
    let mut v___x_1984_: usize = 0;
    v___x_1982_ = 1usize;
    v___x_1983_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0);
    v___x_1984_ = lean_usize_sub(v___x_1983_, v___x_1982_);
    return v___x_1984_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(
    mut v_x_1985_: *mut leanh::LeanObject,
    mut v_x_1986_: usize,
    mut v_x_1987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: usize = 0;
    let mut v___x_1991_: usize = 0;
    let mut v___x_1992_: usize = 0;
    let mut v_j_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: usize = 0;
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1985_) == 0 {
                    v_es_1988_ = leanh::lean_ctor_get(v_x_1985_, 0);
                    v___x_1989_ = leanh::lean_box(2);
                    v___x_1990_ = 5usize;
                    v___x_1991_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1);
                    v___x_1992_ = lean_usize_land(v_x_1986_, v___x_1991_);
                    v_j_1993_ = lean_usize_to_nat(v___x_1992_);
                    v___x_1994_ = lean_array_get_borrowed(v___x_1989_, v_es_1988_, v_j_1993_);
                    leanh::lean_dec(v_j_1993_);
                    match leanh::lean_obj_tag(v___x_1994_) {
                        0 => {
                            v_key_1995_ = leanh::lean_ctor_get(v___x_1994_, 0);
                            v_val_1996_ = leanh::lean_ctor_get(v___x_1994_, 1);
                            v___x_1997_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1987_, v_key_1995_);
                            if v___x_1997_ == 0 {
                                v___x_1998_ = leanh::lean_box(0);
                                return v___x_1998_;
                            } else {
                                leanh::lean_inc(v_val_1996_);
                                v___x_1999_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1999_, 0, v_val_1996_);
                                return v___x_1999_;
                            }
                        }
                        1 => {
                            v_node_2000_ = leanh::lean_ctor_get(v___x_1994_, 0);
                            v___x_2001_ = lean_usize_shift_right(v_x_1986_, v___x_1990_);
                            v_x_1985_ = v_node_2000_;
                            v_x_1986_ = v___x_2001_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2003_ = leanh::lean_box(0);
                            return v___x_2003_;
                        }
                    }
                } else {
                    v_ks_2004_ = leanh::lean_ctor_get(v_x_1985_, 0);
                    v_vs_2005_ = leanh::lean_ctor_get(v_x_1985_, 1);
                    v___x_2006_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2007_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_ks_2004_, v_vs_2005_, v___x_2006_, v_x_1987_);
                    return v___x_2007_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___boxed(
    mut v_x_2008_: *mut leanh::LeanObject,
    mut v_x_2009_: *mut leanh::LeanObject,
    mut v_x_2010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_25664__boxed_2011_: usize = 0;
    let mut v_res_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_25664__boxed_2011_ = leanh::lean_unbox_usize(v_x_2009_);
    leanh::lean_dec(v_x_2009_);
    v_res_2012_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_2008_, v_x_25664__boxed_2011_, v_x_2010_);
    leanh::lean_dec_ref(v_x_2010_);
    leanh::lean_dec_ref(v_x_2008_);
    return v_res_2012_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(
    mut v_x_2013_: *mut leanh::LeanObject,
    mut v_x_2014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2015_: u64 = 0;
    let mut v___x_2016_: usize = 0;
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2014_);
    v___x_2016_ = lean_uint64_to_usize(v___x_2015_);
    v___x_2017_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_2013_, v___x_2016_, v_x_2014_);
    return v___x_2017_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg___boxed(
    mut v_x_2018_: *mut leanh::LeanObject,
    mut v_x_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2020_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_x_2018_, v_x_2019_);
    leanh::lean_dec_ref(v_x_2019_);
    leanh::lean_dec_ref(v_x_2018_);
    return v_res_2020_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(
    mut v_msg_2028_: *mut leanh::LeanObject,
    mut v___y_2029_: *mut leanh::LeanObject,
    mut v___y_2030_: u8,
    mut v___y_2031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_24871__overap_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2032_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0;
    v___f_2033_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1;
    v___f_2034_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2;
    v___f_2035_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3;
    v___f_2036_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4;
    v___f_2037_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5;
    v___f_2038_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6;
    v___x_2039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2039_, 0, v___f_2032_);
    leanh::lean_ctor_set(v___x_2039_, 1, v___f_2033_);
    v___x_2040_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2040_, 0, v___x_2039_);
    leanh::lean_ctor_set(v___x_2040_, 1, v___f_2034_);
    leanh::lean_ctor_set(v___x_2040_, 2, v___f_2035_);
    leanh::lean_ctor_set(v___x_2040_, 3, v___f_2036_);
    leanh::lean_ctor_set(v___x_2040_, 4, v___f_2037_);
    v___x_2041_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2041_, 0, v___x_2040_);
    leanh::lean_ctor_set(v___x_2041_, 1, v___f_2038_);
    leanh::lean_inc_ref_n(v___x_2041_, 6);
    v___f_2042_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2042_, 0, v___x_2041_);
    v___f_2043_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2043_, 0, v___x_2041_);
    v___f_2044_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2044_, 0, v___x_2041_);
    v___f_2045_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2045_, 0, v___x_2041_);
    v___x_2046_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_2046_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2046_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2046_, 2, v___x_2041_);
    v___x_2047_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2047_, 0, v___x_2046_);
    leanh::lean_ctor_set(v___x_2047_, 1, v___f_2042_);
    v___x_2048_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_2048_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2048_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2048_, 2, v___x_2041_);
    v___x_2049_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2049_, 0, v___x_2047_);
    leanh::lean_ctor_set(v___x_2049_, 1, v___x_2048_);
    leanh::lean_ctor_set(v___x_2049_, 2, v___f_2043_);
    leanh::lean_ctor_set(v___x_2049_, 3, v___f_2044_);
    leanh::lean_ctor_set(v___x_2049_, 4, v___f_2045_);
    v___x_2050_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_2050_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2050_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2050_, 2, v___x_2041_);
    v___x_2051_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2051_, 0, v___x_2049_);
    leanh::lean_ctor_set(v___x_2051_, 1, v___x_2050_);
    v___x_2052_ = l_ReaderT_instMonad___redArg(v___x_2051_);
    leanh::lean_inc_ref_n(v___x_2052_, 6);
    v___f_2053_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2053_, 0, v___x_2052_);
    v___f_2054_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2054_, 0, v___x_2052_);
    v___f_2055_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2055_, 0, v___x_2052_);
    v___f_2056_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2056_, 0, v___x_2052_);
    v___x_2057_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_2057_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2057_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2057_, 2, v___x_2052_);
    v___x_2058_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2058_, 0, v___x_2057_);
    leanh::lean_ctor_set(v___x_2058_, 1, v___f_2053_);
    v___x_2059_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_2059_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2059_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2059_, 2, v___x_2052_);
    v___x_2060_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2060_, 0, v___x_2058_);
    leanh::lean_ctor_set(v___x_2060_, 1, v___x_2059_);
    leanh::lean_ctor_set(v___x_2060_, 2, v___f_2054_);
    leanh::lean_ctor_set(v___x_2060_, 3, v___f_2055_);
    leanh::lean_ctor_set(v___x_2060_, 4, v___f_2056_);
    v___x_2061_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_2061_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2061_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2061_, 2, v___x_2052_);
    v___x_2062_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2062_, 0, v___x_2060_);
    leanh::lean_ctor_set(v___x_2062_, 1, v___x_2061_);
    v___x_2063_ = l_Lean_instInhabitedExpr;
    v___x_2064_ = l_instInhabitedOfMonad___redArg(v___x_2062_, v___x_2063_);
    v___x_24871__overap_2065_ = lean_panic_fn_borrowed(v___x_2064_, v_msg_2028_);
    leanh::lean_dec(v___x_2064_);
    v___x_2066_ = leanh::lean_box((v___y_2030_) as usize);
    v___x_2067_ = leanh::lean_apply_3(
        v___x_24871__overap_2065_,
        v___y_2029_,
        v___x_2066_,
        v___y_2031_,
    );
    return v___x_2067_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___boxed(
    mut v_msg_2068_: *mut leanh::LeanObject,
    mut v___y_2069_: *mut leanh::LeanObject,
    mut v___y_2070_: *mut leanh::LeanObject,
    mut v___y_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_25743__boxed_2072_: u8 = 0;
    let mut v_res_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_25743__boxed_2072_ = (leanh::lean_unbox(v___y_2070_) as u8);
    v_res_2073_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(v_msg_2068_, v___y_2069_, v___y_25743__boxed_2072_, v___y_2071_);
    return v_res_2073_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2077_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2;
    v___x_2078_ = leanh::lean_unsigned_to_nat(67);
    v___x_2079_ = leanh::lean_unsigned_to_nat(35);
    v___x_2080_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1;
    v___x_2081_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0;
    v___x_2082_ = l_mkPanicMessageWithDecl(
        v___x_2081_,
        v___x_2080_,
        v___x_2079_,
        v___x_2078_,
        v___x_2077_,
    );
    return v___x_2082_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(
    mut v_minIndex_2083_: *mut leanh::LeanObject,
    mut v___x_2084_: *mut leanh::LeanObject,
    mut v___x_2085_: *mut leanh::LeanObject,
    mut v_start_2086_: *mut leanh::LeanObject,
    mut v_xs_2087_: *mut leanh::LeanObject,
    mut v___x_2088_: *mut leanh::LeanObject,
    mut v_e_2089_: *mut leanh::LeanObject,
    mut v_offset_2090_: *mut leanh::LeanObject,
    mut v_a_2091_: *mut leanh::LeanObject,
    mut v_a_2092_: u8,
    mut v_a_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v_fst_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2111_: u8 = 0;
    let mut v___y_2113_: u8 = 0;
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: u8 = 0;
    let mut v___x_2122_: u8 = 0;
    let mut v_isSharedCheck_2123_: u8 = 0;
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_binderName_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2128_: u8 = 0;
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2141_: u8 = 0;
    let mut v_fst_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___y_2148_: u8 = 0;
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: u8 = 0;
    let mut v___x_2157_: u8 = 0;
    let mut v_isSharedCheck_2158_: u8 = 0;
    let mut v_isSharedCheck_2159_: u8 = 0;
    let mut v_binderName_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2163_: u8 = 0;
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2176_: u8 = 0;
    let mut v_fst_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2181_: u8 = 0;
    let mut v___y_2183_: u8 = 0;
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: u8 = 0;
    let mut v_isSharedCheck_2193_: u8 = 0;
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut v_declName_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2199_: u8 = 0;
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v_fst_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___y_2224_: u8 = 0;
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: u8 = 0;
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_data_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v_fst_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v_typeName_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2269_: u8 = 0;
    let mut v_fst_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2275_: u8 = 0;
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2283_: u8 = 0;
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_2089_) {
                5 => {
                    v_fn_2094_ = leanh::lean_ctor_get(v_e_2089_, 0);
                    v_arg_2095_ = leanh::lean_ctor_get(v_e_2089_, 1);
                    leanh::lean_inc(v_offset_2090_);
                    leanh::lean_inc_ref(v_fn_2094_);
                    leanh::lean_inc_ref(v___x_2084_);
                    v___x_2096_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_fn_2094_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2097_ = leanh::lean_ctor_get(v___x_2096_, 0);
                    leanh::lean_inc(v_fst_2097_);
                    v_snd_2098_ = leanh::lean_ctor_get(v___x_2096_, 1);
                    leanh::lean_inc(v_snd_2098_);
                    leanh::lean_dec_ref(v___x_2096_);
                    v_fst_2099_ = leanh::lean_ctor_get(v_fst_2097_, 0);
                    leanh::lean_inc(v_fst_2099_);
                    v_snd_2100_ = leanh::lean_ctor_get(v_fst_2097_, 1);
                    leanh::lean_inc(v_snd_2100_);
                    leanh::lean_dec(v_fst_2097_);
                    leanh::lean_inc_ref(v_arg_2095_);
                    v___x_2101_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_arg_2095_, v_offset_2090_, v_snd_2100_, v_a_2092_, v_snd_2098_);
                    v_fst_2102_ = leanh::lean_ctor_get(v___x_2101_, 0);
                    v_snd_2103_ = leanh::lean_ctor_get(v___x_2101_, 1);
                    v_isSharedCheck_2124_ = (!leanh::lean_is_exclusive(v___x_2101_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v___x_2105_ = v___x_2101_;
                        v_isShared_2106_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2103_);
                        leanh::lean_inc(v_fst_2102_);
                        leanh::lean_dec(v___x_2101_);
                        v___x_2105_ = leanh::lean_box(0);
                        v_isShared_2106_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_2125_ = leanh::lean_ctor_get(v_e_2089_, 0);
                    v_binderType_2126_ = leanh::lean_ctor_get(v_e_2089_, 1);
                    v_body_2127_ = leanh::lean_ctor_get(v_e_2089_, 2);
                    v_binderInfo_2128_ = leanh::lean_ctor_get_uint8(
                        v_e_2089_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc(v_offset_2090_);
                    leanh::lean_inc_ref(v_binderType_2126_);
                    leanh::lean_inc_ref(v___x_2084_);
                    v___x_2129_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_binderType_2126_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2130_ = leanh::lean_ctor_get(v___x_2129_, 0);
                    leanh::lean_inc(v_fst_2130_);
                    v_snd_2131_ = leanh::lean_ctor_get(v___x_2129_, 1);
                    leanh::lean_inc(v_snd_2131_);
                    leanh::lean_dec_ref(v___x_2129_);
                    v_fst_2132_ = leanh::lean_ctor_get(v_fst_2130_, 0);
                    leanh::lean_inc(v_fst_2132_);
                    v_snd_2133_ = leanh::lean_ctor_get(v_fst_2130_, 1);
                    leanh::lean_inc(v_snd_2133_);
                    leanh::lean_dec(v_fst_2130_);
                    v___x_2134_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2135_ = lean_nat_add(v_offset_2090_, v___x_2134_);
                    leanh::lean_dec(v_offset_2090_);
                    leanh::lean_inc_ref(v_body_2127_);
                    v___x_2136_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_body_2127_, v___x_2135_, v_snd_2133_, v_a_2092_, v_snd_2131_);
                    v_fst_2137_ = leanh::lean_ctor_get(v___x_2136_, 0);
                    v_snd_2138_ = leanh::lean_ctor_get(v___x_2136_, 1);
                    v_isSharedCheck_2159_ = (!leanh::lean_is_exclusive(v___x_2136_)) as u8;
                    if v_isSharedCheck_2159_ == 0 {
                        v___x_2140_ = v___x_2136_;
                        v_isShared_2141_ = v_isSharedCheck_2159_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2138_);
                        leanh::lean_inc(v_fst_2137_);
                        leanh::lean_dec(v___x_2136_);
                        v___x_2140_ = leanh::lean_box(0);
                        v_isShared_2141_ = v_isSharedCheck_2159_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_2160_ = leanh::lean_ctor_get(v_e_2089_, 0);
                    v_binderType_2161_ = leanh::lean_ctor_get(v_e_2089_, 1);
                    v_body_2162_ = leanh::lean_ctor_get(v_e_2089_, 2);
                    v_binderInfo_2163_ = leanh::lean_ctor_get_uint8(
                        v_e_2089_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    leanh::lean_inc(v_offset_2090_);
                    leanh::lean_inc_ref(v_binderType_2161_);
                    leanh::lean_inc_ref(v___x_2084_);
                    v___x_2164_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_binderType_2161_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2165_ = leanh::lean_ctor_get(v___x_2164_, 0);
                    leanh::lean_inc(v_fst_2165_);
                    v_snd_2166_ = leanh::lean_ctor_get(v___x_2164_, 1);
                    leanh::lean_inc(v_snd_2166_);
                    leanh::lean_dec_ref(v___x_2164_);
                    v_fst_2167_ = leanh::lean_ctor_get(v_fst_2165_, 0);
                    leanh::lean_inc(v_fst_2167_);
                    v_snd_2168_ = leanh::lean_ctor_get(v_fst_2165_, 1);
                    leanh::lean_inc(v_snd_2168_);
                    leanh::lean_dec(v_fst_2165_);
                    v___x_2169_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2170_ = lean_nat_add(v_offset_2090_, v___x_2169_);
                    leanh::lean_dec(v_offset_2090_);
                    leanh::lean_inc_ref(v_body_2162_);
                    v___x_2171_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_body_2162_, v___x_2170_, v_snd_2168_, v_a_2092_, v_snd_2166_);
                    v_fst_2172_ = leanh::lean_ctor_get(v___x_2171_, 0);
                    v_snd_2173_ = leanh::lean_ctor_get(v___x_2171_, 1);
                    v_isSharedCheck_2194_ = (!leanh::lean_is_exclusive(v___x_2171_)) as u8;
                    if v_isSharedCheck_2194_ == 0 {
                        v___x_2175_ = v___x_2171_;
                        v_isShared_2176_ = v_isSharedCheck_2194_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2173_);
                        leanh::lean_inc(v_fst_2172_);
                        leanh::lean_dec(v___x_2171_);
                        v___x_2175_ = leanh::lean_box(0);
                        v_isShared_2176_ = v_isSharedCheck_2194_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_2195_ = leanh::lean_ctor_get(v_e_2089_, 0);
                    v_type_2196_ = leanh::lean_ctor_get(v_e_2089_, 1);
                    v_value_2197_ = leanh::lean_ctor_get(v_e_2089_, 2);
                    v_body_2198_ = leanh::lean_ctor_get(v_e_2089_, 3);
                    v_nondep_2199_ = leanh::lean_ctor_get_uint8(
                        v_e_2089_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_inc_n(v_offset_2090_, 2);
                    leanh::lean_inc_ref(v_type_2196_);
                    leanh::lean_inc_ref_n(v___x_2084_, 2);
                    v___x_2200_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_type_2196_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2201_ = leanh::lean_ctor_get(v___x_2200_, 0);
                    leanh::lean_inc(v_fst_2201_);
                    v_snd_2202_ = leanh::lean_ctor_get(v___x_2200_, 1);
                    leanh::lean_inc(v_snd_2202_);
                    leanh::lean_dec_ref(v___x_2200_);
                    v_fst_2203_ = leanh::lean_ctor_get(v_fst_2201_, 0);
                    leanh::lean_inc(v_fst_2203_);
                    v_snd_2204_ = leanh::lean_ctor_get(v_fst_2201_, 1);
                    leanh::lean_inc(v_snd_2204_);
                    leanh::lean_dec(v_fst_2201_);
                    leanh::lean_inc_ref(v_value_2197_);
                    v___x_2205_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_value_2197_, v_offset_2090_, v_snd_2204_, v_a_2092_, v_snd_2202_);
                    v_fst_2206_ = leanh::lean_ctor_get(v___x_2205_, 0);
                    leanh::lean_inc(v_fst_2206_);
                    v_snd_2207_ = leanh::lean_ctor_get(v___x_2205_, 1);
                    leanh::lean_inc(v_snd_2207_);
                    leanh::lean_dec_ref(v___x_2205_);
                    v_fst_2208_ = leanh::lean_ctor_get(v_fst_2206_, 0);
                    leanh::lean_inc(v_fst_2208_);
                    v_snd_2209_ = leanh::lean_ctor_get(v_fst_2206_, 1);
                    leanh::lean_inc(v_snd_2209_);
                    leanh::lean_dec(v_fst_2206_);
                    v___x_2210_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2211_ = lean_nat_add(v_offset_2090_, v___x_2210_);
                    leanh::lean_dec(v_offset_2090_);
                    leanh::lean_inc_ref(v_body_2198_);
                    v___x_2212_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_body_2198_, v___x_2211_, v_snd_2209_, v_a_2092_, v_snd_2207_);
                    v_fst_2213_ = leanh::lean_ctor_get(v___x_2212_, 0);
                    v_snd_2214_ = leanh::lean_ctor_get(v___x_2212_, 1);
                    v_isSharedCheck_2237_ = (!leanh::lean_is_exclusive(v___x_2212_)) as u8;
                    if v_isSharedCheck_2237_ == 0 {
                        v___x_2216_ = v___x_2212_;
                        v_isShared_2217_ = v_isSharedCheck_2237_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2214_);
                        leanh::lean_inc(v_fst_2213_);
                        leanh::lean_dec(v___x_2212_);
                        v___x_2216_ = leanh::lean_box(0);
                        v_isShared_2217_ = v_isSharedCheck_2237_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_2238_ = leanh::lean_ctor_get(v_e_2089_, 0);
                    v_expr_2239_ = leanh::lean_ctor_get(v_e_2089_, 1);
                    leanh::lean_inc_ref(v_expr_2239_);
                    v___x_2240_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_expr_2239_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2241_ = leanh::lean_ctor_get(v___x_2240_, 0);
                    v_snd_2242_ = leanh::lean_ctor_get(v___x_2240_, 1);
                    v_isSharedCheck_2260_ = (!leanh::lean_is_exclusive(v___x_2240_)) as u8;
                    if v_isSharedCheck_2260_ == 0 {
                        v___x_2244_ = v___x_2240_;
                        v_isShared_2245_ = v_isSharedCheck_2260_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2242_);
                        leanh::lean_inc(v_fst_2241_);
                        leanh::lean_dec(v___x_2240_);
                        v___x_2244_ = leanh::lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2260_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_2261_ = leanh::lean_ctor_get(v_e_2089_, 0);
                    v_idx_2262_ = leanh::lean_ctor_get(v_e_2089_, 1);
                    v_struct_2263_ = leanh::lean_ctor_get(v_e_2089_, 2);
                    leanh::lean_inc_ref(v_struct_2263_);
                    v___x_2264_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_struct_2263_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2265_ = leanh::lean_ctor_get(v___x_2264_, 0);
                    v_snd_2266_ = leanh::lean_ctor_get(v___x_2264_, 1);
                    v_isSharedCheck_2284_ = (!leanh::lean_is_exclusive(v___x_2264_)) as u8;
                    if v_isSharedCheck_2284_ == 0 {
                        v___x_2268_ = v___x_2264_;
                        v_isShared_2269_ = v_isSharedCheck_2284_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2266_);
                        leanh::lean_inc(v_fst_2265_);
                        leanh::lean_dec(v___x_2264_);
                        v___x_2268_ = leanh::lean_box(0);
                        v_isShared_2269_ = v_isSharedCheck_2284_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_offset_2090_);
                    leanh::lean_dec_ref(v_e_2089_);
                    leanh::lean_dec_ref(v___x_2084_);
                    v___x_2285_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3);
                    v___x_2286_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(v___x_2285_, v_a_2091_, v_a_2092_, v_a_2093_);
                    return v___x_2286_;
                }
            },
            1 => {
                v_fst_2107_ = leanh::lean_ctor_get(v_fst_2102_, 0);
                v_snd_2108_ = leanh::lean_ctor_get(v_fst_2102_, 1);
                v_isSharedCheck_2123_ = (!leanh::lean_is_exclusive(v_fst_2102_)) as u8;
                if v_isSharedCheck_2123_ == 0 {
                    v___x_2110_ = v_fst_2102_;
                    v_isShared_2111_ = v_isSharedCheck_2123_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2108_);
                    leanh::lean_inc(v_fst_2107_);
                    leanh::lean_dec(v_fst_2102_);
                    v___x_2110_ = leanh::lean_box(0);
                    v_isShared_2111_ = v_isSharedCheck_2123_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2121_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_fn_2094_,
                        v_fst_2099_,
                    );
                if v___x_2121_ == 0 {
                    v___y_2113_ = v___x_2121_;
                    state = 3;
                    continue;
                } else {
                    v___x_2122_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_2095_,
                            v_fst_2107_,
                        );
                    v___y_2113_ = v___x_2122_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_2113_ == 0 {
                    leanh::lean_del_object(v___x_2110_);
                    leanh::lean_del_object(v___x_2105_);
                    leanh::lean_dec_ref_known(v_e_2089_, 2);
                    v___x_2114_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(v_fst_2099_, v_fst_2107_, v_snd_2108_, v_a_2092_, v_snd_2103_);
                    return v___x_2114_;
                } else {
                    leanh::lean_dec(v_fst_2107_);
                    leanh::lean_dec(v_fst_2099_);
                    if v_isShared_2111_ == 0 {
                        leanh::lean_ctor_set(v___x_2110_, 0, v_e_2089_);
                        v___x_2116_ = v___x_2110_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2120_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_e_2089_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_snd_2108_);
                        v___x_2116_ = v_reuseFailAlloc_2120_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2106_ == 0 {
                    leanh::lean_ctor_set(v___x_2105_, 0, v___x_2116_);
                    v___x_2118_ = v___x_2105_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_snd_2103_);
                    v___x_2118_ = v_reuseFailAlloc_2119_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2118_;
            }
            6 => {
                v_fst_2142_ = leanh::lean_ctor_get(v_fst_2137_, 0);
                v_snd_2143_ = leanh::lean_ctor_get(v_fst_2137_, 1);
                v_isSharedCheck_2158_ = (!leanh::lean_is_exclusive(v_fst_2137_)) as u8;
                if v_isSharedCheck_2158_ == 0 {
                    v___x_2145_ = v_fst_2137_;
                    v_isShared_2146_ = v_isSharedCheck_2158_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2143_);
                    leanh::lean_inc(v_fst_2142_);
                    leanh::lean_dec(v_fst_2137_);
                    v___x_2145_ = leanh::lean_box(0);
                    v_isShared_2146_ = v_isSharedCheck_2158_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2156_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_2126_,
                        v_fst_2132_,
                    );
                if v___x_2156_ == 0 {
                    v___y_2148_ = v___x_2156_;
                    state = 8;
                    continue;
                } else {
                    v___x_2157_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_2127_,
                            v_fst_2142_,
                        );
                    v___y_2148_ = v___x_2157_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_2148_ == 0 {
                    leanh::lean_inc(v_binderName_2125_);
                    leanh::lean_del_object(v___x_2145_);
                    leanh::lean_del_object(v___x_2140_);
                    leanh::lean_dec_ref_known(v_e_2089_, 3);
                    v___x_2149_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(v_binderName_2125_, v_binderInfo_2128_, v_fst_2132_, v_fst_2142_, v_snd_2143_, v_a_2092_, v_snd_2138_);
                    return v___x_2149_;
                } else {
                    leanh::lean_dec(v_fst_2142_);
                    leanh::lean_dec(v_fst_2132_);
                    if v_isShared_2146_ == 0 {
                        leanh::lean_ctor_set(v___x_2145_, 0, v_e_2089_);
                        v___x_2151_ = v___x_2145_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2155_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_e_2089_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_snd_2143_);
                        v___x_2151_ = v_reuseFailAlloc_2155_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2141_ == 0 {
                    leanh::lean_ctor_set(v___x_2140_, 0, v___x_2151_);
                    v___x_2153_ = v___x_2140_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_snd_2138_);
                    v___x_2153_ = v_reuseFailAlloc_2154_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2153_;
            }
            11 => {
                v_fst_2177_ = leanh::lean_ctor_get(v_fst_2172_, 0);
                v_snd_2178_ = leanh::lean_ctor_get(v_fst_2172_, 1);
                v_isSharedCheck_2193_ = (!leanh::lean_is_exclusive(v_fst_2172_)) as u8;
                if v_isSharedCheck_2193_ == 0 {
                    v___x_2180_ = v_fst_2172_;
                    v_isShared_2181_ = v_isSharedCheck_2193_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2178_);
                    leanh::lean_inc(v_fst_2177_);
                    leanh::lean_dec(v_fst_2172_);
                    v___x_2180_ = leanh::lean_box(0);
                    v_isShared_2181_ = v_isSharedCheck_2193_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2191_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_2161_,
                        v_fst_2167_,
                    );
                if v___x_2191_ == 0 {
                    v___y_2183_ = v___x_2191_;
                    state = 13;
                    continue;
                } else {
                    v___x_2192_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_2162_,
                            v_fst_2177_,
                        );
                    v___y_2183_ = v___x_2192_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_2183_ == 0 {
                    leanh::lean_inc(v_binderName_2160_);
                    leanh::lean_del_object(v___x_2180_);
                    leanh::lean_del_object(v___x_2175_);
                    leanh::lean_dec_ref_known(v_e_2089_, 3);
                    v___x_2184_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(v_binderName_2160_, v_binderInfo_2163_, v_fst_2167_, v_fst_2177_, v_snd_2178_, v_a_2092_, v_snd_2173_);
                    return v___x_2184_;
                } else {
                    leanh::lean_dec(v_fst_2177_);
                    leanh::lean_dec(v_fst_2167_);
                    if v_isShared_2181_ == 0 {
                        leanh::lean_ctor_set(v___x_2180_, 0, v_e_2089_);
                        v___x_2186_ = v___x_2180_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2190_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_e_2089_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_snd_2178_);
                        v___x_2186_ = v_reuseFailAlloc_2190_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2176_ == 0 {
                    leanh::lean_ctor_set(v___x_2175_, 0, v___x_2186_);
                    v___x_2188_ = v___x_2175_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_snd_2173_);
                    v___x_2188_ = v_reuseFailAlloc_2189_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2188_;
            }
            16 => {
                v_fst_2218_ = leanh::lean_ctor_get(v_fst_2213_, 0);
                v_snd_2219_ = leanh::lean_ctor_get(v_fst_2213_, 1);
                v_isSharedCheck_2236_ = (!leanh::lean_is_exclusive(v_fst_2213_)) as u8;
                if v_isSharedCheck_2236_ == 0 {
                    v___x_2221_ = v_fst_2213_;
                    v_isShared_2222_ = v_isSharedCheck_2236_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2219_);
                    leanh::lean_inc(v_fst_2218_);
                    leanh::lean_dec(v_fst_2213_);
                    v___x_2221_ = leanh::lean_box(0);
                    v_isShared_2222_ = v_isSharedCheck_2236_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2234_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_2196_,
                        v_fst_2203_,
                    );
                if v___x_2234_ == 0 {
                    v___y_2224_ = v___x_2234_;
                    state = 18;
                    continue;
                } else {
                    v___x_2235_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_value_2197_,
                            v_fst_2208_,
                        );
                    v___y_2224_ = v___x_2235_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_2224_ == 0 {
                    leanh::lean_inc(v_declName_2195_);
                    leanh::lean_del_object(v___x_2221_);
                    leanh::lean_del_object(v___x_2216_);
                    leanh::lean_dec_ref_known(v_e_2089_, 4);
                    v___x_2225_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_declName_2195_, v_fst_2203_, v_fst_2208_, v_fst_2218_, v_nondep_2199_, v_snd_2219_, v_a_2092_, v_snd_2214_);
                    return v___x_2225_;
                } else {
                    v___x_2226_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_2198_,
                            v_fst_2218_,
                        );
                    if v___x_2226_ == 0 {
                        leanh::lean_inc(v_declName_2195_);
                        leanh::lean_del_object(v___x_2221_);
                        leanh::lean_del_object(v___x_2216_);
                        leanh::lean_dec_ref_known(v_e_2089_, 4);
                        v___x_2227_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_declName_2195_, v_fst_2203_, v_fst_2208_, v_fst_2218_, v_nondep_2199_, v_snd_2219_, v_a_2092_, v_snd_2214_);
                        return v___x_2227_;
                    } else {
                        leanh::lean_dec(v_fst_2218_);
                        leanh::lean_dec(v_fst_2208_);
                        leanh::lean_dec(v_fst_2203_);
                        if v_isShared_2222_ == 0 {
                            leanh::lean_ctor_set(v___x_2221_, 0, v_e_2089_);
                            v___x_2229_ = v___x_2221_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_2233_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_e_2089_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_snd_2219_);
                            v___x_2229_ = v_reuseFailAlloc_2233_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_2217_ == 0 {
                    leanh::lean_ctor_set(v___x_2216_, 0, v___x_2229_);
                    v___x_2231_ = v___x_2216_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_snd_2214_);
                    v___x_2231_ = v_reuseFailAlloc_2232_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2231_;
            }
            21 => {
                v_fst_2246_ = leanh::lean_ctor_get(v_fst_2241_, 0);
                v_snd_2247_ = leanh::lean_ctor_get(v_fst_2241_, 1);
                v_isSharedCheck_2259_ = (!leanh::lean_is_exclusive(v_fst_2241_)) as u8;
                if v_isSharedCheck_2259_ == 0 {
                    v___x_2249_ = v_fst_2241_;
                    v_isShared_2250_ = v_isSharedCheck_2259_;
                    state = 22;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2247_);
                    leanh::lean_inc(v_fst_2246_);
                    leanh::lean_dec(v_fst_2241_);
                    v___x_2249_ = leanh::lean_box(0);
                    v_isShared_2250_ = v_isSharedCheck_2259_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_2251_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_expr_2239_,
                        v_fst_2246_,
                    );
                if v___x_2251_ == 0 {
                    leanh::lean_inc(v_data_2238_);
                    leanh::lean_del_object(v___x_2249_);
                    leanh::lean_del_object(v___x_2244_);
                    leanh::lean_dec_ref_known(v_e_2089_, 2);
                    v___x_2252_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(v_data_2238_, v_fst_2246_, v_snd_2247_, v_a_2092_, v_snd_2242_);
                    return v___x_2252_;
                } else {
                    leanh::lean_dec(v_fst_2246_);
                    if v_isShared_2250_ == 0 {
                        leanh::lean_ctor_set(v___x_2249_, 0, v_e_2089_);
                        v___x_2254_ = v___x_2249_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2258_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_e_2089_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_snd_2247_);
                        v___x_2254_ = v_reuseFailAlloc_2258_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_2245_ == 0 {
                    leanh::lean_ctor_set(v___x_2244_, 0, v___x_2254_);
                    v___x_2256_ = v___x_2244_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2257_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_snd_2242_);
                    v___x_2256_ = v_reuseFailAlloc_2257_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2256_;
            }
            25 => {
                v_fst_2270_ = leanh::lean_ctor_get(v_fst_2265_, 0);
                v_snd_2271_ = leanh::lean_ctor_get(v_fst_2265_, 1);
                v_isSharedCheck_2283_ = (!leanh::lean_is_exclusive(v_fst_2265_)) as u8;
                if v_isSharedCheck_2283_ == 0 {
                    v___x_2273_ = v_fst_2265_;
                    v_isShared_2274_ = v_isSharedCheck_2283_;
                    state = 26;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2271_);
                    leanh::lean_inc(v_fst_2270_);
                    leanh::lean_dec(v_fst_2265_);
                    v___x_2273_ = leanh::lean_box(0);
                    v_isShared_2274_ = v_isSharedCheck_2283_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_2275_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_struct_2263_,
                        v_fst_2270_,
                    );
                if v___x_2275_ == 0 {
                    leanh::lean_inc(v_idx_2262_);
                    leanh::lean_inc(v_typeName_2261_);
                    leanh::lean_del_object(v___x_2273_);
                    leanh::lean_del_object(v___x_2268_);
                    leanh::lean_dec_ref_known(v_e_2089_, 3);
                    v___x_2276_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(v_typeName_2261_, v_idx_2262_, v_fst_2270_, v_snd_2271_, v_a_2092_, v_snd_2266_);
                    return v___x_2276_;
                } else {
                    leanh::lean_dec(v_fst_2270_);
                    if v_isShared_2274_ == 0 {
                        leanh::lean_ctor_set(v___x_2273_, 0, v_e_2089_);
                        v___x_2278_ = v___x_2273_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_2282_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_e_2089_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_snd_2271_);
                        v___x_2278_ = v_reuseFailAlloc_2282_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2269_ == 0 {
                    leanh::lean_ctor_set(v___x_2268_, 0, v___x_2278_);
                    v___x_2280_ = v___x_2268_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2281_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_snd_2266_);
                    v___x_2280_ = v_reuseFailAlloc_2281_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2280_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(
    mut v_minIndex_2287_: *mut leanh::LeanObject,
    mut v___x_2288_: *mut leanh::LeanObject,
    mut v___x_2289_: *mut leanh::LeanObject,
    mut v_start_2290_: *mut leanh::LeanObject,
    mut v_xs_2291_: *mut leanh::LeanObject,
    mut v___x_2292_: *mut leanh::LeanObject,
    mut v_e_2293_: *mut leanh::LeanObject,
    mut v_offset_2294_: *mut leanh::LeanObject,
    mut v_a_2295_: *mut leanh::LeanObject,
    mut v_a_2296_: u8,
    mut v_a_2297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxIndex_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: u8 = 0;
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_offset_2294_);
                leanh::lean_inc_ref(v_e_2293_);
                v_key_2298_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_key_2298_, 0, v_e_2293_);
                leanh::lean_ctor_set(v_key_2298_, 1, v_offset_2294_);
                v___x_2324_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_a_2295_, v_key_2298_);
                if leanh::lean_obj_tag(v___x_2324_) == 1 {
                    leanh::lean_dec_ref_known(v_key_2298_, 2);
                    leanh::lean_dec(v_offset_2294_);
                    leanh::lean_dec_ref(v_e_2293_);
                    leanh::lean_dec_ref(v___x_2288_);
                    v_val_2325_ = leanh::lean_ctor_get(v___x_2324_, 0);
                    leanh::lean_inc(v_val_2325_);
                    leanh::lean_dec_ref_known(v___x_2324_, 1);
                    v___x_2326_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2326_, 0, v_val_2325_);
                    leanh::lean_ctor_set(v___x_2326_, 1, v_a_2295_);
                    v___x_2327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2327_, 0, v___x_2326_);
                    leanh::lean_ctor_set(v___x_2327_, 1, v_a_2297_);
                    return v___x_2327_;
                } else {
                    leanh::lean_dec(v___x_2324_);
                    match leanh::lean_obj_tag(v_e_2293_) {
                        1 => {
                            leanh::lean_dec_ref(v___x_2288_);
                            v_fvarId_2328_ = leanh::lean_ctor_get(v_e_2293_, 0);
                            v___x_2329_ = leanh::lean_unsigned_to_nat(0);
                            v___x_2330_ = leanh::lean_unsigned_to_nat(1);
                            v___x_2331_ = lean_nat_sub(v___x_2289_, v___x_2330_);
                            v___x_2332_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_2290_, v_xs_2291_, v_fvarId_2328_, v___x_2329_, v___x_2331_);
                            if leanh::lean_obj_tag(v___x_2332_) == 1 {
                                leanh::lean_dec_ref_known(v_e_2293_, 1);
                                v_val_2333_ = leanh::lean_ctor_get(v___x_2332_, 0);
                                leanh::lean_inc(v_val_2333_);
                                leanh::lean_dec_ref_known(v___x_2332_, 1);
                                v___x_2334_ = lean_nat_add(v_offset_2294_, v_val_2333_);
                                leanh::lean_dec(v_val_2333_);
                                leanh::lean_dec(v_offset_2294_);
                                v___x_2335_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_2334_, v_a_2297_);
                                v_fst_2336_ = leanh::lean_ctor_get(v___x_2335_, 0);
                                leanh::lean_inc(v_fst_2336_);
                                v_snd_2337_ = leanh::lean_ctor_get(v___x_2335_, 1);
                                leanh::lean_inc(v_snd_2337_);
                                leanh::lean_dec_ref(v___x_2335_);
                                v___x_2338_ =
                                    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                        v_key_2298_,
                                        v_fst_2336_,
                                        v_a_2295_,
                                        v_a_2296_,
                                        v_snd_2337_,
                                    );
                                return v___x_2338_;
                            } else {
                                leanh::lean_dec(v___x_2332_);
                                leanh::lean_dec(v_offset_2294_);
                                v___x_2339_ =
                                    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                        v_key_2298_,
                                        v_e_2293_,
                                        v_a_2295_,
                                        v_a_2296_,
                                        v_a_2297_,
                                    );
                                return v___x_2339_;
                            }
                        }
                        9 => {
                            leanh::lean_dec(v_offset_2294_);
                            leanh::lean_dec_ref(v___x_2288_);
                            v___x_2340_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2298_,
                                v_e_2293_,
                                v_a_2295_,
                                v_a_2296_,
                                v_a_2297_,
                            );
                            return v___x_2340_;
                        }
                        2 => {
                            leanh::lean_dec(v_offset_2294_);
                            leanh::lean_dec_ref(v___x_2288_);
                            v___x_2341_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2298_,
                                v_e_2293_,
                                v_a_2295_,
                                v_a_2296_,
                                v_a_2297_,
                            );
                            return v___x_2341_;
                        }
                        0 => {
                            leanh::lean_dec(v_offset_2294_);
                            leanh::lean_dec_ref(v___x_2288_);
                            v___x_2342_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2298_,
                                v_e_2293_,
                                v_a_2295_,
                                v_a_2296_,
                                v_a_2297_,
                            );
                            return v___x_2342_;
                        }
                        4 => {
                            leanh::lean_dec(v_offset_2294_);
                            leanh::lean_dec_ref(v___x_2288_);
                            v___x_2343_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2298_,
                                v_e_2293_,
                                v_a_2295_,
                                v_a_2296_,
                                v_a_2297_,
                            );
                            return v___x_2343_;
                        }
                        3 => {
                            leanh::lean_dec(v_offset_2294_);
                            leanh::lean_dec_ref(v___x_2288_);
                            v___x_2344_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2298_,
                                v_e_2293_,
                                v_a_2295_,
                                v_a_2296_,
                                v_a_2297_,
                            );
                            return v___x_2344_;
                        }
                        _ => {
                            v___x_2345_ = l_Lean_Expr_hasFVar(v_e_2293_);
                            if v___x_2345_ == 0 {
                                leanh::lean_dec(v_offset_2294_);
                                leanh::lean_dec_ref(v___x_2288_);
                                v___x_2346_ =
                                    l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                        v_key_2298_,
                                        v_e_2293_,
                                        v_a_2295_,
                                        v_a_2296_,
                                        v_a_2297_,
                                    );
                                return v___x_2346_;
                            } else {
                                v___x_2347_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v___x_2292_, v_e_2293_);
                                if leanh::lean_obj_tag(v___x_2347_) == 1 {
                                    v_val_2348_ = leanh::lean_ctor_get(v___x_2347_, 0);
                                    leanh::lean_inc(v_val_2348_);
                                    leanh::lean_dec_ref_known(v___x_2347_, 1);
                                    if leanh::lean_obj_tag(v_val_2348_) == 0 {
                                        v___x_2349_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                                        v___x_2350_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___x_2349_);
                                        v___y_2319_ = v___x_2350_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v_val_2351_ = leanh::lean_ctor_get(v_val_2348_, 0);
                                        leanh::lean_inc(v_val_2351_);
                                        leanh::lean_dec_ref_known(v_val_2348_, 1);
                                        v___y_2319_ = v_val_2351_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_2347_);
                                    v_snd_2300_ = v_a_2297_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => match leanh::lean_obj_tag(v_e_2293_) {
                9 => {
                    leanh::lean_dec(v_offset_2294_);
                    leanh::lean_dec_ref(v___x_2288_);
                    v___x_2301_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2298_,
                        v_e_2293_,
                        v_a_2295_,
                        v_a_2296_,
                        v_snd_2300_,
                    );
                    return v___x_2301_;
                }
                2 => {
                    leanh::lean_dec(v_offset_2294_);
                    leanh::lean_dec_ref(v___x_2288_);
                    v___x_2302_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2298_,
                        v_e_2293_,
                        v_a_2295_,
                        v_a_2296_,
                        v_snd_2300_,
                    );
                    return v___x_2302_;
                }
                0 => {
                    leanh::lean_dec(v_offset_2294_);
                    leanh::lean_dec_ref(v___x_2288_);
                    v___x_2303_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2298_,
                        v_e_2293_,
                        v_a_2295_,
                        v_a_2296_,
                        v_snd_2300_,
                    );
                    return v___x_2303_;
                }
                1 => {
                    leanh::lean_dec(v_offset_2294_);
                    leanh::lean_dec_ref(v___x_2288_);
                    v___x_2304_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2298_,
                        v_e_2293_,
                        v_a_2295_,
                        v_a_2296_,
                        v_snd_2300_,
                    );
                    return v___x_2304_;
                }
                4 => {
                    leanh::lean_dec(v_offset_2294_);
                    leanh::lean_dec_ref(v___x_2288_);
                    v___x_2305_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2298_,
                        v_e_2293_,
                        v_a_2295_,
                        v_a_2296_,
                        v_snd_2300_,
                    );
                    return v___x_2305_;
                }
                3 => {
                    leanh::lean_dec(v_offset_2294_);
                    leanh::lean_dec_ref(v___x_2288_);
                    v___x_2306_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2298_,
                        v_e_2293_,
                        v_a_2295_,
                        v_a_2296_,
                        v_snd_2300_,
                    );
                    return v___x_2306_;
                }
                _ => {
                    v___x_2307_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_minIndex_2287_, v___x_2288_, v___x_2289_, v_start_2290_, v_xs_2291_, v___x_2292_, v_e_2293_, v_offset_2294_, v_a_2295_, v_a_2296_, v_snd_2300_);
                    v_fst_2308_ = leanh::lean_ctor_get(v___x_2307_, 0);
                    leanh::lean_inc(v_fst_2308_);
                    v_snd_2309_ = leanh::lean_ctor_get(v___x_2307_, 1);
                    leanh::lean_inc(v_snd_2309_);
                    leanh::lean_dec_ref(v___x_2307_);
                    v_fst_2310_ = leanh::lean_ctor_get(v_fst_2308_, 0);
                    leanh::lean_inc(v_fst_2310_);
                    v_snd_2311_ = leanh::lean_ctor_get(v_fst_2308_, 1);
                    leanh::lean_inc(v_snd_2311_);
                    leanh::lean_dec(v_fst_2308_);
                    v___x_2312_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2298_,
                        v_fst_2310_,
                        v_snd_2311_,
                        v_a_2296_,
                        v_snd_2309_,
                    );
                    return v___x_2312_;
                }
            },
            2 => {
                v_maxIndex_2315_ = l_Lean_LocalDecl_index(v___y_2314_);
                leanh::lean_dec_ref(v___y_2314_);
                v___x_2316_ = lean_nat_dec_lt(v_maxIndex_2315_, v_minIndex_2287_);
                leanh::lean_dec(v_maxIndex_2315_);
                if v___x_2316_ == 0 {
                    v_snd_2300_ = v_a_2297_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_offset_2294_);
                    leanh::lean_dec_ref(v___x_2288_);
                    v___x_2317_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2298_,
                        v_e_2293_,
                        v_a_2295_,
                        v_a_2296_,
                        v_a_2297_,
                    );
                    return v___x_2317_;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___x_2288_);
                v___x_2320_ = lean_local_ctx_find(v___x_2288_, v___y_2319_);
                if leanh::lean_obj_tag(v___x_2320_) == 0 {
                    v___x_2321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                    v___x_2322_ =
                        l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_2321_);
                    v___y_2314_ = v___x_2322_;
                    state = 2;
                    continue;
                } else {
                    v_val_2323_ = leanh::lean_ctor_get(v___x_2320_, 0);
                    leanh::lean_inc(v_val_2323_);
                    leanh::lean_dec_ref_known(v___x_2320_, 1);
                    v___y_2314_ = v_val_2323_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6___boxed(
    mut v_minIndex_2352_: *mut leanh::LeanObject,
    mut v___x_2353_: *mut leanh::LeanObject,
    mut v___x_2354_: *mut leanh::LeanObject,
    mut v_start_2355_: *mut leanh::LeanObject,
    mut v_xs_2356_: *mut leanh::LeanObject,
    mut v___x_2357_: *mut leanh::LeanObject,
    mut v_e_2358_: *mut leanh::LeanObject,
    mut v_offset_2359_: *mut leanh::LeanObject,
    mut v_a_2360_: *mut leanh::LeanObject,
    mut v_a_2361_: *mut leanh::LeanObject,
    mut v_a_2362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2363_: u8 = 0;
    let mut v_res_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2363_ = (leanh::lean_unbox(v_a_2361_) as u8);
    v_res_2364_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2352_, v___x_2353_, v___x_2354_, v_start_2355_, v_xs_2356_, v___x_2357_, v_e_2358_, v_offset_2359_, v_a_2360_, v_a_boxed_2363_, v_a_2362_);
    leanh::lean_dec_ref(v___x_2357_);
    leanh::lean_dec_ref(v_xs_2356_);
    leanh::lean_dec(v_start_2355_);
    leanh::lean_dec(v___x_2354_);
    leanh::lean_dec(v_minIndex_2352_);
    return v_res_2364_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(
    mut v_minIndex_2365_: *mut leanh::LeanObject,
    mut v___x_2366_: *mut leanh::LeanObject,
    mut v___x_2367_: *mut leanh::LeanObject,
    mut v_start_2368_: *mut leanh::LeanObject,
    mut v_xs_2369_: *mut leanh::LeanObject,
    mut v___x_2370_: *mut leanh::LeanObject,
    mut v_e_2371_: *mut leanh::LeanObject,
    mut v_offset_2372_: *mut leanh::LeanObject,
    mut v_a_2373_: *mut leanh::LeanObject,
    mut v_a_2374_: *mut leanh::LeanObject,
    mut v_a_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2376_: u8 = 0;
    let mut v_res_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2376_ = (leanh::lean_unbox(v_a_2374_) as u8);
    v_res_2377_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_minIndex_2365_, v___x_2366_, v___x_2367_, v_start_2368_, v_xs_2369_, v___x_2370_, v_e_2371_, v_offset_2372_, v_a_2373_, v_a_boxed_2376_, v_a_2375_);
    leanh::lean_dec_ref(v___x_2370_);
    leanh::lean_dec_ref(v_xs_2369_);
    leanh::lean_dec(v_start_2368_);
    leanh::lean_dec(v___x_2367_);
    leanh::lean_dec(v_minIndex_2365_);
    return v_res_2377_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2378_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(
        leanh::lean_box(0),
    );
    return v___x_2378_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVarsRange___redArg(
    mut v_e_2379_: *mut leanh::LeanObject,
    mut v_start_2380_: *mut leanh::LeanObject,
    mut v_xs_2381_: *mut leanh::LeanObject,
    mut v_a_2382_: *mut leanh::LeanObject,
    mut v_a_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2402_: u8 = 0;
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2405_: u8 = 0;
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2424_: u8 = 0;
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2433_: u8 = 0;
    let mut v_unused_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2437_: u8 = 0;
    let mut v___y_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxIndex_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: u8 = 0;
    let mut v___y_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minIndex_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2385_ = l_Lean_Expr_hasFVar(v_e_2379_);
                if v___x_2385_ == 0 {
                    v___x_2386_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2386_, 0, v_e_2379_);
                    return v___x_2386_;
                } else {
                    v___x_2387_ = lean_array_get_size(v_xs_2381_);
                    v___x_2388_ = lean_nat_dec_lt(v_start_2380_, v___x_2387_);
                    if v___x_2388_ == 0 {
                        v___x_2389_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2389_, 0, v_e_2379_);
                        return v___x_2389_;
                    } else {
                        v___x_2390_ = lean_st_ref_get(v_a_2382_);
                        v___x_2391_ = lean_st_ref_take(v_a_2382_);
                        v_share_2392_ = leanh::lean_ctor_get(v___x_2391_, 0);
                        v_maxFVar_2393_ = leanh::lean_ctor_get(v___x_2391_, 1);
                        v_proofInstInfo_2394_ = leanh::lean_ctor_get(v___x_2391_, 2);
                        v_inferType_2395_ = leanh::lean_ctor_get(v___x_2391_, 3);
                        v_getLevel_2396_ = leanh::lean_ctor_get(v___x_2391_, 4);
                        v_congrInfo_2397_ = leanh::lean_ctor_get(v___x_2391_, 5);
                        v_defEqI_2398_ = leanh::lean_ctor_get(v___x_2391_, 6);
                        v_extensions_2399_ = leanh::lean_ctor_get(v___x_2391_, 7);
                        v_issues_2400_ = leanh::lean_ctor_get(v___x_2391_, 8);
                        v_canon_2401_ = leanh::lean_ctor_get(v___x_2391_, 9);
                        v_debug_2402_ = leanh::lean_ctor_get_uint8(
                            v___x_2391_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                        );
                        v_isSharedCheck_2486_ =
                            (!leanh::lean_is_exclusive(v___x_2391_)) as u8;
                        if v_isSharedCheck_2486_ == 0 {
                            v___x_2404_ = v___x_2391_;
                            v_isShared_2405_ = v_isSharedCheck_2486_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_canon_2401_);
                            leanh::lean_inc(v_issues_2400_);
                            leanh::lean_inc(v_extensions_2399_);
                            leanh::lean_inc(v_defEqI_2398_);
                            leanh::lean_inc(v_congrInfo_2397_);
                            leanh::lean_inc(v_getLevel_2396_);
                            leanh::lean_inc(v_inferType_2395_);
                            leanh::lean_inc(v_proofInstInfo_2394_);
                            leanh::lean_inc(v_maxFVar_2393_);
                            leanh::lean_inc(v_share_2392_);
                            leanh::lean_dec(v___x_2391_);
                            v___x_2404_ = leanh::lean_box(0);
                            v_isShared_2405_ = v_isSharedCheck_2486_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2406_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0_once
                    ),
                    _init_l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0,
                );
                if v_isShared_2405_ == 0 {
                    leanh::lean_ctor_set(v___x_2404_, 0, v___x_2406_);
                    v___x_2408_ = v___x_2404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2485_ = leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2406_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_maxFVar_2393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_proofInstInfo_2394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_inferType_2395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 4, v_getLevel_2396_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 5, v_congrInfo_2397_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 6, v_defEqI_2398_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 7, v_extensions_2399_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 8, v_issues_2400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 9, v_canon_2401_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2485_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                        v_debug_2402_,
                    );
                    v___x_2408_ = v_reuseFailAlloc_2485_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2409_ = lean_st_ref_set(v_a_2382_, v___x_2408_);
                v___x_2410_ = lean_st_ref_get(v_a_2382_);
                v_lctx_2435_ = leanh::lean_ctor_get(v_a_2383_, 2);
                v_maxFVar_2436_ = leanh::lean_ctor_get(v___x_2390_, 1);
                leanh::lean_inc_ref(v_maxFVar_2436_);
                leanh::lean_dec(v___x_2390_);
                v_debug_2437_ = leanh::lean_ctor_get_uint8(
                    v___x_2410_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                leanh::lean_dec(v___x_2410_);
                v___x_2479_ = lean_array_fget_borrowed(v_xs_2381_, v_start_2380_);
                v___x_2480_ = l_Lean_Expr_fvarId_x21(v___x_2479_);
                leanh::lean_inc_ref(v_lctx_2435_);
                v___x_2481_ = lean_local_ctx_find(v_lctx_2435_, v___x_2480_);
                if leanh::lean_obj_tag(v___x_2481_) == 0 {
                    v___x_2482_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                    v___x_2483_ =
                        l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_2482_);
                    v___y_2463_ = v___x_2483_;
                    state = 9;
                    continue;
                } else {
                    v_val_2484_ = leanh::lean_ctor_get(v___x_2481_, 0);
                    leanh::lean_inc(v_val_2484_);
                    leanh::lean_dec_ref_known(v___x_2481_, 1);
                    v___y_2463_ = v_val_2484_;
                    state = 9;
                    continue;
                }
            }
            3 => {
                v___x_2414_ = lean_st_ref_take(v_a_2382_);
                v_maxFVar_2415_ = leanh::lean_ctor_get(v___x_2414_, 1);
                v_proofInstInfo_2416_ = leanh::lean_ctor_get(v___x_2414_, 2);
                v_inferType_2417_ = leanh::lean_ctor_get(v___x_2414_, 3);
                v_getLevel_2418_ = leanh::lean_ctor_get(v___x_2414_, 4);
                v_congrInfo_2419_ = leanh::lean_ctor_get(v___x_2414_, 5);
                v_defEqI_2420_ = leanh::lean_ctor_get(v___x_2414_, 6);
                v_extensions_2421_ = leanh::lean_ctor_get(v___x_2414_, 7);
                v_issues_2422_ = leanh::lean_ctor_get(v___x_2414_, 8);
                v_canon_2423_ = leanh::lean_ctor_get(v___x_2414_, 9);
                v_debug_2424_ = leanh::lean_ctor_get_uint8(
                    v___x_2414_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2433_ = (!leanh::lean_is_exclusive(v___x_2414_)) as u8;
                if v_isSharedCheck_2433_ == 0 {
                    v_unused_2434_ = leanh::lean_ctor_get(v___x_2414_, 0);
                    leanh::lean_dec(v_unused_2434_);
                    v___x_2426_ = v___x_2414_;
                    v_isShared_2427_ = v_isSharedCheck_2433_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_canon_2423_);
                    leanh::lean_inc(v_issues_2422_);
                    leanh::lean_inc(v_extensions_2421_);
                    leanh::lean_inc(v_defEqI_2420_);
                    leanh::lean_inc(v_congrInfo_2419_);
                    leanh::lean_inc(v_getLevel_2418_);
                    leanh::lean_inc(v_inferType_2417_);
                    leanh::lean_inc(v_proofInstInfo_2416_);
                    leanh::lean_inc(v_maxFVar_2415_);
                    leanh::lean_dec(v___x_2414_);
                    v___x_2426_ = leanh::lean_box(0);
                    v_isShared_2427_ = v_isSharedCheck_2433_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2427_ == 0 {
                    leanh::lean_ctor_set(v___x_2426_, 0, v_snd_2413_);
                    v___x_2429_ = v___x_2426_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2432_ = leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_snd_2413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_maxFVar_2415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_proofInstInfo_2416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_inferType_2417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_getLevel_2418_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 5, v_congrInfo_2419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 6, v_defEqI_2420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 7, v_extensions_2421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 8, v_issues_2422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 9, v_canon_2423_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2432_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                        v_debug_2424_,
                    );
                    v___x_2429_ = v_reuseFailAlloc_2432_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2430_ = lean_st_ref_set(v_a_2382_, v___x_2429_);
                v___x_2431_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2431_, 0, v_fst_2412_);
                return v___x_2431_;
            }
            6 => match leanh::lean_obj_tag(v_e_2379_) {
                9 => {
                    leanh::lean_dec(v___y_2440_);
                    leanh::lean_dec(v___y_2439_);
                    leanh::lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                2 => {
                    leanh::lean_dec(v___y_2440_);
                    leanh::lean_dec(v___y_2439_);
                    leanh::lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                0 => {
                    leanh::lean_dec(v___y_2440_);
                    leanh::lean_dec(v___y_2439_);
                    leanh::lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                1 => {
                    leanh::lean_dec(v___y_2440_);
                    leanh::lean_dec(v___y_2439_);
                    leanh::lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                4 => {
                    leanh::lean_dec(v___y_2440_);
                    leanh::lean_dec(v___y_2439_);
                    leanh::lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                3 => {
                    leanh::lean_dec(v___y_2440_);
                    leanh::lean_dec(v___y_2439_);
                    leanh::lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                _ => {
                    v___x_2442_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
                    leanh::lean_inc(v___y_2439_);
                    v___x_2443_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2443_, 0, v___y_2439_);
                    leanh::lean_ctor_set(v___x_2443_, 1, v___x_2442_);
                    leanh::lean_inc_ref(v_lctx_2435_);
                    v___x_2444_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___y_2440_, v_lctx_2435_, v___x_2387_, v_start_2380_, v_xs_2381_, v_maxFVar_2436_, v_e_2379_, v___y_2439_, v___x_2443_, v_debug_2437_, v_snd_2441_);
                    leanh::lean_dec_ref(v_maxFVar_2436_);
                    leanh::lean_dec(v___y_2440_);
                    v_fst_2445_ = leanh::lean_ctor_get(v___x_2444_, 0);
                    leanh::lean_inc(v_fst_2445_);
                    v_snd_2446_ = leanh::lean_ctor_get(v___x_2444_, 1);
                    leanh::lean_inc(v_snd_2446_);
                    leanh::lean_dec_ref(v___x_2444_);
                    v_fst_2447_ = leanh::lean_ctor_get(v_fst_2445_, 0);
                    leanh::lean_inc(v_fst_2447_);
                    leanh::lean_dec(v_fst_2445_);
                    v_fst_2412_ = v_fst_2447_;
                    v_snd_2413_ = v_snd_2446_;
                    state = 3;
                    continue;
                }
            },
            7 => {
                v_maxIndex_2452_ = l_Lean_LocalDecl_index(v___y_2451_);
                leanh::lean_dec_ref(v___y_2451_);
                v___x_2453_ = lean_nat_dec_lt(v_maxIndex_2452_, v___y_2450_);
                leanh::lean_dec(v_maxIndex_2452_);
                if v___x_2453_ == 0 {
                    v___y_2439_ = v___y_2449_;
                    v___y_2440_ = v___y_2450_;
                    v_snd_2441_ = v_share_2392_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v___y_2450_);
                    leanh::lean_dec(v___y_2449_);
                    leanh::lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_share_2392_;
                    state = 3;
                    continue;
                }
            }
            8 => {
                leanh::lean_inc_ref(v_lctx_2435_);
                v___x_2458_ = lean_local_ctx_find(v_lctx_2435_, v___y_2457_);
                if leanh::lean_obj_tag(v___x_2458_) == 0 {
                    v___x_2459_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                    v___x_2460_ =
                        l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_2459_);
                    v___y_2449_ = v___y_2455_;
                    v___y_2450_ = v___y_2456_;
                    v___y_2451_ = v___x_2460_;
                    state = 7;
                    continue;
                } else {
                    v_val_2461_ = leanh::lean_ctor_get(v___x_2458_, 0);
                    leanh::lean_inc(v_val_2461_);
                    leanh::lean_dec_ref_known(v___x_2458_, 1);
                    v___y_2449_ = v___y_2455_;
                    v___y_2450_ = v___y_2456_;
                    v___y_2451_ = v_val_2461_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v___x_2464_ = leanh::lean_unsigned_to_nat(0);
                match leanh::lean_obj_tag(v_e_2379_) {
                    1 => {
                        leanh::lean_dec_ref(v___y_2463_);
                        leanh::lean_dec_ref(v_maxFVar_2436_);
                        v_fvarId_2465_ = leanh::lean_ctor_get(v_e_2379_, 0);
                        v___x_2466_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2467_ = lean_nat_sub(v___x_2387_, v___x_2466_);
                        v___x_2468_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_2380_, v_xs_2381_, v_fvarId_2465_, v___x_2464_, v___x_2467_);
                        if leanh::lean_obj_tag(v___x_2468_) == 1 {
                            leanh::lean_dec_ref_known(v_e_2379_, 1);
                            v_val_2469_ = leanh::lean_ctor_get(v___x_2468_, 0);
                            leanh::lean_inc(v_val_2469_);
                            leanh::lean_dec_ref_known(v___x_2468_, 1);
                            v___x_2470_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_val_2469_, v_share_2392_);
                            v_fst_2471_ = leanh::lean_ctor_get(v___x_2470_, 0);
                            leanh::lean_inc(v_fst_2471_);
                            v_snd_2472_ = leanh::lean_ctor_get(v___x_2470_, 1);
                            leanh::lean_inc(v_snd_2472_);
                            leanh::lean_dec_ref(v___x_2470_);
                            v_fst_2412_ = v_fst_2471_;
                            v_snd_2413_ = v_snd_2472_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2468_);
                            v_fst_2412_ = v_e_2379_;
                            v_snd_2413_ = v_share_2392_;
                            state = 3;
                            continue;
                        }
                    }
                    9 => {
                        leanh::lean_dec_ref(v___y_2463_);
                        leanh::lean_dec_ref(v_maxFVar_2436_);
                        v_fst_2412_ = v_e_2379_;
                        v_snd_2413_ = v_share_2392_;
                        state = 3;
                        continue;
                    }
                    2 => {
                        leanh::lean_dec_ref(v___y_2463_);
                        leanh::lean_dec_ref(v_maxFVar_2436_);
                        v_fst_2412_ = v_e_2379_;
                        v_snd_2413_ = v_share_2392_;
                        state = 3;
                        continue;
                    }
                    0 => {
                        leanh::lean_dec_ref(v___y_2463_);
                        leanh::lean_dec_ref(v_maxFVar_2436_);
                        v_fst_2412_ = v_e_2379_;
                        v_snd_2413_ = v_share_2392_;
                        state = 3;
                        continue;
                    }
                    4 => {
                        leanh::lean_dec_ref(v___y_2463_);
                        leanh::lean_dec_ref(v_maxFVar_2436_);
                        v_fst_2412_ = v_e_2379_;
                        v_snd_2413_ = v_share_2392_;
                        state = 3;
                        continue;
                    }
                    3 => {
                        leanh::lean_dec_ref(v___y_2463_);
                        leanh::lean_dec_ref(v_maxFVar_2436_);
                        v_fst_2412_ = v_e_2379_;
                        v_snd_2413_ = v_share_2392_;
                        state = 3;
                        continue;
                    }
                    _ => {
                        if v___x_2385_ == 0 {
                            leanh::lean_dec_ref(v___y_2463_);
                            leanh::lean_dec_ref(v_maxFVar_2436_);
                            v_fst_2412_ = v_e_2379_;
                            v_snd_2413_ = v_share_2392_;
                            state = 3;
                            continue;
                        } else {
                            v_minIndex_2473_ = l_Lean_LocalDecl_index(v___y_2463_);
                            leanh::lean_dec_ref(v___y_2463_);
                            v___x_2474_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_maxFVar_2436_, v_e_2379_);
                            if leanh::lean_obj_tag(v___x_2474_) == 1 {
                                v_val_2475_ = leanh::lean_ctor_get(v___x_2474_, 0);
                                leanh::lean_inc(v_val_2475_);
                                leanh::lean_dec_ref_known(v___x_2474_, 1);
                                if leanh::lean_obj_tag(v_val_2475_) == 0 {
                                    v___x_2476_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                                    v___x_2477_ =
                                        l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(
                                            v___x_2476_,
                                        );
                                    v___y_2455_ = v___x_2464_;
                                    v___y_2456_ = v_minIndex_2473_;
                                    v___y_2457_ = v___x_2477_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_val_2478_ = leanh::lean_ctor_get(v_val_2475_, 0);
                                    leanh::lean_inc(v_val_2478_);
                                    leanh::lean_dec_ref_known(v_val_2475_, 1);
                                    v___y_2455_ = v___x_2464_;
                                    v___y_2456_ = v_minIndex_2473_;
                                    v___y_2457_ = v_val_2478_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_2474_);
                                v___y_2439_ = v___x_2464_;
                                v___y_2440_ = v_minIndex_2473_;
                                v_snd_2441_ = v_share_2392_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVarsRange___redArg___boxed(
    mut v_e_2487_: *mut leanh::LeanObject,
    mut v_start_2488_: *mut leanh::LeanObject,
    mut v_xs_2489_: *mut leanh::LeanObject,
    mut v_a_2490_: *mut leanh::LeanObject,
    mut v_a_2491_: *mut leanh::LeanObject,
    mut v_a_2492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2493_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
        v_e_2487_,
        v_start_2488_,
        v_xs_2489_,
        v_a_2490_,
        v_a_2491_,
    );
    leanh::lean_dec_ref(v_a_2491_);
    leanh::lean_dec(v_a_2490_);
    leanh::lean_dec_ref(v_xs_2489_);
    leanh::lean_dec(v_start_2488_);
    return v_res_2493_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVarsRange(
    mut v_e_2494_: *mut leanh::LeanObject,
    mut v_start_2495_: *mut leanh::LeanObject,
    mut v_xs_2496_: *mut leanh::LeanObject,
    mut v_a_2497_: *mut leanh::LeanObject,
    mut v_a_2498_: *mut leanh::LeanObject,
    mut v_a_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
    mut v_a_2501_: *mut leanh::LeanObject,
    mut v_a_2502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2504_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
        v_e_2494_,
        v_start_2495_,
        v_xs_2496_,
        v_a_2498_,
        v_a_2499_,
    );
    return v___x_2504_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVarsRange___boxed(
    mut v_e_2505_: *mut leanh::LeanObject,
    mut v_start_2506_: *mut leanh::LeanObject,
    mut v_xs_2507_: *mut leanh::LeanObject,
    mut v_a_2508_: *mut leanh::LeanObject,
    mut v_a_2509_: *mut leanh::LeanObject,
    mut v_a_2510_: *mut leanh::LeanObject,
    mut v_a_2511_: *mut leanh::LeanObject,
    mut v_a_2512_: *mut leanh::LeanObject,
    mut v_a_2513_: *mut leanh::LeanObject,
    mut v_a_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Lean_Meta_Sym_abstractFVarsRange(
        v_e_2505_,
        v_start_2506_,
        v_xs_2507_,
        v_a_2508_,
        v_a_2509_,
        v_a_2510_,
        v_a_2511_,
        v_a_2512_,
        v_a_2513_,
    );
    leanh::lean_dec(v_a_2513_);
    leanh::lean_dec_ref(v_a_2512_);
    leanh::lean_dec(v_a_2511_);
    leanh::lean_dec_ref(v_a_2510_);
    leanh::lean_dec(v_a_2509_);
    leanh::lean_dec_ref(v_a_2508_);
    leanh::lean_dec_ref(v_xs_2507_);
    leanh::lean_dec(v_start_2506_);
    return v_res_2515_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(
    mut v_00_u03b2_2516_: *mut leanh::LeanObject,
    mut v_x_2517_: *mut leanh::LeanObject,
    mut v_x_2518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2519_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_x_2517_, v_x_2518_);
    return v___x_2519_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___boxed(
    mut v_00_u03b2_2520_: *mut leanh::LeanObject,
    mut v_x_2521_: *mut leanh::LeanObject,
    mut v_x_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2523_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(
            v_00_u03b2_2520_,
            v_x_2521_,
            v_x_2522_,
        );
    leanh::lean_dec_ref(v_x_2522_);
    leanh::lean_dec_ref(v_x_2521_);
    return v_res_2523_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(
    mut v_00_u03b2_2524_: *mut leanh::LeanObject,
    mut v_x_2525_: *mut leanh::LeanObject,
    mut v_x_2526_: usize,
    mut v_x_2527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2528_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_2525_, v_x_2526_, v_x_2527_);
    return v___x_2528_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___boxed(
    mut v_00_u03b2_2529_: *mut leanh::LeanObject,
    mut v_x_2530_: *mut leanh::LeanObject,
    mut v_x_2531_: *mut leanh::LeanObject,
    mut v_x_2532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26629__boxed_2533_: usize = 0;
    let mut v_res_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26629__boxed_2533_ = leanh::lean_unbox_usize(v_x_2531_);
    leanh::lean_dec(v_x_2531_);
    v_res_2534_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(v_00_u03b2_2529_, v_x_2530_, v_x_26629__boxed_2533_, v_x_2532_);
    leanh::lean_dec_ref(v_x_2532_);
    leanh::lean_dec_ref(v_x_2530_);
    return v_res_2534_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(
    mut v_00_u03b2_2535_: *mut leanh::LeanObject,
    mut v_keys_2536_: *mut leanh::LeanObject,
    mut v_vals_2537_: *mut leanh::LeanObject,
    mut v_heq_2538_: *mut leanh::LeanObject,
    mut v_i_2539_: *mut leanh::LeanObject,
    mut v_k_2540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2541_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_keys_2536_, v_vals_2537_, v_i_2539_, v_k_2540_);
    return v___x_2541_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___boxed(
    mut v_00_u03b2_2542_: *mut leanh::LeanObject,
    mut v_keys_2543_: *mut leanh::LeanObject,
    mut v_vals_2544_: *mut leanh::LeanObject,
    mut v_heq_2545_: *mut leanh::LeanObject,
    mut v_i_2546_: *mut leanh::LeanObject,
    mut v_k_2547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2548_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(v_00_u03b2_2542_, v_keys_2543_, v_vals_2544_, v_heq_2545_, v_i_2546_, v_k_2547_);
    leanh::lean_dec_ref(v_k_2547_);
    leanh::lean_dec_ref(v_vals_2544_);
    leanh::lean_dec_ref(v_keys_2543_);
    return v_res_2548_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(
    mut v_00_u03b2_2549_: *mut leanh::LeanObject,
    mut v_m_2550_: *mut leanh::LeanObject,
    mut v_a_2551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2552_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_m_2550_, v_a_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___boxed(
    mut v_00_u03b2_2553_: *mut leanh::LeanObject,
    mut v_m_2554_: *mut leanh::LeanObject,
    mut v_a_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(v_00_u03b2_2553_, v_m_2554_, v_a_2555_);
    leanh::lean_dec_ref(v_a_2555_);
    leanh::lean_dec_ref(v_m_2554_);
    return v_res_2556_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(
    mut v_00_u03b2_2557_: *mut leanh::LeanObject,
    mut v_a_2558_: *mut leanh::LeanObject,
    mut v_x_2559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2560_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(v_a_2558_, v_x_2559_);
    return v___x_2560_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___boxed(
    mut v_00_u03b2_2561_: *mut leanh::LeanObject,
    mut v_a_2562_: *mut leanh::LeanObject,
    mut v_x_2563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2564_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(v_00_u03b2_2561_, v_a_2562_, v_x_2563_);
    leanh::lean_dec(v_x_2563_);
    leanh::lean_dec_ref(v_a_2562_);
    return v_res_2564_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVars___redArg(
    mut v_e_2565_: *mut leanh::LeanObject,
    mut v_xs_2566_: *mut leanh::LeanObject,
    mut v_a_2567_: *mut leanh::LeanObject,
    mut v_a_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2570_ = leanh::lean_unsigned_to_nat(0);
    v___x_2571_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
        v_e_2565_,
        v___x_2570_,
        v_xs_2566_,
        v_a_2567_,
        v_a_2568_,
    );
    return v___x_2571_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVars___redArg___boxed(
    mut v_e_2572_: *mut leanh::LeanObject,
    mut v_xs_2573_: *mut leanh::LeanObject,
    mut v_a_2574_: *mut leanh::LeanObject,
    mut v_a_2575_: *mut leanh::LeanObject,
    mut v_a_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2577_ =
        l_Lean_Meta_Sym_abstractFVars___redArg(v_e_2572_, v_xs_2573_, v_a_2574_, v_a_2575_);
    leanh::lean_dec_ref(v_a_2575_);
    leanh::lean_dec(v_a_2574_);
    leanh::lean_dec_ref(v_xs_2573_);
    return v_res_2577_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVars(
    mut v_e_2578_: *mut leanh::LeanObject,
    mut v_xs_2579_: *mut leanh::LeanObject,
    mut v_a_2580_: *mut leanh::LeanObject,
    mut v_a_2581_: *mut leanh::LeanObject,
    mut v_a_2582_: *mut leanh::LeanObject,
    mut v_a_2583_: *mut leanh::LeanObject,
    mut v_a_2584_: *mut leanh::LeanObject,
    mut v_a_2585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2587_ = leanh::lean_unsigned_to_nat(0);
    v___x_2588_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
        v_e_2578_,
        v___x_2587_,
        v_xs_2579_,
        v_a_2581_,
        v_a_2582_,
    );
    return v___x_2588_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVars___boxed(
    mut v_e_2589_: *mut leanh::LeanObject,
    mut v_xs_2590_: *mut leanh::LeanObject,
    mut v_a_2591_: *mut leanh::LeanObject,
    mut v_a_2592_: *mut leanh::LeanObject,
    mut v_a_2593_: *mut leanh::LeanObject,
    mut v_a_2594_: *mut leanh::LeanObject,
    mut v_a_2595_: *mut leanh::LeanObject,
    mut v_a_2596_: *mut leanh::LeanObject,
    mut v_a_2597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2598_ = l_Lean_Meta_Sym_abstractFVars(
        v_e_2589_, v_xs_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_,
    );
    leanh::lean_dec(v_a_2596_);
    leanh::lean_dec_ref(v_a_2595_);
    leanh::lean_dec(v_a_2594_);
    leanh::lean_dec_ref(v_a_2593_);
    leanh::lean_dec(v_a_2592_);
    leanh::lean_dec_ref(v_a_2591_);
    leanh::lean_dec_ref(v_xs_2590_);
    return v_res_2598_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(
    mut v_x_2599_: *mut leanh::LeanObject,
    mut v_bi_2600_: u8,
    mut v_t_2601_: *mut leanh::LeanObject,
    mut v_b_2602_: *mut leanh::LeanObject,
    mut v___y_2603_: *mut leanh::LeanObject,
    mut v___y_2604_: *mut leanh::LeanObject,
    mut v___y_2605_: *mut leanh::LeanObject,
    mut v___y_2606_: *mut leanh::LeanObject,
    mut v___y_2607_: *mut leanh::LeanObject,
    mut v___y_2608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2615_: u8 = 0;
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v_a_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2614_ = lean_st_ref_get(v___y_2604_);
                v_debug_2615_ = leanh::lean_ctor_get_uint8(
                    v___x_2614_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                leanh::lean_dec(v___x_2614_);
                if v_debug_2615_ == 0 {
                    v___y_2611_ = v___y_2604_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_t_2601_);
                    v___x_2616_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_t_2601_,
                        v___y_2603_,
                        v___y_2604_,
                        v___y_2605_,
                        v___y_2606_,
                        v___y_2607_,
                        v___y_2608_,
                    );
                    if leanh::lean_obj_tag(v___x_2616_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2616_, 1);
                        leanh::lean_inc_ref(v_b_2602_);
                        v___x_2617_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_b_2602_,
                            v___y_2603_,
                            v___y_2604_,
                            v___y_2605_,
                            v___y_2606_,
                            v___y_2607_,
                            v___y_2608_,
                        );
                        if leanh::lean_obj_tag(v___x_2617_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2617_, 1);
                            v___y_2611_ = v___y_2604_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_2602_);
                            leanh::lean_dec_ref(v_t_2601_);
                            leanh::lean_dec(v_x_2599_);
                            v_a_2618_ = leanh::lean_ctor_get(v___x_2617_, 0);
                            v_isSharedCheck_2625_ =
                                (!leanh::lean_is_exclusive(v___x_2617_)) as u8;
                            if v_isSharedCheck_2625_ == 0 {
                                v___x_2620_ = v___x_2617_;
                                v_isShared_2621_ = v_isSharedCheck_2625_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2618_);
                                leanh::lean_dec(v___x_2617_);
                                v___x_2620_ = leanh::lean_box(0);
                                v_isShared_2621_ = v_isSharedCheck_2625_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_2602_);
                        leanh::lean_dec_ref(v_t_2601_);
                        leanh::lean_dec(v_x_2599_);
                        v_a_2626_ = leanh::lean_ctor_get(v___x_2616_, 0);
                        v_isSharedCheck_2633_ =
                            (!leanh::lean_is_exclusive(v___x_2616_)) as u8;
                        if v_isSharedCheck_2633_ == 0 {
                            v___x_2628_ = v___x_2616_;
                            v_isShared_2629_ = v_isSharedCheck_2633_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2626_);
                            leanh::lean_dec(v___x_2616_);
                            v___x_2628_ = leanh::lean_box(0);
                            v_isShared_2629_ = v_isSharedCheck_2633_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2612_ =
                    l_Lean_Expr_lam___override(v_x_2599_, v_t_2601_, v_b_2602_, v_bi_2600_);
                v___x_2613_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2612_, v___y_2611_);
                return v___x_2613_;
            }
            2 => {
                if v_isShared_2621_ == 0 {
                    v___x_2623_ = v___x_2620_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2624_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
                    v___x_2623_ = v_reuseFailAlloc_2624_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2623_;
            }
            4 => {
                if v_isShared_2629_ == 0 {
                    v___x_2631_ = v___x_2628_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
                    v___x_2631_ = v_reuseFailAlloc_2632_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0___boxed(
    mut v_x_2634_: *mut leanh::LeanObject,
    mut v_bi_2635_: *mut leanh::LeanObject,
    mut v_t_2636_: *mut leanh::LeanObject,
    mut v_b_2637_: *mut leanh::LeanObject,
    mut v___y_2638_: *mut leanh::LeanObject,
    mut v___y_2639_: *mut leanh::LeanObject,
    mut v___y_2640_: *mut leanh::LeanObject,
    mut v___y_2641_: *mut leanh::LeanObject,
    mut v___y_2642_: *mut leanh::LeanObject,
    mut v___y_2643_: *mut leanh::LeanObject,
    mut v___y_2644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_2645_: u8 = 0;
    let mut v_res_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2645_ = (leanh::lean_unbox(v_bi_2635_) as u8);
    v_res_2646_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(
        v_x_2634_,
        v_bi_boxed_2645_,
        v_t_2636_,
        v_b_2637_,
        v___y_2638_,
        v___y_2639_,
        v___y_2640_,
        v___y_2641_,
        v___y_2642_,
        v___y_2643_,
    );
    leanh::lean_dec(v___y_2643_);
    leanh::lean_dec_ref(v___y_2642_);
    leanh::lean_dec(v___y_2641_);
    leanh::lean_dec_ref(v___y_2640_);
    leanh::lean_dec(v___y_2639_);
    leanh::lean_dec_ref(v___y_2638_);
    return v_res_2646_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(
    mut v_xs_2647_: *mut leanh::LeanObject,
    mut v_i_2648_: *mut leanh::LeanObject,
    mut v_a_2649_: *mut leanh::LeanObject,
    mut v___y_2650_: *mut leanh::LeanObject,
    mut v___y_2651_: *mut leanh::LeanObject,
    mut v___y_2652_: *mut leanh::LeanObject,
    mut v___y_2653_: *mut leanh::LeanObject,
    mut v___y_2654_: *mut leanh::LeanObject,
    mut v___y_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2658_: u8 = 0;
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: u8 = 0;
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2657_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2658_ = lean_nat_dec_eq(v_i_2648_, v_zero_2657_);
                if v_isZero_2658_ == 1 {
                    leanh::lean_dec(v_i_2648_);
                    v___x_2659_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2659_, 0, v_a_2649_);
                    return v___x_2659_;
                } else {
                    v_one_2660_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2661_ = lean_nat_sub(v_i_2648_, v_one_2660_);
                    leanh::lean_dec(v_i_2648_);
                    v___x_2666_ = lean_array_fget_borrowed(v_xs_2647_, v_n_2661_);
                    v___x_2667_ = l_Lean_Expr_fvarId_x21(v___x_2666_);
                    v___x_2668_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_2667_,
                        v___y_2652_,
                        v___y_2654_,
                        v___y_2655_,
                    );
                    if leanh::lean_obj_tag(v___x_2668_) == 0 {
                        v_a_2669_ = leanh::lean_ctor_get(v___x_2668_, 0);
                        leanh::lean_inc(v_a_2669_);
                        leanh::lean_dec_ref_known(v___x_2668_, 1);
                        v___x_2670_ = l_Lean_LocalDecl_type(v_a_2669_);
                        v___x_2671_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
                            v___x_2670_,
                            v_n_2661_,
                            v_xs_2647_,
                            v___y_2651_,
                            v___y_2652_,
                        );
                        v_a_2672_ = leanh::lean_ctor_get(v___x_2671_, 0);
                        leanh::lean_inc(v_a_2672_);
                        leanh::lean_dec_ref(v___x_2671_);
                        v___x_2673_ = l_Lean_LocalDecl_userName(v_a_2669_);
                        v___x_2674_ = l_Lean_LocalDecl_binderInfo(v_a_2669_);
                        leanh::lean_dec(v_a_2669_);
                        v___x_2675_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_2673_, v___x_2674_, v_a_2672_, v_a_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
                        v___y_2663_ = v___x_2675_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_n_2661_);
                        leanh::lean_dec_ref(v_a_2649_);
                        v_a_2676_ = leanh::lean_ctor_get(v___x_2668_, 0);
                        v_isSharedCheck_2683_ =
                            (!leanh::lean_is_exclusive(v___x_2668_)) as u8;
                        if v_isSharedCheck_2683_ == 0 {
                            v___x_2678_ = v___x_2668_;
                            v_isShared_2679_ = v_isSharedCheck_2683_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2676_);
                            leanh::lean_dec(v___x_2668_);
                            v___x_2678_ = leanh::lean_box(0);
                            v_isShared_2679_ = v_isSharedCheck_2683_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_2663_) == 0 {
                    v_a_2664_ = leanh::lean_ctor_get(v___y_2663_, 0);
                    leanh::lean_inc(v_a_2664_);
                    leanh::lean_dec_ref_known(v___y_2663_, 1);
                    v_i_2648_ = v_n_2661_;
                    v_a_2649_ = v_a_2664_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_n_2661_);
                    return v___y_2663_;
                }
            }
            2 => {
                if v_isShared_2679_ == 0 {
                    v___x_2681_ = v___x_2678_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
                    v___x_2681_ = v_reuseFailAlloc_2682_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg___boxed(
    mut v_xs_2684_: *mut leanh::LeanObject,
    mut v_i_2685_: *mut leanh::LeanObject,
    mut v_a_2686_: *mut leanh::LeanObject,
    mut v___y_2687_: *mut leanh::LeanObject,
    mut v___y_2688_: *mut leanh::LeanObject,
    mut v___y_2689_: *mut leanh::LeanObject,
    mut v___y_2690_: *mut leanh::LeanObject,
    mut v___y_2691_: *mut leanh::LeanObject,
    mut v___y_2692_: *mut leanh::LeanObject,
    mut v___y_2693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2694_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2684_, v_i_2685_, v_a_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
    leanh::lean_dec(v___y_2692_);
    leanh::lean_dec_ref(v___y_2691_);
    leanh::lean_dec(v___y_2690_);
    leanh::lean_dec_ref(v___y_2689_);
    leanh::lean_dec(v___y_2688_);
    leanh::lean_dec_ref(v___y_2687_);
    leanh::lean_dec_ref(v_xs_2684_);
    return v_res_2694_;
}
pub unsafe fn l_Lean_Meta_Sym_mkLambdaFVarsS(
    mut v_xs_2695_: *mut leanh::LeanObject,
    mut v_e_2696_: *mut leanh::LeanObject,
    mut v_a_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: *mut leanh::LeanObject,
    mut v_a_2699_: *mut leanh::LeanObject,
    mut v_a_2700_: *mut leanh::LeanObject,
    mut v_a_2701_: *mut leanh::LeanObject,
    mut v_a_2702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2704_ = leanh::lean_unsigned_to_nat(0);
    v___x_2705_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
        v_e_2696_,
        v___x_2704_,
        v_xs_2695_,
        v_a_2698_,
        v_a_2699_,
    );
    v_a_2706_ = leanh::lean_ctor_get(v___x_2705_, 0);
    leanh::lean_inc(v_a_2706_);
    leanh::lean_dec_ref(v___x_2705_);
    v___x_2707_ = lean_array_get_size(v_xs_2695_);
    v___x_2708_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2695_, v___x_2707_, v_a_2706_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
    return v___x_2708_;
}
pub unsafe fn l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(
    mut v_xs_2709_: *mut leanh::LeanObject,
    mut v_e_2710_: *mut leanh::LeanObject,
    mut v_a_2711_: *mut leanh::LeanObject,
    mut v_a_2712_: *mut leanh::LeanObject,
    mut v_a_2713_: *mut leanh::LeanObject,
    mut v_a_2714_: *mut leanh::LeanObject,
    mut v_a_2715_: *mut leanh::LeanObject,
    mut v_a_2716_: *mut leanh::LeanObject,
    mut v_a_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Lean_Meta_Sym_mkLambdaFVarsS(
        v_xs_2709_, v_e_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_,
    );
    leanh::lean_dec(v_a_2716_);
    leanh::lean_dec_ref(v_a_2715_);
    leanh::lean_dec(v_a_2714_);
    leanh::lean_dec_ref(v_a_2713_);
    leanh::lean_dec(v_a_2712_);
    leanh::lean_dec_ref(v_a_2711_);
    leanh::lean_dec_ref(v_xs_2709_);
    return v_res_2718_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(
    mut v_xs_2719_: *mut leanh::LeanObject,
    mut v_n_2720_: *mut leanh::LeanObject,
    mut v_i_2721_: *mut leanh::LeanObject,
    mut v_a_2722_: *mut leanh::LeanObject,
    mut v_a_2723_: *mut leanh::LeanObject,
    mut v___y_2724_: *mut leanh::LeanObject,
    mut v___y_2725_: *mut leanh::LeanObject,
    mut v___y_2726_: *mut leanh::LeanObject,
    mut v___y_2727_: *mut leanh::LeanObject,
    mut v___y_2728_: *mut leanh::LeanObject,
    mut v___y_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2731_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2719_, v_i_2721_, v_a_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
    return v___x_2731_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(
    mut v_xs_2732_: *mut leanh::LeanObject,
    mut v_n_2733_: *mut leanh::LeanObject,
    mut v_i_2734_: *mut leanh::LeanObject,
    mut v_a_2735_: *mut leanh::LeanObject,
    mut v_a_2736_: *mut leanh::LeanObject,
    mut v___y_2737_: *mut leanh::LeanObject,
    mut v___y_2738_: *mut leanh::LeanObject,
    mut v___y_2739_: *mut leanh::LeanObject,
    mut v___y_2740_: *mut leanh::LeanObject,
    mut v___y_2741_: *mut leanh::LeanObject,
    mut v___y_2742_: *mut leanh::LeanObject,
    mut v___y_2743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2744_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_2732_, v_n_2733_, v_i_2734_, v_a_2735_, v_a_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
    leanh::lean_dec(v___y_2742_);
    leanh::lean_dec_ref(v___y_2741_);
    leanh::lean_dec(v___y_2740_);
    leanh::lean_dec_ref(v___y_2739_);
    leanh::lean_dec(v___y_2738_);
    leanh::lean_dec_ref(v___y_2737_);
    leanh::lean_dec(v_n_2733_);
    leanh::lean_dec_ref(v_xs_2732_);
    return v_res_2744_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(
    mut v_x_2745_: *mut leanh::LeanObject,
    mut v_bi_2746_: u8,
    mut v_t_2747_: *mut leanh::LeanObject,
    mut v_b_2748_: *mut leanh::LeanObject,
    mut v___y_2749_: *mut leanh::LeanObject,
    mut v___y_2750_: *mut leanh::LeanObject,
    mut v___y_2751_: *mut leanh::LeanObject,
    mut v___y_2752_: *mut leanh::LeanObject,
    mut v___y_2753_: *mut leanh::LeanObject,
    mut v___y_2754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2761_: u8 = 0;
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v_a_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2760_ = lean_st_ref_get(v___y_2750_);
                v_debug_2761_ = leanh::lean_ctor_get_uint8(
                    v___x_2760_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                leanh::lean_dec(v___x_2760_);
                if v_debug_2761_ == 0 {
                    v___y_2757_ = v___y_2750_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_t_2747_);
                    v___x_2762_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_t_2747_,
                        v___y_2749_,
                        v___y_2750_,
                        v___y_2751_,
                        v___y_2752_,
                        v___y_2753_,
                        v___y_2754_,
                    );
                    if leanh::lean_obj_tag(v___x_2762_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2762_, 1);
                        leanh::lean_inc_ref(v_b_2748_);
                        v___x_2763_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_b_2748_,
                            v___y_2749_,
                            v___y_2750_,
                            v___y_2751_,
                            v___y_2752_,
                            v___y_2753_,
                            v___y_2754_,
                        );
                        if leanh::lean_obj_tag(v___x_2763_) == 0 {
                            leanh::lean_dec_ref_known(v___x_2763_, 1);
                            v___y_2757_ = v___y_2750_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_b_2748_);
                            leanh::lean_dec_ref(v_t_2747_);
                            leanh::lean_dec(v_x_2745_);
                            v_a_2764_ = leanh::lean_ctor_get(v___x_2763_, 0);
                            v_isSharedCheck_2771_ =
                                (!leanh::lean_is_exclusive(v___x_2763_)) as u8;
                            if v_isSharedCheck_2771_ == 0 {
                                v___x_2766_ = v___x_2763_;
                                v_isShared_2767_ = v_isSharedCheck_2771_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2764_);
                                leanh::lean_dec(v___x_2763_);
                                v___x_2766_ = leanh::lean_box(0);
                                v_isShared_2767_ = v_isSharedCheck_2771_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_2748_);
                        leanh::lean_dec_ref(v_t_2747_);
                        leanh::lean_dec(v_x_2745_);
                        v_a_2772_ = leanh::lean_ctor_get(v___x_2762_, 0);
                        v_isSharedCheck_2779_ =
                            (!leanh::lean_is_exclusive(v___x_2762_)) as u8;
                        if v_isSharedCheck_2779_ == 0 {
                            v___x_2774_ = v___x_2762_;
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2772_);
                            leanh::lean_dec(v___x_2762_);
                            v___x_2774_ = leanh::lean_box(0);
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2758_ =
                    l_Lean_Expr_forallE___override(v_x_2745_, v_t_2747_, v_b_2748_, v_bi_2746_);
                v___x_2759_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2758_, v___y_2757_);
                return v___x_2759_;
            }
            2 => {
                if v_isShared_2767_ == 0 {
                    v___x_2769_ = v___x_2766_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
                    v___x_2769_ = v_reuseFailAlloc_2770_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2769_;
            }
            4 => {
                if v_isShared_2775_ == 0 {
                    v___x_2777_ = v___x_2774_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0___boxed(
    mut v_x_2780_: *mut leanh::LeanObject,
    mut v_bi_2781_: *mut leanh::LeanObject,
    mut v_t_2782_: *mut leanh::LeanObject,
    mut v_b_2783_: *mut leanh::LeanObject,
    mut v___y_2784_: *mut leanh::LeanObject,
    mut v___y_2785_: *mut leanh::LeanObject,
    mut v___y_2786_: *mut leanh::LeanObject,
    mut v___y_2787_: *mut leanh::LeanObject,
    mut v___y_2788_: *mut leanh::LeanObject,
    mut v___y_2789_: *mut leanh::LeanObject,
    mut v___y_2790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_2791_: u8 = 0;
    let mut v_res_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2791_ = (leanh::lean_unbox(v_bi_2781_) as u8);
    v_res_2792_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(
        v_x_2780_,
        v_bi_boxed_2791_,
        v_t_2782_,
        v_b_2783_,
        v___y_2784_,
        v___y_2785_,
        v___y_2786_,
        v___y_2787_,
        v___y_2788_,
        v___y_2789_,
    );
    leanh::lean_dec(v___y_2789_);
    leanh::lean_dec_ref(v___y_2788_);
    leanh::lean_dec(v___y_2787_);
    leanh::lean_dec_ref(v___y_2786_);
    leanh::lean_dec(v___y_2785_);
    leanh::lean_dec_ref(v___y_2784_);
    return v_res_2792_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(
    mut v_xs_2793_: *mut leanh::LeanObject,
    mut v_i_2794_: *mut leanh::LeanObject,
    mut v_a_2795_: *mut leanh::LeanObject,
    mut v___y_2796_: *mut leanh::LeanObject,
    mut v___y_2797_: *mut leanh::LeanObject,
    mut v___y_2798_: *mut leanh::LeanObject,
    mut v___y_2799_: *mut leanh::LeanObject,
    mut v___y_2800_: *mut leanh::LeanObject,
    mut v___y_2801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2804_: u8 = 0;
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2803_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2804_ = lean_nat_dec_eq(v_i_2794_, v_zero_2803_);
                if v_isZero_2804_ == 1 {
                    leanh::lean_dec(v_i_2794_);
                    v___x_2805_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2805_, 0, v_a_2795_);
                    return v___x_2805_;
                } else {
                    v_one_2806_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2807_ = lean_nat_sub(v_i_2794_, v_one_2806_);
                    leanh::lean_dec(v_i_2794_);
                    v___x_2812_ = lean_array_fget_borrowed(v_xs_2793_, v_n_2807_);
                    v___x_2813_ = l_Lean_Expr_fvarId_x21(v___x_2812_);
                    v___x_2814_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_2813_,
                        v___y_2798_,
                        v___y_2800_,
                        v___y_2801_,
                    );
                    if leanh::lean_obj_tag(v___x_2814_) == 0 {
                        v_a_2815_ = leanh::lean_ctor_get(v___x_2814_, 0);
                        leanh::lean_inc(v_a_2815_);
                        leanh::lean_dec_ref_known(v___x_2814_, 1);
                        v___x_2816_ = l_Lean_LocalDecl_type(v_a_2815_);
                        v___x_2817_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
                            v___x_2816_,
                            v_n_2807_,
                            v_xs_2793_,
                            v___y_2797_,
                            v___y_2798_,
                        );
                        v_a_2818_ = leanh::lean_ctor_get(v___x_2817_, 0);
                        leanh::lean_inc(v_a_2818_);
                        leanh::lean_dec_ref(v___x_2817_);
                        v___x_2819_ = l_Lean_LocalDecl_userName(v_a_2815_);
                        v___x_2820_ = l_Lean_LocalDecl_binderInfo(v_a_2815_);
                        leanh::lean_dec(v_a_2815_);
                        v___x_2821_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_2819_, v___x_2820_, v_a_2818_, v_a_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
                        v___y_2809_ = v___x_2821_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_n_2807_);
                        leanh::lean_dec_ref(v_a_2795_);
                        v_a_2822_ = leanh::lean_ctor_get(v___x_2814_, 0);
                        v_isSharedCheck_2829_ =
                            (!leanh::lean_is_exclusive(v___x_2814_)) as u8;
                        if v_isSharedCheck_2829_ == 0 {
                            v___x_2824_ = v___x_2814_;
                            v_isShared_2825_ = v_isSharedCheck_2829_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2822_);
                            leanh::lean_dec(v___x_2814_);
                            v___x_2824_ = leanh::lean_box(0);
                            v_isShared_2825_ = v_isSharedCheck_2829_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_2809_) == 0 {
                    v_a_2810_ = leanh::lean_ctor_get(v___y_2809_, 0);
                    leanh::lean_inc(v_a_2810_);
                    leanh::lean_dec_ref_known(v___y_2809_, 1);
                    v_i_2794_ = v_n_2807_;
                    v_a_2795_ = v_a_2810_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_n_2807_);
                    return v___y_2809_;
                }
            }
            2 => {
                if v_isShared_2825_ == 0 {
                    v___x_2827_ = v___x_2824_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2828_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
                    v___x_2827_ = v_reuseFailAlloc_2828_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg___boxed(
    mut v_xs_2830_: *mut leanh::LeanObject,
    mut v_i_2831_: *mut leanh::LeanObject,
    mut v_a_2832_: *mut leanh::LeanObject,
    mut v___y_2833_: *mut leanh::LeanObject,
    mut v___y_2834_: *mut leanh::LeanObject,
    mut v___y_2835_: *mut leanh::LeanObject,
    mut v___y_2836_: *mut leanh::LeanObject,
    mut v___y_2837_: *mut leanh::LeanObject,
    mut v___y_2838_: *mut leanh::LeanObject,
    mut v___y_2839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2840_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2830_, v_i_2831_, v_a_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
    leanh::lean_dec(v___y_2838_);
    leanh::lean_dec_ref(v___y_2837_);
    leanh::lean_dec(v___y_2836_);
    leanh::lean_dec_ref(v___y_2835_);
    leanh::lean_dec(v___y_2834_);
    leanh::lean_dec_ref(v___y_2833_);
    leanh::lean_dec_ref(v_xs_2830_);
    return v_res_2840_;
}
pub unsafe fn l_Lean_Meta_Sym_mkForallFVarsS(
    mut v_xs_2841_: *mut leanh::LeanObject,
    mut v_e_2842_: *mut leanh::LeanObject,
    mut v_a_2843_: *mut leanh::LeanObject,
    mut v_a_2844_: *mut leanh::LeanObject,
    mut v_a_2845_: *mut leanh::LeanObject,
    mut v_a_2846_: *mut leanh::LeanObject,
    mut v_a_2847_: *mut leanh::LeanObject,
    mut v_a_2848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2850_ = leanh::lean_unsigned_to_nat(0);
    v___x_2851_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
        v_e_2842_,
        v___x_2850_,
        v_xs_2841_,
        v_a_2844_,
        v_a_2845_,
    );
    v_a_2852_ = leanh::lean_ctor_get(v___x_2851_, 0);
    leanh::lean_inc(v_a_2852_);
    leanh::lean_dec_ref(v___x_2851_);
    v___x_2853_ = lean_array_get_size(v_xs_2841_);
    v___x_2854_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2841_, v___x_2853_, v_a_2852_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
    return v___x_2854_;
}
pub unsafe fn l_Lean_Meta_Sym_mkForallFVarsS___boxed(
    mut v_xs_2855_: *mut leanh::LeanObject,
    mut v_e_2856_: *mut leanh::LeanObject,
    mut v_a_2857_: *mut leanh::LeanObject,
    mut v_a_2858_: *mut leanh::LeanObject,
    mut v_a_2859_: *mut leanh::LeanObject,
    mut v_a_2860_: *mut leanh::LeanObject,
    mut v_a_2861_: *mut leanh::LeanObject,
    mut v_a_2862_: *mut leanh::LeanObject,
    mut v_a_2863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2864_ = l_Lean_Meta_Sym_mkForallFVarsS(
        v_xs_2855_, v_e_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_,
    );
    leanh::lean_dec(v_a_2862_);
    leanh::lean_dec_ref(v_a_2861_);
    leanh::lean_dec(v_a_2860_);
    leanh::lean_dec_ref(v_a_2859_);
    leanh::lean_dec(v_a_2858_);
    leanh::lean_dec_ref(v_a_2857_);
    leanh::lean_dec_ref(v_xs_2855_);
    return v_res_2864_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(
    mut v_xs_2865_: *mut leanh::LeanObject,
    mut v_n_2866_: *mut leanh::LeanObject,
    mut v_i_2867_: *mut leanh::LeanObject,
    mut v_a_2868_: *mut leanh::LeanObject,
    mut v_a_2869_: *mut leanh::LeanObject,
    mut v___y_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
    mut v___y_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2877_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2865_, v_i_2867_, v_a_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
    return v___x_2877_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(
    mut v_xs_2878_: *mut leanh::LeanObject,
    mut v_n_2879_: *mut leanh::LeanObject,
    mut v_i_2880_: *mut leanh::LeanObject,
    mut v_a_2881_: *mut leanh::LeanObject,
    mut v_a_2882_: *mut leanh::LeanObject,
    mut v___y_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
    mut v___y_2888_: *mut leanh::LeanObject,
    mut v___y_2889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2890_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_2878_, v_n_2879_, v_i_2880_, v_a_2881_, v_a_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
    leanh::lean_dec(v___y_2888_);
    leanh::lean_dec_ref(v___y_2887_);
    leanh::lean_dec(v___y_2886_);
    leanh::lean_dec_ref(v___y_2885_);
    leanh::lean_dec(v___y_2884_);
    leanh::lean_dec_ref(v___y_2883_);
    leanh::lean_dec(v_n_2879_);
    leanh::lean_dec_ref(v_xs_2878_);
    return v_res_2890_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_AbstractS(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
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
pub unsafe fn meta_initialize_Lean_Meta_Sym_AbstractS(
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
pub unsafe fn initialize_Lean_Meta_Sym_AbstractS(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_AbstractS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_AbstractS(builtin);
}