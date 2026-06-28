// Lean compiler output
// Module: Lean.Meta.Sym.AbstractS
// Imports: Lean.Meta.Sym.SymM Lean.Meta.Sym.ReplaceS Init.Omega
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_uget_borrowed, lean_mk_array};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_uint64_mix_hash,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97, 115, 105, 99, 65, 117, 120, 0]};
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0]};
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0]};
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1: usize = 0;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    v___x_1449_ =
        l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__2;
    v___x_1450_ = lean_unsigned_to_nat(14);
    v___x_1451_ = lean_unsigned_to_nat(22);
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
    mut v_toDeBruijn_x3f_1457_: *mut LeanObject,
    mut v___x_1458_: *mut LeanObject,
    mut v_maxFVar_1459_: *mut LeanObject,
    mut v_minIndex_1460_: *mut LeanObject,
    mut v_lctx_1461_: *mut LeanObject,
    mut v___x_1462_: *mut LeanObject,
    mut v_e_1463_: *mut LeanObject,
    mut v_offset_1464_: *mut LeanObject,
    mut v___y_1465_: u8,
    mut v___y_1466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxIndex_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: u8 = 0;
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1486_: u8 = 0;
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873__overap_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1495_: u8 = 0;
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1502_: u8 = 0;
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_1463_) {
                1 => {
                    lean_dec_ref(v_lctx_1461_);
                    v_fvarId_1481_ = lean_ctor_get(v_e_1463_, 0);
                    lean_inc(v_fvarId_1481_);
                    v___x_1482_ = lean_apply_1(v_toDeBruijn_x3f_1457_, v_fvarId_1481_);
                    if lean_obj_tag(v___x_1482_) == 1 {
                        lean_dec_ref_known(v_e_1463_, 1);
                        v_val_1483_ = lean_ctor_get(v___x_1482_, 0);
                        v_isSharedCheck_1503_ = (!lean_is_exclusive(v___x_1482_)) as u8;
                        if v_isSharedCheck_1503_ == 0 {
                            v___x_1485_ = v___x_1482_;
                            v_isShared_1486_ = v_isSharedCheck_1503_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_1483_);
                            lean_dec(v___x_1482_);
                            v___x_1485_ = lean_box(0);
                            v_isShared_1486_ = v_isSharedCheck_1503_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1482_);
                        lean_dec_ref(v___x_1458_);
                        v___x_1504_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1504_, 0, v_e_1463_);
                        v___x_1505_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1505_, 0, v___x_1504_);
                        lean_ctor_set(v___x_1505_, 1, v___y_1466_);
                        return v___x_1505_;
                    }
                }
                9 => {
                    lean_dec_ref(v_lctx_1461_);
                    lean_dec_ref(v___x_1458_);
                    lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1506_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1506_, 0, v_e_1463_);
                    v___x_1507_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1507_, 0, v___x_1506_);
                    lean_ctor_set(v___x_1507_, 1, v___y_1466_);
                    return v___x_1507_;
                }
                2 => {
                    lean_dec_ref(v_lctx_1461_);
                    lean_dec_ref(v___x_1458_);
                    lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1508_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1508_, 0, v_e_1463_);
                    v___x_1509_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1509_, 0, v___x_1508_);
                    lean_ctor_set(v___x_1509_, 1, v___y_1466_);
                    return v___x_1509_;
                }
                0 => {
                    lean_dec_ref(v_lctx_1461_);
                    lean_dec_ref(v___x_1458_);
                    lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1510_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1510_, 0, v_e_1463_);
                    v___x_1511_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1511_, 0, v___x_1510_);
                    lean_ctor_set(v___x_1511_, 1, v___y_1466_);
                    return v___x_1511_;
                }
                4 => {
                    lean_dec_ref(v_lctx_1461_);
                    lean_dec_ref(v___x_1458_);
                    lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1512_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1512_, 0, v_e_1463_);
                    v___x_1513_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1513_, 0, v___x_1512_);
                    lean_ctor_set(v___x_1513_, 1, v___y_1466_);
                    return v___x_1513_;
                }
                3 => {
                    lean_dec_ref(v_lctx_1461_);
                    lean_dec_ref(v___x_1458_);
                    lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1514_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1514_, 0, v_e_1463_);
                    v___x_1515_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1515_, 0, v___x_1514_);
                    lean_ctor_set(v___x_1515_, 1, v___y_1466_);
                    return v___x_1515_;
                }
                _ => {
                    lean_dec_ref(v___x_1458_);
                    lean_dec_ref(v_toDeBruijn_x3f_1457_);
                    v___x_1516_ = l_Lean_Expr_hasFVar(v_e_1463_);
                    if v___x_1516_ == 0 {
                        lean_dec_ref(v_lctx_1461_);
                        v___x_1517_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1517_, 0, v_e_1463_);
                        v___x_1518_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1518_, 0, v___x_1517_);
                        lean_ctor_set(v___x_1518_, 1, v___y_1466_);
                        return v___x_1518_;
                    } else {
                        v___f_1519_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__4;
                        v___f_1520_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__5;
                        lean_inc_ref(v_e_1463_);
                        v___x_1521_ = l_Lean_PersistentHashMap_find_x3f___redArg(
                            v___f_1519_,
                            v___f_1520_,
                            v_maxFVar_1459_,
                            v_e_1463_,
                        );
                        if lean_obj_tag(v___x_1521_) == 1 {
                            v_val_1522_ = lean_ctor_get(v___x_1521_, 0);
                            lean_inc(v_val_1522_);
                            lean_dec_ref_known(v___x_1521_, 1);
                            if lean_obj_tag(v_val_1522_) == 0 {
                                v___x_1523_ = lean_box(0);
                                v___x_1524_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                                v___x_1525_ = l_panic___redArg(v___x_1523_, v___x_1524_);
                                v___y_1476_ = v___x_1525_;
                                state = 2;
                                continue;
                            } else {
                                v_val_1526_ = lean_ctor_get(v_val_1522_, 0);
                                lean_inc(v_val_1526_);
                                lean_dec_ref_known(v_val_1522_, 1);
                                v___y_1476_ = v_val_1526_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_1521_);
                            lean_dec_ref(v_e_1463_);
                            lean_dec_ref(v_lctx_1461_);
                            v___x_1527_ = lean_box(0);
                            v___x_1528_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1528_, 0, v___x_1527_);
                            lean_ctor_set(v___x_1528_, 1, v___y_1466_);
                            return v___x_1528_;
                        }
                    }
                }
            },
            1 => {
                v_maxIndex_1469_ = l_Lean_LocalDecl_index(v___y_1468_);
                lean_dec_ref(v___y_1468_);
                v___x_1470_ = lean_nat_dec_lt(v_maxIndex_1469_, v_minIndex_1460_);
                lean_dec(v_maxIndex_1469_);
                if v___x_1470_ == 0 {
                    lean_dec_ref(v_e_1463_);
                    v___x_1471_ = lean_box(0);
                    v___x_1472_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1472_, 0, v___x_1471_);
                    lean_ctor_set(v___x_1472_, 1, v___y_1466_);
                    return v___x_1472_;
                } else {
                    v___x_1473_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1473_, 0, v_e_1463_);
                    v___x_1474_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1474_, 0, v___x_1473_);
                    lean_ctor_set(v___x_1474_, 1, v___y_1466_);
                    return v___x_1474_;
                }
            }
            2 => {
                v___x_1477_ = lean_local_ctx_find(v_lctx_1461_, v___y_1476_);
                if lean_obj_tag(v___x_1477_) == 0 {
                    v___x_1478_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                    v___x_1479_ = l_panic___redArg(v___x_1462_, v___x_1478_);
                    v___y_1468_ = v___x_1479_;
                    state = 1;
                    continue;
                } else {
                    v_val_1480_ = lean_ctor_get(v___x_1477_, 0);
                    lean_inc(v_val_1480_);
                    lean_dec_ref_known(v___x_1477_, 1);
                    v___y_1468_ = v_val_1480_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1487_ = lean_nat_add(v_offset_1464_, v_val_1483_);
                lean_dec(v_val_1483_);
                v___x_2873__overap_1488_ =
                    l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v___x_1458_, v___x_1487_);
                v___x_1489_ = lean_box((v___y_1465_) as usize);
                v___x_1490_ = lean_apply_2(v___x_2873__overap_1488_, v___x_1489_, v___y_1466_);
                v_fst_1491_ = lean_ctor_get(v___x_1490_, 0);
                v_snd_1492_ = lean_ctor_get(v___x_1490_, 1);
                v_isSharedCheck_1502_ = (!lean_is_exclusive(v___x_1490_)) as u8;
                if v_isSharedCheck_1502_ == 0 {
                    v___x_1494_ = v___x_1490_;
                    v_isShared_1495_ = v_isSharedCheck_1502_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_1492_);
                    lean_inc(v_fst_1491_);
                    lean_dec(v___x_1490_);
                    v___x_1494_ = lean_box(0);
                    v_isShared_1495_ = v_isSharedCheck_1502_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1486_ == 0 {
                    lean_ctor_set(v___x_1485_, 0, v_fst_1491_);
                    v___x_1497_ = v___x_1485_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_fst_1491_);
                    v___x_1497_ = v_reuseFailAlloc_1501_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1495_ == 0 {
                    lean_ctor_set(v___x_1494_, 0, v___x_1497_);
                    v___x_1499_ = v___x_1494_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1497_);
                    lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_snd_1492_);
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
    mut v_toDeBruijn_x3f_1529_: *mut LeanObject,
    mut v___x_1530_: *mut LeanObject,
    mut v_maxFVar_1531_: *mut LeanObject,
    mut v_minIndex_1532_: *mut LeanObject,
    mut v_lctx_1533_: *mut LeanObject,
    mut v___x_1534_: *mut LeanObject,
    mut v_e_1535_: *mut LeanObject,
    mut v_offset_1536_: *mut LeanObject,
    mut v___y_1537_: *mut LeanObject,
    mut v___y_1538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2965__boxed_1539_: u8 = 0;
    let mut v_res_1540_: *mut LeanObject = core::ptr::null_mut();
    v___y_2965__boxed_1539_ = (lean_unbox(v___y_1537_) as u8);
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
    lean_dec(v_offset_1536_);
    lean_dec_ref(v___x_1534_);
    lean_dec(v_minIndex_1532_);
    lean_dec_ref(v_maxFVar_1531_);
    return v_res_1540_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0()
-> *mut LeanObject {
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    v___x_1541_ = lean_box(0);
    v___x_1542_ = lean_unsigned_to_nat(16);
    v___x_1543_ = lean_mk_array(v___x_1542_, v___x_1541_);
    return v___x_1543_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1()
-> *mut LeanObject {
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v___x_1544_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once
        ),
        _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0,
    );
    v___x_1545_ = lean_unsigned_to_nat(0);
    v___x_1546_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1546_, 0, v___x_1545_);
    lean_ctor_set(v___x_1546_, 1, v___x_1544_);
    return v___x_1546_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore(
    mut v_e_1547_: *mut LeanObject,
    mut v_lctx_1548_: *mut LeanObject,
    mut v_maxFVar_1549_: *mut LeanObject,
    mut v_minFVarId_1550_: *mut LeanObject,
    mut v_toDeBruijn_x3f_1551_: *mut LeanObject,
    mut v_a_1552_: u8,
    mut v_a_1553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minIndex_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1566_: u8 = 0;
    let mut v_val_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut v_unused_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1580_: u8 = 0;
    let mut v_unused_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1585_: u8 = 0;
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1589_: u8 = 0;
    let mut v_unused_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1594_: u8 = 0;
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v_unused_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_unused_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1616_: u8 = 0;
    let mut v_unused_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut v_unused_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1635_: u8 = 0;
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut v_unused_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1554_ = l_Lean_instInhabitedLocalDecl_default;
                v___x_1555_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM;
                lean_inc_ref(v_lctx_1548_);
                v___x_1641_ = lean_local_ctx_find(v_lctx_1548_, v_minFVarId_1550_);
                if lean_obj_tag(v___x_1641_) == 0 {
                    v___x_1642_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                    v___x_1643_ = l_panic___redArg(v___x_1554_, v___x_1642_);
                    v___y_1557_ = v___x_1643_;
                    state = 1;
                    continue;
                } else {
                    v_val_1644_ = lean_ctor_get(v___x_1641_, 0);
                    lean_inc(v_val_1644_);
                    lean_dec_ref_known(v___x_1641_, 1);
                    v___y_1557_ = v_val_1644_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_minIndex_1558_ = l_Lean_LocalDecl_index(v___y_1557_);
                lean_dec_ref(v___y_1557_);
                lean_inc_ref(v_lctx_1548_);
                lean_inc(v_minIndex_1558_);
                lean_inc_ref(v_maxFVar_1549_);
                lean_inc_ref(v_toDeBruijn_x3f_1551_);
                v___f_1559_ = lean_alloc_closure(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___boxed as *mut core::ffi::c_void, 10, 6);
                lean_closure_set(v___f_1559_, 0, v_toDeBruijn_x3f_1551_);
                lean_closure_set(v___f_1559_, 1, v___x_1555_);
                lean_closure_set(v___f_1559_, 2, v_maxFVar_1549_);
                lean_closure_set(v___f_1559_, 3, v_minIndex_1558_);
                lean_closure_set(v___f_1559_, 4, v_lctx_1548_);
                lean_closure_set(v___f_1559_, 5, v___x_1554_);
                v___x_1560_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_e_1547_);
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
                lean_dec(v_minIndex_1558_);
                lean_dec_ref(v_maxFVar_1549_);
                v_fst_1562_ = lean_ctor_get(v___x_1561_, 0);
                lean_inc(v_fst_1562_);
                if lean_obj_tag(v_fst_1562_) == 1 {
                    lean_dec_ref(v___f_1559_);
                    lean_dec_ref(v_e_1547_);
                    v_snd_1563_ = lean_ctor_get(v___x_1561_, 1);
                    v_isSharedCheck_1571_ = (!lean_is_exclusive(v___x_1561_)) as u8;
                    if v_isSharedCheck_1571_ == 0 {
                        v_unused_1572_ = lean_ctor_get(v___x_1561_, 0);
                        lean_dec(v_unused_1572_);
                        v___x_1565_ = v___x_1561_;
                        v_isShared_1566_ = v_isSharedCheck_1571_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_1563_);
                        lean_dec(v___x_1561_);
                        v___x_1565_ = lean_box(0);
                        v_isShared_1566_ = v_isSharedCheck_1571_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_1562_);
                    match lean_obj_tag(v_e_1547_) {
                        9 => {
                            lean_dec_ref(v___f_1559_);
                            v_snd_1573_ = lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1580_ = (!lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1580_ == 0 {
                                v_unused_1581_ = lean_ctor_get(v___x_1561_, 0);
                                lean_dec(v_unused_1581_);
                                v___x_1575_ = v___x_1561_;
                                v_isShared_1576_ = v_isSharedCheck_1580_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_snd_1573_);
                                lean_dec(v___x_1561_);
                                v___x_1575_ = lean_box(0);
                                v_isShared_1576_ = v_isSharedCheck_1580_;
                                state = 4;
                                continue;
                            }
                        }
                        2 => {
                            lean_dec_ref(v___f_1559_);
                            v_snd_1582_ = lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1589_ = (!lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1589_ == 0 {
                                v_unused_1590_ = lean_ctor_get(v___x_1561_, 0);
                                lean_dec(v_unused_1590_);
                                v___x_1584_ = v___x_1561_;
                                v_isShared_1585_ = v_isSharedCheck_1589_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_snd_1582_);
                                lean_dec(v___x_1561_);
                                v___x_1584_ = lean_box(0);
                                v_isShared_1585_ = v_isSharedCheck_1589_;
                                state = 6;
                                continue;
                            }
                        }
                        0 => {
                            lean_dec_ref(v___f_1559_);
                            v_snd_1591_ = lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1598_ = (!lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1598_ == 0 {
                                v_unused_1599_ = lean_ctor_get(v___x_1561_, 0);
                                lean_dec(v_unused_1599_);
                                v___x_1593_ = v___x_1561_;
                                v_isShared_1594_ = v_isSharedCheck_1598_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_snd_1591_);
                                lean_dec(v___x_1561_);
                                v___x_1593_ = lean_box(0);
                                v_isShared_1594_ = v_isSharedCheck_1598_;
                                state = 8;
                                continue;
                            }
                        }
                        1 => {
                            lean_dec_ref(v___f_1559_);
                            v_snd_1600_ = lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1607_ = (!lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1607_ == 0 {
                                v_unused_1608_ = lean_ctor_get(v___x_1561_, 0);
                                lean_dec(v_unused_1608_);
                                v___x_1602_ = v___x_1561_;
                                v_isShared_1603_ = v_isSharedCheck_1607_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_snd_1600_);
                                lean_dec(v___x_1561_);
                                v___x_1602_ = lean_box(0);
                                v_isShared_1603_ = v_isSharedCheck_1607_;
                                state = 10;
                                continue;
                            }
                        }
                        4 => {
                            lean_dec_ref(v___f_1559_);
                            v_snd_1609_ = lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1616_ = (!lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1616_ == 0 {
                                v_unused_1617_ = lean_ctor_get(v___x_1561_, 0);
                                lean_dec(v_unused_1617_);
                                v___x_1611_ = v___x_1561_;
                                v_isShared_1612_ = v_isSharedCheck_1616_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_snd_1609_);
                                lean_dec(v___x_1561_);
                                v___x_1611_ = lean_box(0);
                                v_isShared_1612_ = v_isSharedCheck_1616_;
                                state = 12;
                                continue;
                            }
                        }
                        3 => {
                            lean_dec_ref(v___f_1559_);
                            v_snd_1618_ = lean_ctor_get(v___x_1561_, 1);
                            v_isSharedCheck_1625_ = (!lean_is_exclusive(v___x_1561_)) as u8;
                            if v_isSharedCheck_1625_ == 0 {
                                v_unused_1626_ = lean_ctor_get(v___x_1561_, 0);
                                lean_dec(v_unused_1626_);
                                v___x_1620_ = v___x_1561_;
                                v_isShared_1621_ = v_isSharedCheck_1625_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_snd_1618_);
                                lean_dec(v___x_1561_);
                                v___x_1620_ = lean_box(0);
                                v_isShared_1621_ = v_isSharedCheck_1625_;
                                state = 14;
                                continue;
                            }
                        }
                        _ => {
                            v_snd_1627_ = lean_ctor_get(v___x_1561_, 1);
                            lean_inc(v_snd_1627_);
                            lean_dec_ref(v___x_1561_);
                            v___x_1628_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__1);
                            v___x_1629_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit(
                                v_e_1547_,
                                v___x_1560_,
                                v___f_1559_,
                                v___x_1628_,
                                v_a_1552_,
                                v_snd_1627_,
                            );
                            v_fst_1630_ = lean_ctor_get(v___x_1629_, 0);
                            lean_inc(v_fst_1630_);
                            v_snd_1631_ = lean_ctor_get(v___x_1629_, 1);
                            lean_inc(v_snd_1631_);
                            lean_dec_ref(v___x_1629_);
                            v_fst_1632_ = lean_ctor_get(v_fst_1630_, 0);
                            v_isSharedCheck_1639_ = (!lean_is_exclusive(v_fst_1630_)) as u8;
                            if v_isSharedCheck_1639_ == 0 {
                                v_unused_1640_ = lean_ctor_get(v_fst_1630_, 1);
                                lean_dec(v_unused_1640_);
                                v___x_1634_ = v_fst_1630_;
                                v_isShared_1635_ = v_isSharedCheck_1639_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_fst_1632_);
                                lean_dec(v_fst_1630_);
                                v___x_1634_ = lean_box(0);
                                v_isShared_1635_ = v_isSharedCheck_1639_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v_val_1567_ = lean_ctor_get(v_fst_1562_, 0);
                lean_inc(v_val_1567_);
                lean_dec_ref_known(v_fst_1562_, 1);
                if v_isShared_1566_ == 0 {
                    lean_ctor_set(v___x_1565_, 0, v_val_1567_);
                    v___x_1569_ = v___x_1565_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_val_1567_);
                    lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_snd_1563_);
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
                    lean_ctor_set(v___x_1575_, 0, v_e_1547_);
                    v___x_1578_ = v___x_1575_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_e_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_snd_1573_);
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
                    lean_ctor_set(v___x_1584_, 0, v_e_1547_);
                    v___x_1587_ = v___x_1584_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_e_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1588_, 1, v_snd_1582_);
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
                    lean_ctor_set(v___x_1593_, 0, v_e_1547_);
                    v___x_1596_ = v___x_1593_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_e_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_snd_1591_);
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
                    lean_ctor_set(v___x_1602_, 0, v_e_1547_);
                    v___x_1605_ = v___x_1602_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_e_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_snd_1600_);
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
                    lean_ctor_set(v___x_1611_, 0, v_e_1547_);
                    v___x_1614_ = v___x_1611_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_e_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_snd_1609_);
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
                    lean_ctor_set(v___x_1620_, 0, v_e_1547_);
                    v___x_1623_ = v___x_1620_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_e_1547_);
                    lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_snd_1618_);
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
                    lean_ctor_set(v___x_1634_, 1, v_snd_1631_);
                    v___x_1637_ = v___x_1634_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_fst_1632_);
                    lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_snd_1631_);
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
    mut v_e_1645_: *mut LeanObject,
    mut v_lctx_1646_: *mut LeanObject,
    mut v_maxFVar_1647_: *mut LeanObject,
    mut v_minFVarId_1648_: *mut LeanObject,
    mut v_toDeBruijn_x3f_1649_: *mut LeanObject,
    mut v_a_1650_: *mut LeanObject,
    mut v_a_1651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_1652_: u8 = 0;
    let mut v_res_1653_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_1652_ = (lean_unbox(v_a_1650_) as u8);
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
    mut v_start_1654_: *mut LeanObject,
    mut v_xs_1655_: *mut LeanObject,
    mut v_fvarId_1656_: *mut LeanObject,
    mut v_bidx_1657_: *mut LeanObject,
    mut v_i_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: u8 = 0;
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1659_ = lean_array_fget_borrowed(v_xs_1655_, v_i_1658_);
                v___x_1660_ = l_Lean_Expr_fvarId_x21(v___x_1659_);
                v___x_1661_ = l_Lean_instBEqFVarId_beq(v___x_1660_, v_fvarId_1656_);
                lean_dec(v___x_1660_);
                if v___x_1661_ == 0 {
                    v___x_1662_ = lean_nat_dec_lt(v_start_1654_, v_i_1658_);
                    if v___x_1662_ == 0 {
                        lean_dec(v_i_1658_);
                        lean_dec(v_bidx_1657_);
                        v___x_1663_ = lean_box(0);
                        return v___x_1663_;
                    } else {
                        v___x_1664_ = lean_unsigned_to_nat(1);
                        v___x_1665_ = lean_nat_add(v_bidx_1657_, v___x_1664_);
                        lean_dec(v_bidx_1657_);
                        v___x_1666_ = lean_nat_sub(v_i_1658_, v___x_1664_);
                        lean_dec(v_i_1658_);
                        v_bidx_1657_ = v___x_1665_;
                        v_i_1658_ = v___x_1666_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_i_1658_);
                    v___x_1668_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1668_, 0, v_bidx_1657_);
                    return v___x_1668_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg___boxed(
    mut v_start_1669_: *mut LeanObject,
    mut v_xs_1670_: *mut LeanObject,
    mut v_fvarId_1671_: *mut LeanObject,
    mut v_bidx_1672_: *mut LeanObject,
    mut v_i_1673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1674_: *mut LeanObject = core::ptr::null_mut();
    v_res_1674_ =
        l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(
            v_start_1669_,
            v_xs_1670_,
            v_fvarId_1671_,
            v_bidx_1672_,
            v_i_1673_,
        );
    lean_dec(v_fvarId_1671_);
    lean_dec_ref(v_xs_1670_);
    lean_dec(v_start_1669_);
    return v_res_1674_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(
    mut v_start_1675_: *mut LeanObject,
    mut v_xs_1676_: *mut LeanObject,
    mut v_fvarId_1677_: *mut LeanObject,
    mut v_bidx_1678_: *mut LeanObject,
    mut v_i_1679_: *mut LeanObject,
    mut v_h_1680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_start_1682_: *mut LeanObject,
    mut v_xs_1683_: *mut LeanObject,
    mut v_fvarId_1684_: *mut LeanObject,
    mut v_bidx_1685_: *mut LeanObject,
    mut v_i_1686_: *mut LeanObject,
    mut v_h_1687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1688_: *mut LeanObject = core::ptr::null_mut();
    v_res_1688_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go(
        v_start_1682_,
        v_xs_1683_,
        v_fvarId_1684_,
        v_bidx_1685_,
        v_i_1686_,
        v_h_1687_,
    );
    lean_dec(v_fvarId_1684_);
    lean_dec_ref(v_xs_1683_);
    lean_dec(v_start_1682_);
    return v_res_1688_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    v___x_1689_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1689_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    v___x_1690_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__0);
    v___x_1691_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1691_, 0, v___x_1690_);
    return v___x_1691_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(
    mut v_00_u03b2_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    v___x_1693_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0___closed__1);
    return v___x_1693_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(
    mut v_msg_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    v___x_1695_ = l_Lean_instInhabitedLocalDecl_default;
    v___x_1696_ = lean_panic_fn_borrowed(v___x_1695_, v_msg_1694_);
    return v___x_1696_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(
    mut v_idx_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    v___x_1699_ = l_Lean_Expr_bvar___override(v_idx_1697_);
    v___x_1700_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_1699_, v___y_1698_);
    return v___x_1700_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(
    mut v_idx_1701_: *mut LeanObject,
    mut v___y_1702_: u8,
    mut v___y_1703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    v___x_1704_ =
        l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(
            v_idx_1701_,
            v___y_1703_,
        );
    return v___x_1704_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___boxed(
    mut v_idx_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_25263__boxed_1708_: u8 = 0;
    let mut v_res_1709_: *mut LeanObject = core::ptr::null_mut();
    v___y_25263__boxed_1708_ = (lean_unbox(v___y_1706_) as u8);
    v_res_1709_ =
        l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2(
            v_idx_1705_,
            v___y_25263__boxed_1708_,
            v___y_1707_,
        );
    return v_res_1709_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(
    mut v_msg_1710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    v___x_1711_ = lean_box(0);
    v___x_1712_ = lean_panic_fn_borrowed(v___x_1711_, v_msg_1710_);
    return v___x_1712_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(
    mut v_structName_1713_: *mut LeanObject,
    mut v_idx_1714_: *mut LeanObject,
    mut v_struct_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: u8,
    mut v___y_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1728_: u8 = 0;
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1733_: u8 = 0;
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1735_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_struct_1715_);
                    v___x_1734_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_struct_1715_,
                        v___y_1717_,
                        v___y_1718_,
                    );
                    v_snd_1735_ = lean_ctor_get(v___x_1734_, 1);
                    lean_inc(v_snd_1735_);
                    lean_dec_ref(v___x_1734_);
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
                v_fst_1724_ = lean_ctor_get(v___x_1723_, 0);
                v_snd_1725_ = lean_ctor_get(v___x_1723_, 1);
                v_isSharedCheck_1733_ = (!lean_is_exclusive(v___x_1723_)) as u8;
                if v_isSharedCheck_1733_ == 0 {
                    v___x_1727_ = v___x_1723_;
                    v_isShared_1728_ = v_isSharedCheck_1733_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1725_);
                    lean_inc(v_fst_1724_);
                    lean_dec(v___x_1723_);
                    v___x_1727_ = lean_box(0);
                    v_isShared_1728_ = v_isSharedCheck_1733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1728_ == 0 {
                    lean_ctor_set(v___x_1727_, 1, v___y_1720_);
                    v___x_1730_ = v___x_1727_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_fst_1724_);
                    lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___y_1720_);
                    v___x_1730_ = v_reuseFailAlloc_1732_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1731_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1731_, 0, v___x_1730_);
                lean_ctor_set(v___x_1731_, 1, v_snd_1725_);
                return v___x_1731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12___boxed(
    mut v_structName_1736_: *mut LeanObject,
    mut v_idx_1737_: *mut LeanObject,
    mut v_struct_1738_: *mut LeanObject,
    mut v___y_1739_: *mut LeanObject,
    mut v___y_1740_: *mut LeanObject,
    mut v___y_1741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_25276__boxed_1742_: u8 = 0;
    let mut v_res_1743_: *mut LeanObject = core::ptr::null_mut();
    v___y_25276__boxed_1742_ = (lean_unbox(v___y_1740_) as u8);
    v_res_1743_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(v_structName_1736_, v_idx_1737_, v_struct_1738_, v___y_1739_, v___y_25276__boxed_1742_, v___y_1741_);
    return v_res_1743_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(
    mut v_d_1744_: *mut LeanObject,
    mut v_e_1745_: *mut LeanObject,
    mut v___y_1746_: *mut LeanObject,
    mut v___y_1747_: u8,
    mut v___y_1748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1758_: u8 = 0;
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1765_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_e_1745_);
                    v___x_1764_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_e_1745_,
                        v___y_1747_,
                        v___y_1748_,
                    );
                    v_snd_1765_ = lean_ctor_get(v___x_1764_, 1);
                    lean_inc(v_snd_1765_);
                    lean_dec_ref(v___x_1764_);
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
                v_fst_1754_ = lean_ctor_get(v___x_1753_, 0);
                v_snd_1755_ = lean_ctor_get(v___x_1753_, 1);
                v_isSharedCheck_1763_ = (!lean_is_exclusive(v___x_1753_)) as u8;
                if v_isSharedCheck_1763_ == 0 {
                    v___x_1757_ = v___x_1753_;
                    v_isShared_1758_ = v_isSharedCheck_1763_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1755_);
                    lean_inc(v_fst_1754_);
                    lean_dec(v___x_1753_);
                    v___x_1757_ = lean_box(0);
                    v_isShared_1758_ = v_isSharedCheck_1763_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1758_ == 0 {
                    lean_ctor_set(v___x_1757_, 1, v___y_1750_);
                    v___x_1760_ = v___x_1757_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_fst_1754_);
                    lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___y_1750_);
                    v___x_1760_ = v_reuseFailAlloc_1762_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1761_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1761_, 0, v___x_1760_);
                lean_ctor_set(v___x_1761_, 1, v_snd_1755_);
                return v___x_1761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11___boxed(
    mut v_d_1766_: *mut LeanObject,
    mut v_e_1767_: *mut LeanObject,
    mut v___y_1768_: *mut LeanObject,
    mut v___y_1769_: *mut LeanObject,
    mut v___y_1770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_25320__boxed_1771_: u8 = 0;
    let mut v_res_1772_: *mut LeanObject = core::ptr::null_mut();
    v___y_25320__boxed_1771_ = (lean_unbox(v___y_1769_) as u8);
    v_res_1772_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(v_d_1766_, v_e_1767_, v___y_1768_, v___y_25320__boxed_1771_, v___y_1770_);
    return v_res_1772_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(
    mut v_x_1773_: *mut LeanObject,
    mut v_bi_1774_: u8,
    mut v_t_1775_: *mut LeanObject,
    mut v_b_1776_: *mut LeanObject,
    mut v___y_1777_: *mut LeanObject,
    mut v___y_1778_: u8,
    mut v___y_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1789_: u8 = 0;
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1794_: u8 = 0;
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1798_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_t_1775_);
                    v___x_1795_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1775_,
                        v___y_1778_,
                        v___y_1779_,
                    );
                    v_snd_1796_ = lean_ctor_get(v___x_1795_, 1);
                    lean_inc(v_snd_1796_);
                    lean_dec_ref(v___x_1795_);
                    lean_inc_ref(v_b_1776_);
                    v___x_1797_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1776_,
                        v___y_1778_,
                        v_snd_1796_,
                    );
                    v_snd_1798_ = lean_ctor_get(v___x_1797_, 1);
                    lean_inc(v_snd_1798_);
                    lean_dec_ref(v___x_1797_);
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
                v_fst_1785_ = lean_ctor_get(v___x_1784_, 0);
                v_snd_1786_ = lean_ctor_get(v___x_1784_, 1);
                v_isSharedCheck_1794_ = (!lean_is_exclusive(v___x_1784_)) as u8;
                if v_isSharedCheck_1794_ == 0 {
                    v___x_1788_ = v___x_1784_;
                    v_isShared_1789_ = v_isSharedCheck_1794_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1786_);
                    lean_inc(v_fst_1785_);
                    lean_dec(v___x_1784_);
                    v___x_1788_ = lean_box(0);
                    v_isShared_1789_ = v_isSharedCheck_1794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1789_ == 0 {
                    lean_ctor_set(v___x_1788_, 1, v___y_1781_);
                    v___x_1791_ = v___x_1788_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_fst_1785_);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___y_1781_);
                    v___x_1791_ = v_reuseFailAlloc_1793_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1792_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1792_, 0, v___x_1791_);
                lean_ctor_set(v___x_1792_, 1, v_snd_1786_);
                return v___x_1792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9___boxed(
    mut v_x_1799_: *mut LeanObject,
    mut v_bi_1800_: *mut LeanObject,
    mut v_t_1801_: *mut LeanObject,
    mut v_b_1802_: *mut LeanObject,
    mut v___y_1803_: *mut LeanObject,
    mut v___y_1804_: *mut LeanObject,
    mut v___y_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_1806_: u8 = 0;
    let mut v___y_25364__boxed_1807_: u8 = 0;
    let mut v_res_1808_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_1806_ = (lean_unbox(v_bi_1800_) as u8);
    v___y_25364__boxed_1807_ = (lean_unbox(v___y_1804_) as u8);
    v_res_1808_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(v_x_1799_, v_bi_boxed_1806_, v_t_1801_, v_b_1802_, v___y_1803_, v___y_25364__boxed_1807_, v___y_1805_);
    return v_res_1808_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(
    mut v_x_1809_: *mut LeanObject,
    mut v_bi_1810_: u8,
    mut v_t_1811_: *mut LeanObject,
    mut v_b_1812_: *mut LeanObject,
    mut v___y_1813_: *mut LeanObject,
    mut v___y_1814_: u8,
    mut v___y_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1825_: u8 = 0;
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1830_: u8 = 0;
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1834_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_t_1811_);
                    v___x_1831_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1811_,
                        v___y_1814_,
                        v___y_1815_,
                    );
                    v_snd_1832_ = lean_ctor_get(v___x_1831_, 1);
                    lean_inc(v_snd_1832_);
                    lean_dec_ref(v___x_1831_);
                    lean_inc_ref(v_b_1812_);
                    v___x_1833_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1812_,
                        v___y_1814_,
                        v_snd_1832_,
                    );
                    v_snd_1834_ = lean_ctor_get(v___x_1833_, 1);
                    lean_inc(v_snd_1834_);
                    lean_dec_ref(v___x_1833_);
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
                v_fst_1821_ = lean_ctor_get(v___x_1820_, 0);
                v_snd_1822_ = lean_ctor_get(v___x_1820_, 1);
                v_isSharedCheck_1830_ = (!lean_is_exclusive(v___x_1820_)) as u8;
                if v_isSharedCheck_1830_ == 0 {
                    v___x_1824_ = v___x_1820_;
                    v_isShared_1825_ = v_isSharedCheck_1830_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1822_);
                    lean_inc(v_fst_1821_);
                    lean_dec(v___x_1820_);
                    v___x_1824_ = lean_box(0);
                    v_isShared_1825_ = v_isSharedCheck_1830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1825_ == 0 {
                    lean_ctor_set(v___x_1824_, 1, v___y_1817_);
                    v___x_1827_ = v___x_1824_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_fst_1821_);
                    lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___y_1817_);
                    v___x_1827_ = v_reuseFailAlloc_1829_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1828_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1828_, 0, v___x_1827_);
                lean_ctor_set(v___x_1828_, 1, v_snd_1822_);
                return v___x_1828_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8___boxed(
    mut v_x_1835_: *mut LeanObject,
    mut v_bi_1836_: *mut LeanObject,
    mut v_t_1837_: *mut LeanObject,
    mut v_b_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_1842_: u8 = 0;
    let mut v___y_25413__boxed_1843_: u8 = 0;
    let mut v_res_1844_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_1842_ = (lean_unbox(v_bi_1836_) as u8);
    v___y_25413__boxed_1843_ = (lean_unbox(v___y_1840_) as u8);
    v_res_1844_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(v_x_1835_, v_bi_boxed_1842_, v_t_1837_, v_b_1838_, v___y_1839_, v___y_25413__boxed_1843_, v___y_1841_);
    return v_res_1844_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(
    mut v_x_1845_: *mut LeanObject,
    mut v_t_1846_: *mut LeanObject,
    mut v_v_1847_: *mut LeanObject,
    mut v_b_1848_: *mut LeanObject,
    mut v_nondep_1849_: u8,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: u8,
    mut v___y_1852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1867_: u8 = 0;
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1873_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_t_1846_);
                    v___x_1868_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_1846_,
                        v___y_1851_,
                        v___y_1852_,
                    );
                    v_snd_1869_ = lean_ctor_get(v___x_1868_, 1);
                    lean_inc(v_snd_1869_);
                    lean_dec_ref(v___x_1868_);
                    lean_inc_ref(v_v_1847_);
                    v___x_1870_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_v_1847_,
                        v___y_1851_,
                        v_snd_1869_,
                    );
                    v_snd_1871_ = lean_ctor_get(v___x_1870_, 1);
                    lean_inc(v_snd_1871_);
                    lean_dec_ref(v___x_1870_);
                    lean_inc_ref(v_b_1848_);
                    v___x_1872_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_1848_,
                        v___y_1851_,
                        v_snd_1871_,
                    );
                    v_snd_1873_ = lean_ctor_get(v___x_1872_, 1);
                    lean_inc(v_snd_1873_);
                    lean_dec_ref(v___x_1872_);
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
                v_fst_1858_ = lean_ctor_get(v___x_1857_, 0);
                v_snd_1859_ = lean_ctor_get(v___x_1857_, 1);
                v_isSharedCheck_1867_ = (!lean_is_exclusive(v___x_1857_)) as u8;
                if v_isSharedCheck_1867_ == 0 {
                    v___x_1861_ = v___x_1857_;
                    v_isShared_1862_ = v_isSharedCheck_1867_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1859_);
                    lean_inc(v_fst_1858_);
                    lean_dec(v___x_1857_);
                    v___x_1861_ = lean_box(0);
                    v_isShared_1862_ = v_isSharedCheck_1867_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1862_ == 0 {
                    lean_ctor_set(v___x_1861_, 1, v___y_1854_);
                    v___x_1864_ = v___x_1861_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_fst_1858_);
                    lean_ctor_set(v_reuseFailAlloc_1866_, 1, v___y_1854_);
                    v___x_1864_ = v_reuseFailAlloc_1866_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1865_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1865_, 0, v___x_1864_);
                lean_ctor_set(v___x_1865_, 1, v_snd_1859_);
                return v___x_1865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10___boxed(
    mut v_x_1874_: *mut LeanObject,
    mut v_t_1875_: *mut LeanObject,
    mut v_v_1876_: *mut LeanObject,
    mut v_b_1877_: *mut LeanObject,
    mut v_nondep_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_1882_: u8 = 0;
    let mut v___y_25462__boxed_1883_: u8 = 0;
    let mut v_res_1884_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_1882_ = (lean_unbox(v_nondep_1878_) as u8);
    v___y_25462__boxed_1883_ = (lean_unbox(v___y_1880_) as u8);
    v_res_1884_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_x_1874_, v_t_1875_, v_v_1876_, v_b_1877_, v_nondep_boxed_1882_, v___y_1879_, v___y_25462__boxed_1883_, v___y_1881_);
    return v_res_1884_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(
    mut v_f_1885_: *mut LeanObject,
    mut v_a_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
    mut v___y_1888_: u8,
    mut v___y_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1899_: u8 = 0;
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1908_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_f_1885_);
                    v___x_1905_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_f_1885_,
                        v___y_1888_,
                        v___y_1889_,
                    );
                    v_snd_1906_ = lean_ctor_get(v___x_1905_, 1);
                    lean_inc(v_snd_1906_);
                    lean_dec_ref(v___x_1905_);
                    lean_inc_ref(v_a_1886_);
                    v___x_1907_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_a_1886_,
                        v___y_1888_,
                        v_snd_1906_,
                    );
                    v_snd_1908_ = lean_ctor_get(v___x_1907_, 1);
                    lean_inc(v_snd_1908_);
                    lean_dec_ref(v___x_1907_);
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
                v_fst_1895_ = lean_ctor_get(v___x_1894_, 0);
                v_snd_1896_ = lean_ctor_get(v___x_1894_, 1);
                v_isSharedCheck_1904_ = (!lean_is_exclusive(v___x_1894_)) as u8;
                if v_isSharedCheck_1904_ == 0 {
                    v___x_1898_ = v___x_1894_;
                    v_isShared_1899_ = v_isSharedCheck_1904_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1896_);
                    lean_inc(v_fst_1895_);
                    lean_dec(v___x_1894_);
                    v___x_1898_ = lean_box(0);
                    v_isShared_1899_ = v_isSharedCheck_1904_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1899_ == 0 {
                    lean_ctor_set(v___x_1898_, 1, v___y_1891_);
                    v___x_1901_ = v___x_1898_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_fst_1895_);
                    lean_ctor_set(v_reuseFailAlloc_1903_, 1, v___y_1891_);
                    v___x_1901_ = v_reuseFailAlloc_1903_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1902_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1902_, 0, v___x_1901_);
                lean_ctor_set(v___x_1902_, 1, v_snd_1896_);
                return v___x_1902_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7___boxed(
    mut v_f_1909_: *mut LeanObject,
    mut v_a_1910_: *mut LeanObject,
    mut v___y_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_25516__boxed_1914_: u8 = 0;
    let mut v_res_1915_: *mut LeanObject = core::ptr::null_mut();
    v___y_25516__boxed_1914_ = (lean_unbox(v___y_1912_) as u8);
    v_res_1915_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(v_f_1909_, v_a_1910_, v___y_1911_, v___y_25516__boxed_1914_, v___y_1913_);
    return v_res_1915_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(
    mut v_a_1916_: *mut LeanObject,
    mut v_x_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: u8 = 0;
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: u8 = 0;
    let mut v___x_1931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1917_) == 0 {
                    v___x_1918_ = lean_box(0);
                    return v___x_1918_;
                } else {
                    v_key_1919_ = lean_ctor_get(v_x_1917_, 0);
                    v_value_1920_ = lean_ctor_get(v_x_1917_, 1);
                    v_tail_1921_ = lean_ctor_get(v_x_1917_, 2);
                    v_fst_1926_ = lean_ctor_get(v_key_1919_, 0);
                    v_snd_1927_ = lean_ctor_get(v_key_1919_, 1);
                    v_fst_1928_ = lean_ctor_get(v_a_1916_, 0);
                    v_snd_1929_ = lean_ctor_get(v_a_1916_, 1);
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
                    lean_inc(v_value_1920_);
                    v___x_1925_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1925_, 0, v_value_1920_);
                    return v___x_1925_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg___boxed(
    mut v_a_1932_: *mut LeanObject,
    mut v_x_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1934_: *mut LeanObject = core::ptr::null_mut();
    v_res_1934_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(v_a_1932_, v_x_1933_);
    lean_dec(v_x_1933_);
    lean_dec_ref(v_a_1932_);
    return v_res_1934_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(
    mut v_m_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1937_ = lean_ctor_get(v_m_1935_, 1);
    v_fst_1938_ = lean_ctor_get(v_a_1936_, 0);
    v_snd_1939_ = lean_ctor_get(v_a_1936_, 1);
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
    mut v_m_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1959_: *mut LeanObject = core::ptr::null_mut();
    v_res_1959_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_m_1957_, v_a_1958_);
    lean_dec_ref(v_a_1958_);
    lean_dec_ref(v_m_1957_);
    return v_res_1959_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(
    mut v_keys_1960_: *mut LeanObject,
    mut v_vals_1961_: *mut LeanObject,
    mut v_i_1962_: *mut LeanObject,
    mut v_k_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1964_ = lean_array_get_size(v_keys_1960_);
                v___x_1965_ = lean_nat_dec_lt(v_i_1962_, v___x_1964_);
                if v___x_1965_ == 0 {
                    lean_dec(v_i_1962_);
                    v___x_1966_ = lean_box(0);
                    return v___x_1966_;
                } else {
                    v_k_x27_1967_ = lean_array_fget_borrowed(v_keys_1960_, v_i_1962_);
                    v___x_1968_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1963_,
                            v_k_x27_1967_,
                        );
                    if v___x_1968_ == 0 {
                        v___x_1969_ = lean_unsigned_to_nat(1);
                        v___x_1970_ = lean_nat_add(v_i_1962_, v___x_1969_);
                        lean_dec(v_i_1962_);
                        v_i_1962_ = v___x_1970_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1972_ = lean_array_fget_borrowed(v_vals_1961_, v_i_1962_);
                        lean_dec(v_i_1962_);
                        lean_inc(v___x_1972_);
                        v___x_1973_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1973_, 0, v___x_1972_);
                        return v___x_1973_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg___boxed(
    mut v_keys_1974_: *mut LeanObject,
    mut v_vals_1975_: *mut LeanObject,
    mut v_i_1976_: *mut LeanObject,
    mut v_k_1977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1978_: *mut LeanObject = core::ptr::null_mut();
    v_res_1978_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_keys_1974_, v_vals_1975_, v_i_1976_, v_k_1977_);
    lean_dec_ref(v_k_1977_);
    lean_dec_ref(v_vals_1975_);
    lean_dec_ref(v_keys_1974_);
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
    v___x_1983_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__0);
    v___x_1984_ = lean_usize_sub(v___x_1983_, v___x_1982_);
    return v___x_1984_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(
    mut v_x_1985_: *mut LeanObject,
    mut v_x_1986_: usize,
    mut v_x_1987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: usize = 0;
    let mut v___x_1991_: usize = 0;
    let mut v___x_1992_: usize = 0;
    let mut v_j_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: usize = 0;
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1985_) == 0 {
                    v_es_1988_ = lean_ctor_get(v_x_1985_, 0);
                    v___x_1989_ = lean_box(2);
                    v___x_1990_ = 5usize;
                    v___x_1991_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___closed__1);
                    v___x_1992_ = lean_usize_land(v_x_1986_, v___x_1991_);
                    v_j_1993_ = lean_usize_to_nat(v___x_1992_);
                    v___x_1994_ = lean_array_get_borrowed(v___x_1989_, v_es_1988_, v_j_1993_);
                    lean_dec(v_j_1993_);
                    match lean_obj_tag(v___x_1994_) {
                        0 => {
                            v_key_1995_ = lean_ctor_get(v___x_1994_, 0);
                            v_val_1996_ = lean_ctor_get(v___x_1994_, 1);
                            v___x_1997_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1987_, v_key_1995_);
                            if v___x_1997_ == 0 {
                                v___x_1998_ = lean_box(0);
                                return v___x_1998_;
                            } else {
                                lean_inc(v_val_1996_);
                                v___x_1999_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1999_, 0, v_val_1996_);
                                return v___x_1999_;
                            }
                        }
                        1 => {
                            v_node_2000_ = lean_ctor_get(v___x_1994_, 0);
                            v___x_2001_ = lean_usize_shift_right(v_x_1986_, v___x_1990_);
                            v_x_1985_ = v_node_2000_;
                            v_x_1986_ = v___x_2001_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2003_ = lean_box(0);
                            return v___x_2003_;
                        }
                    }
                } else {
                    v_ks_2004_ = lean_ctor_get(v_x_1985_, 0);
                    v_vs_2005_ = lean_ctor_get(v_x_1985_, 1);
                    v___x_2006_ = lean_unsigned_to_nat(0);
                    v___x_2007_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_ks_2004_, v_vs_2005_, v___x_2006_, v_x_1987_);
                    return v___x_2007_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg___boxed(
    mut v_x_2008_: *mut LeanObject,
    mut v_x_2009_: *mut LeanObject,
    mut v_x_2010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_25664__boxed_2011_: usize = 0;
    let mut v_res_2012_: *mut LeanObject = core::ptr::null_mut();
    v_x_25664__boxed_2011_ = lean_unbox_usize(v_x_2009_);
    lean_dec(v_x_2009_);
    v_res_2012_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_2008_, v_x_25664__boxed_2011_, v_x_2010_);
    lean_dec_ref(v_x_2010_);
    lean_dec_ref(v_x_2008_);
    return v_res_2012_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(
    mut v_x_2013_: *mut LeanObject,
    mut v_x_2014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2015_: u64 = 0;
    let mut v___x_2016_: usize = 0;
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    v___x_2015_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2014_);
    v___x_2016_ = lean_uint64_to_usize(v___x_2015_);
    v___x_2017_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_2013_, v___x_2016_, v_x_2014_);
    return v___x_2017_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg___boxed(
    mut v_x_2018_: *mut LeanObject,
    mut v_x_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2020_: *mut LeanObject = core::ptr::null_mut();
    v_res_2020_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_x_2018_, v_x_2019_);
    lean_dec_ref(v_x_2019_);
    lean_dec_ref(v_x_2018_);
    return v_res_2020_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(
    mut v_msg_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
    mut v___y_2030_: u8,
    mut v___y_2031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_24871__overap_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    v___f_2032_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__0;
    v___f_2033_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__1;
    v___f_2034_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__2;
    v___f_2035_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__3;
    v___f_2036_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__4;
    v___f_2037_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__5;
    v___f_2038_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___closed__6;
    v___x_2039_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2039_, 0, v___f_2032_);
    lean_ctor_set(v___x_2039_, 1, v___f_2033_);
    v___x_2040_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2040_, 0, v___x_2039_);
    lean_ctor_set(v___x_2040_, 1, v___f_2034_);
    lean_ctor_set(v___x_2040_, 2, v___f_2035_);
    lean_ctor_set(v___x_2040_, 3, v___f_2036_);
    lean_ctor_set(v___x_2040_, 4, v___f_2037_);
    v___x_2041_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2041_, 0, v___x_2040_);
    lean_ctor_set(v___x_2041_, 1, v___f_2038_);
    lean_inc_ref_n(v___x_2041_, 6);
    v___f_2042_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2042_, 0, v___x_2041_);
    v___f_2043_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2043_, 0, v___x_2041_);
    v___f_2044_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2044_, 0, v___x_2041_);
    v___f_2045_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2045_, 0, v___x_2041_);
    v___x_2046_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2046_, 0, lean_box(0));
    lean_closure_set(v___x_2046_, 1, lean_box(0));
    lean_closure_set(v___x_2046_, 2, v___x_2041_);
    v___x_2047_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2047_, 0, v___x_2046_);
    lean_ctor_set(v___x_2047_, 1, v___f_2042_);
    v___x_2048_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_2048_, 0, lean_box(0));
    lean_closure_set(v___x_2048_, 1, lean_box(0));
    lean_closure_set(v___x_2048_, 2, v___x_2041_);
    v___x_2049_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2049_, 0, v___x_2047_);
    lean_ctor_set(v___x_2049_, 1, v___x_2048_);
    lean_ctor_set(v___x_2049_, 2, v___f_2043_);
    lean_ctor_set(v___x_2049_, 3, v___f_2044_);
    lean_ctor_set(v___x_2049_, 4, v___f_2045_);
    v___x_2050_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2050_, 0, lean_box(0));
    lean_closure_set(v___x_2050_, 1, lean_box(0));
    lean_closure_set(v___x_2050_, 2, v___x_2041_);
    v___x_2051_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2051_, 0, v___x_2049_);
    lean_ctor_set(v___x_2051_, 1, v___x_2050_);
    v___x_2052_ = l_ReaderT_instMonad___redArg(v___x_2051_);
    lean_inc_ref_n(v___x_2052_, 6);
    v___f_2053_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2053_, 0, v___x_2052_);
    v___f_2054_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2054_, 0, v___x_2052_);
    v___f_2055_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2055_, 0, v___x_2052_);
    v___f_2056_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2056_, 0, v___x_2052_);
    v___x_2057_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2057_, 0, lean_box(0));
    lean_closure_set(v___x_2057_, 1, lean_box(0));
    lean_closure_set(v___x_2057_, 2, v___x_2052_);
    v___x_2058_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2058_, 0, v___x_2057_);
    lean_ctor_set(v___x_2058_, 1, v___f_2053_);
    v___x_2059_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_2059_, 0, lean_box(0));
    lean_closure_set(v___x_2059_, 1, lean_box(0));
    lean_closure_set(v___x_2059_, 2, v___x_2052_);
    v___x_2060_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2060_, 0, v___x_2058_);
    lean_ctor_set(v___x_2060_, 1, v___x_2059_);
    lean_ctor_set(v___x_2060_, 2, v___f_2054_);
    lean_ctor_set(v___x_2060_, 3, v___f_2055_);
    lean_ctor_set(v___x_2060_, 4, v___f_2056_);
    v___x_2061_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2061_, 0, lean_box(0));
    lean_closure_set(v___x_2061_, 1, lean_box(0));
    lean_closure_set(v___x_2061_, 2, v___x_2052_);
    v___x_2062_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2062_, 0, v___x_2060_);
    lean_ctor_set(v___x_2062_, 1, v___x_2061_);
    v___x_2063_ = l_Lean_instInhabitedExpr;
    v___x_2064_ = l_instInhabitedOfMonad___redArg(v___x_2062_, v___x_2063_);
    v___x_24871__overap_2065_ = lean_panic_fn_borrowed(v___x_2064_, v_msg_2028_);
    lean_dec(v___x_2064_);
    v___x_2066_ = lean_box((v___y_2030_) as usize);
    v___x_2067_ = lean_apply_3(
        v___x_24871__overap_2065_,
        v___y_2029_,
        v___x_2066_,
        v___y_2031_,
    );
    return v___x_2067_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13___boxed(
    mut v_msg_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
    mut v___y_2070_: *mut LeanObject,
    mut v___y_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_25743__boxed_2072_: u8 = 0;
    let mut v_res_2073_: *mut LeanObject = core::ptr::null_mut();
    v___y_25743__boxed_2072_ = (lean_unbox(v___y_2070_) as u8);
    v_res_2073_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(v_msg_2068_, v___y_2069_, v___y_25743__boxed_2072_, v___y_2071_);
    return v_res_2073_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    v___x_2077_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__2;
    v___x_2078_ = lean_unsigned_to_nat(67);
    v___x_2079_ = lean_unsigned_to_nat(35);
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
    mut v_minIndex_2083_: *mut LeanObject,
    mut v___x_2084_: *mut LeanObject,
    mut v___x_2085_: *mut LeanObject,
    mut v_start_2086_: *mut LeanObject,
    mut v_xs_2087_: *mut LeanObject,
    mut v___x_2088_: *mut LeanObject,
    mut v_e_2089_: *mut LeanObject,
    mut v_offset_2090_: *mut LeanObject,
    mut v_a_2091_: *mut LeanObject,
    mut v_a_2092_: u8,
    mut v_a_2093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v_fst_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2111_: u8 = 0;
    let mut v___y_2113_: u8 = 0;
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: u8 = 0;
    let mut v___x_2122_: u8 = 0;
    let mut v_isSharedCheck_2123_: u8 = 0;
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_binderName_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2128_: u8 = 0;
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2141_: u8 = 0;
    let mut v_fst_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___y_2148_: u8 = 0;
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: u8 = 0;
    let mut v___x_2157_: u8 = 0;
    let mut v_isSharedCheck_2158_: u8 = 0;
    let mut v_isSharedCheck_2159_: u8 = 0;
    let mut v_binderName_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2163_: u8 = 0;
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2176_: u8 = 0;
    let mut v_fst_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2181_: u8 = 0;
    let mut v___y_2183_: u8 = 0;
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v___x_2192_: u8 = 0;
    let mut v_isSharedCheck_2193_: u8 = 0;
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut v_declName_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_2199_: u8 = 0;
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v_fst_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___y_2224_: u8 = 0;
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: u8 = 0;
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_data_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v_fst_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2259_: u8 = 0;
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v_typeName_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2269_: u8 = 0;
    let mut v_fst_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2275_: u8 = 0;
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2283_: u8 = 0;
    let mut v_isSharedCheck_2284_: u8 = 0;
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_2089_) {
                5 => {
                    v_fn_2094_ = lean_ctor_get(v_e_2089_, 0);
                    v_arg_2095_ = lean_ctor_get(v_e_2089_, 1);
                    lean_inc(v_offset_2090_);
                    lean_inc_ref(v_fn_2094_);
                    lean_inc_ref(v___x_2084_);
                    v___x_2096_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_fn_2094_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2097_ = lean_ctor_get(v___x_2096_, 0);
                    lean_inc(v_fst_2097_);
                    v_snd_2098_ = lean_ctor_get(v___x_2096_, 1);
                    lean_inc(v_snd_2098_);
                    lean_dec_ref(v___x_2096_);
                    v_fst_2099_ = lean_ctor_get(v_fst_2097_, 0);
                    lean_inc(v_fst_2099_);
                    v_snd_2100_ = lean_ctor_get(v_fst_2097_, 1);
                    lean_inc(v_snd_2100_);
                    lean_dec(v_fst_2097_);
                    lean_inc_ref(v_arg_2095_);
                    v___x_2101_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_arg_2095_, v_offset_2090_, v_snd_2100_, v_a_2092_, v_snd_2098_);
                    v_fst_2102_ = lean_ctor_get(v___x_2101_, 0);
                    v_snd_2103_ = lean_ctor_get(v___x_2101_, 1);
                    v_isSharedCheck_2124_ = (!lean_is_exclusive(v___x_2101_)) as u8;
                    if v_isSharedCheck_2124_ == 0 {
                        v___x_2105_ = v___x_2101_;
                        v_isShared_2106_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2103_);
                        lean_inc(v_fst_2102_);
                        lean_dec(v___x_2101_);
                        v___x_2105_ = lean_box(0);
                        v_isShared_2106_ = v_isSharedCheck_2124_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_2125_ = lean_ctor_get(v_e_2089_, 0);
                    v_binderType_2126_ = lean_ctor_get(v_e_2089_, 1);
                    v_body_2127_ = lean_ctor_get(v_e_2089_, 2);
                    v_binderInfo_2128_ = lean_ctor_get_uint8(
                        v_e_2089_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_2090_);
                    lean_inc_ref(v_binderType_2126_);
                    lean_inc_ref(v___x_2084_);
                    v___x_2129_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_binderType_2126_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2130_ = lean_ctor_get(v___x_2129_, 0);
                    lean_inc(v_fst_2130_);
                    v_snd_2131_ = lean_ctor_get(v___x_2129_, 1);
                    lean_inc(v_snd_2131_);
                    lean_dec_ref(v___x_2129_);
                    v_fst_2132_ = lean_ctor_get(v_fst_2130_, 0);
                    lean_inc(v_fst_2132_);
                    v_snd_2133_ = lean_ctor_get(v_fst_2130_, 1);
                    lean_inc(v_snd_2133_);
                    lean_dec(v_fst_2130_);
                    v___x_2134_ = lean_unsigned_to_nat(1);
                    v___x_2135_ = lean_nat_add(v_offset_2090_, v___x_2134_);
                    lean_dec(v_offset_2090_);
                    lean_inc_ref(v_body_2127_);
                    v___x_2136_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_body_2127_, v___x_2135_, v_snd_2133_, v_a_2092_, v_snd_2131_);
                    v_fst_2137_ = lean_ctor_get(v___x_2136_, 0);
                    v_snd_2138_ = lean_ctor_get(v___x_2136_, 1);
                    v_isSharedCheck_2159_ = (!lean_is_exclusive(v___x_2136_)) as u8;
                    if v_isSharedCheck_2159_ == 0 {
                        v___x_2140_ = v___x_2136_;
                        v_isShared_2141_ = v_isSharedCheck_2159_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_2138_);
                        lean_inc(v_fst_2137_);
                        lean_dec(v___x_2136_);
                        v___x_2140_ = lean_box(0);
                        v_isShared_2141_ = v_isSharedCheck_2159_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_2160_ = lean_ctor_get(v_e_2089_, 0);
                    v_binderType_2161_ = lean_ctor_get(v_e_2089_, 1);
                    v_body_2162_ = lean_ctor_get(v_e_2089_, 2);
                    v_binderInfo_2163_ = lean_ctor_get_uint8(
                        v_e_2089_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_2090_);
                    lean_inc_ref(v_binderType_2161_);
                    lean_inc_ref(v___x_2084_);
                    v___x_2164_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_binderType_2161_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2165_ = lean_ctor_get(v___x_2164_, 0);
                    lean_inc(v_fst_2165_);
                    v_snd_2166_ = lean_ctor_get(v___x_2164_, 1);
                    lean_inc(v_snd_2166_);
                    lean_dec_ref(v___x_2164_);
                    v_fst_2167_ = lean_ctor_get(v_fst_2165_, 0);
                    lean_inc(v_fst_2167_);
                    v_snd_2168_ = lean_ctor_get(v_fst_2165_, 1);
                    lean_inc(v_snd_2168_);
                    lean_dec(v_fst_2165_);
                    v___x_2169_ = lean_unsigned_to_nat(1);
                    v___x_2170_ = lean_nat_add(v_offset_2090_, v___x_2169_);
                    lean_dec(v_offset_2090_);
                    lean_inc_ref(v_body_2162_);
                    v___x_2171_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_body_2162_, v___x_2170_, v_snd_2168_, v_a_2092_, v_snd_2166_);
                    v_fst_2172_ = lean_ctor_get(v___x_2171_, 0);
                    v_snd_2173_ = lean_ctor_get(v___x_2171_, 1);
                    v_isSharedCheck_2194_ = (!lean_is_exclusive(v___x_2171_)) as u8;
                    if v_isSharedCheck_2194_ == 0 {
                        v___x_2175_ = v___x_2171_;
                        v_isShared_2176_ = v_isSharedCheck_2194_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_snd_2173_);
                        lean_inc(v_fst_2172_);
                        lean_dec(v___x_2171_);
                        v___x_2175_ = lean_box(0);
                        v_isShared_2176_ = v_isSharedCheck_2194_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_2195_ = lean_ctor_get(v_e_2089_, 0);
                    v_type_2196_ = lean_ctor_get(v_e_2089_, 1);
                    v_value_2197_ = lean_ctor_get(v_e_2089_, 2);
                    v_body_2198_ = lean_ctor_get(v_e_2089_, 3);
                    v_nondep_2199_ = lean_ctor_get_uint8(
                        v_e_2089_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_inc_n(v_offset_2090_, 2);
                    lean_inc_ref(v_type_2196_);
                    lean_inc_ref_n(v___x_2084_, 2);
                    v___x_2200_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_type_2196_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2201_ = lean_ctor_get(v___x_2200_, 0);
                    lean_inc(v_fst_2201_);
                    v_snd_2202_ = lean_ctor_get(v___x_2200_, 1);
                    lean_inc(v_snd_2202_);
                    lean_dec_ref(v___x_2200_);
                    v_fst_2203_ = lean_ctor_get(v_fst_2201_, 0);
                    lean_inc(v_fst_2203_);
                    v_snd_2204_ = lean_ctor_get(v_fst_2201_, 1);
                    lean_inc(v_snd_2204_);
                    lean_dec(v_fst_2201_);
                    lean_inc_ref(v_value_2197_);
                    v___x_2205_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_value_2197_, v_offset_2090_, v_snd_2204_, v_a_2092_, v_snd_2202_);
                    v_fst_2206_ = lean_ctor_get(v___x_2205_, 0);
                    lean_inc(v_fst_2206_);
                    v_snd_2207_ = lean_ctor_get(v___x_2205_, 1);
                    lean_inc(v_snd_2207_);
                    lean_dec_ref(v___x_2205_);
                    v_fst_2208_ = lean_ctor_get(v_fst_2206_, 0);
                    lean_inc(v_fst_2208_);
                    v_snd_2209_ = lean_ctor_get(v_fst_2206_, 1);
                    lean_inc(v_snd_2209_);
                    lean_dec(v_fst_2206_);
                    v___x_2210_ = lean_unsigned_to_nat(1);
                    v___x_2211_ = lean_nat_add(v_offset_2090_, v___x_2210_);
                    lean_dec(v_offset_2090_);
                    lean_inc_ref(v_body_2198_);
                    v___x_2212_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_body_2198_, v___x_2211_, v_snd_2209_, v_a_2092_, v_snd_2207_);
                    v_fst_2213_ = lean_ctor_get(v___x_2212_, 0);
                    v_snd_2214_ = lean_ctor_get(v___x_2212_, 1);
                    v_isSharedCheck_2237_ = (!lean_is_exclusive(v___x_2212_)) as u8;
                    if v_isSharedCheck_2237_ == 0 {
                        v___x_2216_ = v___x_2212_;
                        v_isShared_2217_ = v_isSharedCheck_2237_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_snd_2214_);
                        lean_inc(v_fst_2213_);
                        lean_dec(v___x_2212_);
                        v___x_2216_ = lean_box(0);
                        v_isShared_2217_ = v_isSharedCheck_2237_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_2238_ = lean_ctor_get(v_e_2089_, 0);
                    v_expr_2239_ = lean_ctor_get(v_e_2089_, 1);
                    lean_inc_ref(v_expr_2239_);
                    v___x_2240_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_expr_2239_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2241_ = lean_ctor_get(v___x_2240_, 0);
                    v_snd_2242_ = lean_ctor_get(v___x_2240_, 1);
                    v_isSharedCheck_2260_ = (!lean_is_exclusive(v___x_2240_)) as u8;
                    if v_isSharedCheck_2260_ == 0 {
                        v___x_2244_ = v___x_2240_;
                        v_isShared_2245_ = v_isSharedCheck_2260_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_snd_2242_);
                        lean_inc(v_fst_2241_);
                        lean_dec(v___x_2240_);
                        v___x_2244_ = lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2260_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_2261_ = lean_ctor_get(v_e_2089_, 0);
                    v_idx_2262_ = lean_ctor_get(v_e_2089_, 1);
                    v_struct_2263_ = lean_ctor_get(v_e_2089_, 2);
                    lean_inc_ref(v_struct_2263_);
                    v___x_2264_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2083_, v___x_2084_, v___x_2085_, v_start_2086_, v_xs_2087_, v___x_2088_, v_struct_2263_, v_offset_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
                    v_fst_2265_ = lean_ctor_get(v___x_2264_, 0);
                    v_snd_2266_ = lean_ctor_get(v___x_2264_, 1);
                    v_isSharedCheck_2284_ = (!lean_is_exclusive(v___x_2264_)) as u8;
                    if v_isSharedCheck_2284_ == 0 {
                        v___x_2268_ = v___x_2264_;
                        v_isShared_2269_ = v_isSharedCheck_2284_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_snd_2266_);
                        lean_inc(v_fst_2265_);
                        lean_dec(v___x_2264_);
                        v___x_2268_ = lean_box(0);
                        v_isShared_2269_ = v_isSharedCheck_2284_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_offset_2090_);
                    lean_dec_ref(v_e_2089_);
                    lean_dec_ref(v___x_2084_);
                    v___x_2285_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___closed__3);
                    v___x_2286_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__13(v___x_2285_, v_a_2091_, v_a_2092_, v_a_2093_);
                    return v___x_2286_;
                }
            },
            1 => {
                v_fst_2107_ = lean_ctor_get(v_fst_2102_, 0);
                v_snd_2108_ = lean_ctor_get(v_fst_2102_, 1);
                v_isSharedCheck_2123_ = (!lean_is_exclusive(v_fst_2102_)) as u8;
                if v_isSharedCheck_2123_ == 0 {
                    v___x_2110_ = v_fst_2102_;
                    v_isShared_2111_ = v_isSharedCheck_2123_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2108_);
                    lean_inc(v_fst_2107_);
                    lean_dec(v_fst_2102_);
                    v___x_2110_ = lean_box(0);
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
                    lean_del_object(v___x_2110_);
                    lean_del_object(v___x_2105_);
                    lean_dec_ref_known(v_e_2089_, 2);
                    v___x_2114_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__7(v_fst_2099_, v_fst_2107_, v_snd_2108_, v_a_2092_, v_snd_2103_);
                    return v___x_2114_;
                } else {
                    lean_dec(v_fst_2107_);
                    lean_dec(v_fst_2099_);
                    if v_isShared_2111_ == 0 {
                        lean_ctor_set(v___x_2110_, 0, v_e_2089_);
                        v___x_2116_ = v___x_2110_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_e_2089_);
                        lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_snd_2108_);
                        v___x_2116_ = v_reuseFailAlloc_2120_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2106_ == 0 {
                    lean_ctor_set(v___x_2105_, 0, v___x_2116_);
                    v___x_2118_ = v___x_2105_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
                    lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_snd_2103_);
                    v___x_2118_ = v_reuseFailAlloc_2119_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2118_;
            }
            6 => {
                v_fst_2142_ = lean_ctor_get(v_fst_2137_, 0);
                v_snd_2143_ = lean_ctor_get(v_fst_2137_, 1);
                v_isSharedCheck_2158_ = (!lean_is_exclusive(v_fst_2137_)) as u8;
                if v_isSharedCheck_2158_ == 0 {
                    v___x_2145_ = v_fst_2137_;
                    v_isShared_2146_ = v_isSharedCheck_2158_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_2143_);
                    lean_inc(v_fst_2142_);
                    lean_dec(v_fst_2137_);
                    v___x_2145_ = lean_box(0);
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
                    lean_inc(v_binderName_2125_);
                    lean_del_object(v___x_2145_);
                    lean_del_object(v___x_2140_);
                    lean_dec_ref_known(v_e_2089_, 3);
                    v___x_2149_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__8(v_binderName_2125_, v_binderInfo_2128_, v_fst_2132_, v_fst_2142_, v_snd_2143_, v_a_2092_, v_snd_2138_);
                    return v___x_2149_;
                } else {
                    lean_dec(v_fst_2142_);
                    lean_dec(v_fst_2132_);
                    if v_isShared_2146_ == 0 {
                        lean_ctor_set(v___x_2145_, 0, v_e_2089_);
                        v___x_2151_ = v___x_2145_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_e_2089_);
                        lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_snd_2143_);
                        v___x_2151_ = v_reuseFailAlloc_2155_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2141_ == 0 {
                    lean_ctor_set(v___x_2140_, 0, v___x_2151_);
                    v___x_2153_ = v___x_2140_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
                    lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_snd_2138_);
                    v___x_2153_ = v_reuseFailAlloc_2154_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2153_;
            }
            11 => {
                v_fst_2177_ = lean_ctor_get(v_fst_2172_, 0);
                v_snd_2178_ = lean_ctor_get(v_fst_2172_, 1);
                v_isSharedCheck_2193_ = (!lean_is_exclusive(v_fst_2172_)) as u8;
                if v_isSharedCheck_2193_ == 0 {
                    v___x_2180_ = v_fst_2172_;
                    v_isShared_2181_ = v_isSharedCheck_2193_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_snd_2178_);
                    lean_inc(v_fst_2177_);
                    lean_dec(v_fst_2172_);
                    v___x_2180_ = lean_box(0);
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
                    lean_inc(v_binderName_2160_);
                    lean_del_object(v___x_2180_);
                    lean_del_object(v___x_2175_);
                    lean_dec_ref_known(v_e_2089_, 3);
                    v___x_2184_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__9(v_binderName_2160_, v_binderInfo_2163_, v_fst_2167_, v_fst_2177_, v_snd_2178_, v_a_2092_, v_snd_2173_);
                    return v___x_2184_;
                } else {
                    lean_dec(v_fst_2177_);
                    lean_dec(v_fst_2167_);
                    if v_isShared_2181_ == 0 {
                        lean_ctor_set(v___x_2180_, 0, v_e_2089_);
                        v___x_2186_ = v___x_2180_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_e_2089_);
                        lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_snd_2178_);
                        v___x_2186_ = v_reuseFailAlloc_2190_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2176_ == 0 {
                    lean_ctor_set(v___x_2175_, 0, v___x_2186_);
                    v___x_2188_ = v___x_2175_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_snd_2173_);
                    v___x_2188_ = v_reuseFailAlloc_2189_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2188_;
            }
            16 => {
                v_fst_2218_ = lean_ctor_get(v_fst_2213_, 0);
                v_snd_2219_ = lean_ctor_get(v_fst_2213_, 1);
                v_isSharedCheck_2236_ = (!lean_is_exclusive(v_fst_2213_)) as u8;
                if v_isSharedCheck_2236_ == 0 {
                    v___x_2221_ = v_fst_2213_;
                    v_isShared_2222_ = v_isSharedCheck_2236_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_snd_2219_);
                    lean_inc(v_fst_2218_);
                    lean_dec(v_fst_2213_);
                    v___x_2221_ = lean_box(0);
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
                    lean_inc(v_declName_2195_);
                    lean_del_object(v___x_2221_);
                    lean_del_object(v___x_2216_);
                    lean_dec_ref_known(v_e_2089_, 4);
                    v___x_2225_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_declName_2195_, v_fst_2203_, v_fst_2208_, v_fst_2218_, v_nondep_2199_, v_snd_2219_, v_a_2092_, v_snd_2214_);
                    return v___x_2225_;
                } else {
                    v___x_2226_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_2198_,
                            v_fst_2218_,
                        );
                    if v___x_2226_ == 0 {
                        lean_inc(v_declName_2195_);
                        lean_del_object(v___x_2221_);
                        lean_del_object(v___x_2216_);
                        lean_dec_ref_known(v_e_2089_, 4);
                        v___x_2227_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__10(v_declName_2195_, v_fst_2203_, v_fst_2208_, v_fst_2218_, v_nondep_2199_, v_snd_2219_, v_a_2092_, v_snd_2214_);
                        return v___x_2227_;
                    } else {
                        lean_dec(v_fst_2218_);
                        lean_dec(v_fst_2208_);
                        lean_dec(v_fst_2203_);
                        if v_isShared_2222_ == 0 {
                            lean_ctor_set(v___x_2221_, 0, v_e_2089_);
                            v___x_2229_ = v___x_2221_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_e_2089_);
                            lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_snd_2219_);
                            v___x_2229_ = v_reuseFailAlloc_2233_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_2217_ == 0 {
                    lean_ctor_set(v___x_2216_, 0, v___x_2229_);
                    v___x_2231_ = v___x_2216_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
                    lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_snd_2214_);
                    v___x_2231_ = v_reuseFailAlloc_2232_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2231_;
            }
            21 => {
                v_fst_2246_ = lean_ctor_get(v_fst_2241_, 0);
                v_snd_2247_ = lean_ctor_get(v_fst_2241_, 1);
                v_isSharedCheck_2259_ = (!lean_is_exclusive(v_fst_2241_)) as u8;
                if v_isSharedCheck_2259_ == 0 {
                    v___x_2249_ = v_fst_2241_;
                    v_isShared_2250_ = v_isSharedCheck_2259_;
                    state = 22;
                    continue;
                } else {
                    lean_inc(v_snd_2247_);
                    lean_inc(v_fst_2246_);
                    lean_dec(v_fst_2241_);
                    v___x_2249_ = lean_box(0);
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
                    lean_inc(v_data_2238_);
                    lean_del_object(v___x_2249_);
                    lean_del_object(v___x_2244_);
                    lean_dec_ref_known(v_e_2089_, 2);
                    v___x_2252_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__11(v_data_2238_, v_fst_2246_, v_snd_2247_, v_a_2092_, v_snd_2242_);
                    return v___x_2252_;
                } else {
                    lean_dec(v_fst_2246_);
                    if v_isShared_2250_ == 0 {
                        lean_ctor_set(v___x_2249_, 0, v_e_2089_);
                        v___x_2254_ = v___x_2249_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_e_2089_);
                        lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_snd_2247_);
                        v___x_2254_ = v_reuseFailAlloc_2258_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_2245_ == 0 {
                    lean_ctor_set(v___x_2244_, 0, v___x_2254_);
                    v___x_2256_ = v___x_2244_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2254_);
                    lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_snd_2242_);
                    v___x_2256_ = v_reuseFailAlloc_2257_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2256_;
            }
            25 => {
                v_fst_2270_ = lean_ctor_get(v_fst_2265_, 0);
                v_snd_2271_ = lean_ctor_get(v_fst_2265_, 1);
                v_isSharedCheck_2283_ = (!lean_is_exclusive(v_fst_2265_)) as u8;
                if v_isSharedCheck_2283_ == 0 {
                    v___x_2273_ = v_fst_2265_;
                    v_isShared_2274_ = v_isSharedCheck_2283_;
                    state = 26;
                    continue;
                } else {
                    lean_inc(v_snd_2271_);
                    lean_inc(v_fst_2270_);
                    lean_dec(v_fst_2265_);
                    v___x_2273_ = lean_box(0);
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
                    lean_inc(v_idx_2262_);
                    lean_inc(v_typeName_2261_);
                    lean_del_object(v___x_2273_);
                    lean_del_object(v___x_2268_);
                    lean_dec_ref_known(v_e_2089_, 3);
                    v___x_2276_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__12(v_typeName_2261_, v_idx_2262_, v_fst_2270_, v_snd_2271_, v_a_2092_, v_snd_2266_);
                    return v___x_2276_;
                } else {
                    lean_dec(v_fst_2270_);
                    if v_isShared_2274_ == 0 {
                        lean_ctor_set(v___x_2273_, 0, v_e_2089_);
                        v___x_2278_ = v___x_2273_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_e_2089_);
                        lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_snd_2271_);
                        v___x_2278_ = v_reuseFailAlloc_2282_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2269_ == 0 {
                    lean_ctor_set(v___x_2268_, 0, v___x_2278_);
                    v___x_2280_ = v___x_2268_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
                    lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_snd_2266_);
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
    mut v_minIndex_2287_: *mut LeanObject,
    mut v___x_2288_: *mut LeanObject,
    mut v___x_2289_: *mut LeanObject,
    mut v_start_2290_: *mut LeanObject,
    mut v_xs_2291_: *mut LeanObject,
    mut v___x_2292_: *mut LeanObject,
    mut v_e_2293_: *mut LeanObject,
    mut v_offset_2294_: *mut LeanObject,
    mut v_a_2295_: *mut LeanObject,
    mut v_a_2296_: u8,
    mut v_a_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxIndex_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: u8 = 0;
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_offset_2294_);
                lean_inc_ref(v_e_2293_);
                v_key_2298_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_key_2298_, 0, v_e_2293_);
                lean_ctor_set(v_key_2298_, 1, v_offset_2294_);
                v___x_2324_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_a_2295_, v_key_2298_);
                if lean_obj_tag(v___x_2324_) == 1 {
                    lean_dec_ref_known(v_key_2298_, 2);
                    lean_dec(v_offset_2294_);
                    lean_dec_ref(v_e_2293_);
                    lean_dec_ref(v___x_2288_);
                    v_val_2325_ = lean_ctor_get(v___x_2324_, 0);
                    lean_inc(v_val_2325_);
                    lean_dec_ref_known(v___x_2324_, 1);
                    v___x_2326_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2326_, 0, v_val_2325_);
                    lean_ctor_set(v___x_2326_, 1, v_a_2295_);
                    v___x_2327_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2327_, 0, v___x_2326_);
                    lean_ctor_set(v___x_2327_, 1, v_a_2297_);
                    return v___x_2327_;
                } else {
                    lean_dec(v___x_2324_);
                    match lean_obj_tag(v_e_2293_) {
                        1 => {
                            lean_dec_ref(v___x_2288_);
                            v_fvarId_2328_ = lean_ctor_get(v_e_2293_, 0);
                            v___x_2329_ = lean_unsigned_to_nat(0);
                            v___x_2330_ = lean_unsigned_to_nat(1);
                            v___x_2331_ = lean_nat_sub(v___x_2289_, v___x_2330_);
                            v___x_2332_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_2290_, v_xs_2291_, v_fvarId_2328_, v___x_2329_, v___x_2331_);
                            if lean_obj_tag(v___x_2332_) == 1 {
                                lean_dec_ref_known(v_e_2293_, 1);
                                v_val_2333_ = lean_ctor_get(v___x_2332_, 0);
                                lean_inc(v_val_2333_);
                                lean_dec_ref_known(v___x_2332_, 1);
                                v___x_2334_ = lean_nat_add(v_offset_2294_, v_val_2333_);
                                lean_dec(v_val_2333_);
                                lean_dec(v_offset_2294_);
                                v___x_2335_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v___x_2334_, v_a_2297_);
                                v_fst_2336_ = lean_ctor_get(v___x_2335_, 0);
                                lean_inc(v_fst_2336_);
                                v_snd_2337_ = lean_ctor_get(v___x_2335_, 1);
                                lean_inc(v_snd_2337_);
                                lean_dec_ref(v___x_2335_);
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
                                lean_dec(v___x_2332_);
                                lean_dec(v_offset_2294_);
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
                            lean_dec(v_offset_2294_);
                            lean_dec_ref(v___x_2288_);
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
                            lean_dec(v_offset_2294_);
                            lean_dec_ref(v___x_2288_);
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
                            lean_dec(v_offset_2294_);
                            lean_dec_ref(v___x_2288_);
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
                            lean_dec(v_offset_2294_);
                            lean_dec_ref(v___x_2288_);
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
                            lean_dec(v_offset_2294_);
                            lean_dec_ref(v___x_2288_);
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
                                lean_dec(v_offset_2294_);
                                lean_dec_ref(v___x_2288_);
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
                                if lean_obj_tag(v___x_2347_) == 1 {
                                    v_val_2348_ = lean_ctor_get(v___x_2347_, 0);
                                    lean_inc(v_val_2348_);
                                    lean_dec_ref_known(v___x_2347_, 1);
                                    if lean_obj_tag(v_val_2348_) == 0 {
                                        v___x_2349_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                                        v___x_2350_ = l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__4(v___x_2349_);
                                        v___y_2319_ = v___x_2350_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v_val_2351_ = lean_ctor_get(v_val_2348_, 0);
                                        lean_inc(v_val_2351_);
                                        lean_dec_ref_known(v_val_2348_, 1);
                                        v___y_2319_ = v_val_2351_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_2347_);
                                    v_snd_2300_ = v_a_2297_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => match lean_obj_tag(v_e_2293_) {
                9 => {
                    lean_dec(v_offset_2294_);
                    lean_dec_ref(v___x_2288_);
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
                    lean_dec(v_offset_2294_);
                    lean_dec_ref(v___x_2288_);
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
                    lean_dec(v_offset_2294_);
                    lean_dec_ref(v___x_2288_);
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
                    lean_dec(v_offset_2294_);
                    lean_dec_ref(v___x_2288_);
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
                    lean_dec(v_offset_2294_);
                    lean_dec_ref(v___x_2288_);
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
                    lean_dec(v_offset_2294_);
                    lean_dec_ref(v___x_2288_);
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
                    v_fst_2308_ = lean_ctor_get(v___x_2307_, 0);
                    lean_inc(v_fst_2308_);
                    v_snd_2309_ = lean_ctor_get(v___x_2307_, 1);
                    lean_inc(v_snd_2309_);
                    lean_dec_ref(v___x_2307_);
                    v_fst_2310_ = lean_ctor_get(v_fst_2308_, 0);
                    lean_inc(v_fst_2310_);
                    v_snd_2311_ = lean_ctor_get(v_fst_2308_, 1);
                    lean_inc(v_snd_2311_);
                    lean_dec(v_fst_2308_);
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
                lean_dec_ref(v___y_2314_);
                v___x_2316_ = lean_nat_dec_lt(v_maxIndex_2315_, v_minIndex_2287_);
                lean_dec(v_maxIndex_2315_);
                if v___x_2316_ == 0 {
                    v_snd_2300_ = v_a_2297_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_offset_2294_);
                    lean_dec_ref(v___x_2288_);
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
                lean_inc_ref(v___x_2288_);
                v___x_2320_ = lean_local_ctx_find(v___x_2288_, v___y_2319_);
                if lean_obj_tag(v___x_2320_) == 0 {
                    v___x_2321_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                    v___x_2322_ =
                        l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_2321_);
                    v___y_2314_ = v___x_2322_;
                    state = 2;
                    continue;
                } else {
                    v_val_2323_ = lean_ctor_get(v___x_2320_, 0);
                    lean_inc(v_val_2323_);
                    lean_dec_ref_known(v___x_2320_, 1);
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
    mut v_minIndex_2352_: *mut LeanObject,
    mut v___x_2353_: *mut LeanObject,
    mut v___x_2354_: *mut LeanObject,
    mut v_start_2355_: *mut LeanObject,
    mut v_xs_2356_: *mut LeanObject,
    mut v___x_2357_: *mut LeanObject,
    mut v_e_2358_: *mut LeanObject,
    mut v_offset_2359_: *mut LeanObject,
    mut v_a_2360_: *mut LeanObject,
    mut v_a_2361_: *mut LeanObject,
    mut v_a_2362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2363_: u8 = 0;
    let mut v_res_2364_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2363_ = (lean_unbox(v_a_2361_) as u8);
    v_res_2364_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6(v_minIndex_2352_, v___x_2353_, v___x_2354_, v_start_2355_, v_xs_2356_, v___x_2357_, v_e_2358_, v_offset_2359_, v_a_2360_, v_a_boxed_2363_, v_a_2362_);
    lean_dec_ref(v___x_2357_);
    lean_dec_ref(v_xs_2356_);
    lean_dec(v_start_2355_);
    lean_dec(v___x_2354_);
    lean_dec(v_minIndex_2352_);
    return v_res_2364_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5___boxed(
    mut v_minIndex_2365_: *mut LeanObject,
    mut v___x_2366_: *mut LeanObject,
    mut v___x_2367_: *mut LeanObject,
    mut v_start_2368_: *mut LeanObject,
    mut v_xs_2369_: *mut LeanObject,
    mut v___x_2370_: *mut LeanObject,
    mut v_e_2371_: *mut LeanObject,
    mut v_offset_2372_: *mut LeanObject,
    mut v_a_2373_: *mut LeanObject,
    mut v_a_2374_: *mut LeanObject,
    mut v_a_2375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2376_: u8 = 0;
    let mut v_res_2377_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2376_ = (lean_unbox(v_a_2374_) as u8);
    v_res_2377_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v_minIndex_2365_, v___x_2366_, v___x_2367_, v_start_2368_, v_xs_2369_, v___x_2370_, v_e_2371_, v_offset_2372_, v_a_2373_, v_a_boxed_2376_, v_a_2375_);
    lean_dec_ref(v___x_2370_);
    lean_dec_ref(v_xs_2369_);
    lean_dec(v_start_2368_);
    lean_dec(v___x_2367_);
    lean_dec(v_minIndex_2365_);
    return v_res_2377_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    v___x_2378_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_abstractFVarsRange_spec__0(
        lean_box(0),
    );
    return v___x_2378_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVarsRange___redArg(
    mut v_e_2379_: *mut LeanObject,
    mut v_start_2380_: *mut LeanObject,
    mut v_xs_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
    mut v_a_2383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2402_: u8 = 0;
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2405_: u8 = 0;
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2424_: u8 = 0;
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2427_: u8 = 0;
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2433_: u8 = 0;
    let mut v_unused_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2437_: u8 = 0;
    let mut v___y_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxIndex_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: u8 = 0;
    let mut v___y_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minIndex_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2385_ = l_Lean_Expr_hasFVar(v_e_2379_);
                if v___x_2385_ == 0 {
                    v___x_2386_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2386_, 0, v_e_2379_);
                    return v___x_2386_;
                } else {
                    v___x_2387_ = lean_array_get_size(v_xs_2381_);
                    v___x_2388_ = lean_nat_dec_lt(v_start_2380_, v___x_2387_);
                    if v___x_2388_ == 0 {
                        v___x_2389_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2389_, 0, v_e_2379_);
                        return v___x_2389_;
                    } else {
                        v___x_2390_ = lean_st_ref_get(v_a_2382_);
                        v___x_2391_ = lean_st_ref_take(v_a_2382_);
                        v_share_2392_ = lean_ctor_get(v___x_2391_, 0);
                        v_maxFVar_2393_ = lean_ctor_get(v___x_2391_, 1);
                        v_proofInstInfo_2394_ = lean_ctor_get(v___x_2391_, 2);
                        v_inferType_2395_ = lean_ctor_get(v___x_2391_, 3);
                        v_getLevel_2396_ = lean_ctor_get(v___x_2391_, 4);
                        v_congrInfo_2397_ = lean_ctor_get(v___x_2391_, 5);
                        v_defEqI_2398_ = lean_ctor_get(v___x_2391_, 6);
                        v_extensions_2399_ = lean_ctor_get(v___x_2391_, 7);
                        v_issues_2400_ = lean_ctor_get(v___x_2391_, 8);
                        v_canon_2401_ = lean_ctor_get(v___x_2391_, 9);
                        v_debug_2402_ = lean_ctor_get_uint8(
                            v___x_2391_,
                            (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        );
                        v_isSharedCheck_2486_ = (!lean_is_exclusive(v___x_2391_)) as u8;
                        if v_isSharedCheck_2486_ == 0 {
                            v___x_2404_ = v___x_2391_;
                            v_isShared_2405_ = v_isSharedCheck_2486_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_canon_2401_);
                            lean_inc(v_issues_2400_);
                            lean_inc(v_extensions_2399_);
                            lean_inc(v_defEqI_2398_);
                            lean_inc(v_congrInfo_2397_);
                            lean_inc(v_getLevel_2396_);
                            lean_inc(v_inferType_2395_);
                            lean_inc(v_proofInstInfo_2394_);
                            lean_inc(v_maxFVar_2393_);
                            lean_inc(v_share_2392_);
                            lean_dec(v___x_2391_);
                            v___x_2404_ = lean_box(0);
                            v_isShared_2405_ = v_isSharedCheck_2486_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2406_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0_once
                    ),
                    _init_l_Lean_Meta_Sym_abstractFVarsRange___redArg___closed__0,
                );
                if v_isShared_2405_ == 0 {
                    lean_ctor_set(v___x_2404_, 0, v___x_2406_);
                    v___x_2408_ = v___x_2404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2406_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_maxFVar_2393_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_proofInstInfo_2394_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_inferType_2395_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 4, v_getLevel_2396_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 5, v_congrInfo_2397_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 6, v_defEqI_2398_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 7, v_extensions_2399_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 8, v_issues_2400_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 9, v_canon_2401_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2485_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
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
                v_lctx_2435_ = lean_ctor_get(v_a_2383_, 2);
                v_maxFVar_2436_ = lean_ctor_get(v___x_2390_, 1);
                lean_inc_ref(v_maxFVar_2436_);
                lean_dec(v___x_2390_);
                v_debug_2437_ = lean_ctor_get_uint8(
                    v___x_2410_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_2410_);
                v___x_2479_ = lean_array_fget_borrowed(v_xs_2381_, v_start_2380_);
                v___x_2480_ = l_Lean_Expr_fvarId_x21(v___x_2479_);
                lean_inc_ref(v_lctx_2435_);
                v___x_2481_ = lean_local_ctx_find(v_lctx_2435_, v___x_2480_);
                if lean_obj_tag(v___x_2481_) == 0 {
                    v___x_2482_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                    v___x_2483_ =
                        l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_2482_);
                    v___y_2463_ = v___x_2483_;
                    state = 9;
                    continue;
                } else {
                    v_val_2484_ = lean_ctor_get(v___x_2481_, 0);
                    lean_inc(v_val_2484_);
                    lean_dec_ref_known(v___x_2481_, 1);
                    v___y_2463_ = v_val_2484_;
                    state = 9;
                    continue;
                }
            }
            3 => {
                v___x_2414_ = lean_st_ref_take(v_a_2382_);
                v_maxFVar_2415_ = lean_ctor_get(v___x_2414_, 1);
                v_proofInstInfo_2416_ = lean_ctor_get(v___x_2414_, 2);
                v_inferType_2417_ = lean_ctor_get(v___x_2414_, 3);
                v_getLevel_2418_ = lean_ctor_get(v___x_2414_, 4);
                v_congrInfo_2419_ = lean_ctor_get(v___x_2414_, 5);
                v_defEqI_2420_ = lean_ctor_get(v___x_2414_, 6);
                v_extensions_2421_ = lean_ctor_get(v___x_2414_, 7);
                v_issues_2422_ = lean_ctor_get(v___x_2414_, 8);
                v_canon_2423_ = lean_ctor_get(v___x_2414_, 9);
                v_debug_2424_ = lean_ctor_get_uint8(
                    v___x_2414_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2433_ = (!lean_is_exclusive(v___x_2414_)) as u8;
                if v_isSharedCheck_2433_ == 0 {
                    v_unused_2434_ = lean_ctor_get(v___x_2414_, 0);
                    lean_dec(v_unused_2434_);
                    v___x_2426_ = v___x_2414_;
                    v_isShared_2427_ = v_isSharedCheck_2433_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_canon_2423_);
                    lean_inc(v_issues_2422_);
                    lean_inc(v_extensions_2421_);
                    lean_inc(v_defEqI_2420_);
                    lean_inc(v_congrInfo_2419_);
                    lean_inc(v_getLevel_2418_);
                    lean_inc(v_inferType_2417_);
                    lean_inc(v_proofInstInfo_2416_);
                    lean_inc(v_maxFVar_2415_);
                    lean_dec(v___x_2414_);
                    v___x_2426_ = lean_box(0);
                    v_isShared_2427_ = v_isSharedCheck_2433_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2427_ == 0 {
                    lean_ctor_set(v___x_2426_, 0, v_snd_2413_);
                    v___x_2429_ = v___x_2426_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_snd_2413_);
                    lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_maxFVar_2415_);
                    lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_proofInstInfo_2416_);
                    lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_inferType_2417_);
                    lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_getLevel_2418_);
                    lean_ctor_set(v_reuseFailAlloc_2432_, 5, v_congrInfo_2419_);
                    lean_ctor_set(v_reuseFailAlloc_2432_, 6, v_defEqI_2420_);
                    lean_ctor_set(v_reuseFailAlloc_2432_, 7, v_extensions_2421_);
                    lean_ctor_set(v_reuseFailAlloc_2432_, 8, v_issues_2422_);
                    lean_ctor_set(v_reuseFailAlloc_2432_, 9, v_canon_2423_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2432_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_2424_,
                    );
                    v___x_2429_ = v_reuseFailAlloc_2432_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2430_ = lean_st_ref_set(v_a_2382_, v___x_2429_);
                v___x_2431_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2431_, 0, v_fst_2412_);
                return v___x_2431_;
            }
            6 => match lean_obj_tag(v_e_2379_) {
                9 => {
                    lean_dec(v___y_2440_);
                    lean_dec(v___y_2439_);
                    lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                2 => {
                    lean_dec(v___y_2440_);
                    lean_dec(v___y_2439_);
                    lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                0 => {
                    lean_dec(v___y_2440_);
                    lean_dec(v___y_2439_);
                    lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                1 => {
                    lean_dec(v___y_2440_);
                    lean_dec(v___y_2439_);
                    lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                4 => {
                    lean_dec(v___y_2440_);
                    lean_dec(v___y_2439_);
                    lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                3 => {
                    lean_dec(v___y_2440_);
                    lean_dec(v___y_2439_);
                    lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_snd_2441_;
                    state = 3;
                    continue;
                }
                _ => {
                    v___x_2442_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___closed__0);
                    lean_inc(v___y_2439_);
                    v___x_2443_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2443_, 0, v___y_2439_);
                    lean_ctor_set(v___x_2443_, 1, v___x_2442_);
                    lean_inc_ref(v_lctx_2435_);
                    v___x_2444_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5(v___y_2440_, v_lctx_2435_, v___x_2387_, v_start_2380_, v_xs_2381_, v_maxFVar_2436_, v_e_2379_, v___y_2439_, v___x_2443_, v_debug_2437_, v_snd_2441_);
                    lean_dec_ref(v_maxFVar_2436_);
                    lean_dec(v___y_2440_);
                    v_fst_2445_ = lean_ctor_get(v___x_2444_, 0);
                    lean_inc(v_fst_2445_);
                    v_snd_2446_ = lean_ctor_get(v___x_2444_, 1);
                    lean_inc(v_snd_2446_);
                    lean_dec_ref(v___x_2444_);
                    v_fst_2447_ = lean_ctor_get(v_fst_2445_, 0);
                    lean_inc(v_fst_2447_);
                    lean_dec(v_fst_2445_);
                    v_fst_2412_ = v_fst_2447_;
                    v_snd_2413_ = v_snd_2446_;
                    state = 3;
                    continue;
                }
            },
            7 => {
                v_maxIndex_2452_ = l_Lean_LocalDecl_index(v___y_2451_);
                lean_dec_ref(v___y_2451_);
                v___x_2453_ = lean_nat_dec_lt(v_maxIndex_2452_, v___y_2450_);
                lean_dec(v_maxIndex_2452_);
                if v___x_2453_ == 0 {
                    v___y_2439_ = v___y_2449_;
                    v___y_2440_ = v___y_2450_;
                    v_snd_2441_ = v_share_2392_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v___y_2450_);
                    lean_dec(v___y_2449_);
                    lean_dec_ref(v_maxFVar_2436_);
                    v_fst_2412_ = v_e_2379_;
                    v_snd_2413_ = v_share_2392_;
                    state = 3;
                    continue;
                }
            }
            8 => {
                lean_inc_ref(v_lctx_2435_);
                v___x_2458_ = lean_local_ctx_find(v_lctx_2435_, v___y_2457_);
                if lean_obj_tag(v___x_2458_) == 0 {
                    v___x_2459_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
                    v___x_2460_ =
                        l_panic___at___00Lean_Meta_Sym_abstractFVarsRange_spec__1(v___x_2459_);
                    v___y_2449_ = v___y_2455_;
                    v___y_2450_ = v___y_2456_;
                    v___y_2451_ = v___x_2460_;
                    state = 7;
                    continue;
                } else {
                    v_val_2461_ = lean_ctor_get(v___x_2458_, 0);
                    lean_inc(v_val_2461_);
                    lean_dec_ref_known(v___x_2458_, 1);
                    v___y_2449_ = v___y_2455_;
                    v___y_2450_ = v___y_2456_;
                    v___y_2451_ = v_val_2461_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v___x_2464_ = lean_unsigned_to_nat(0);
                match lean_obj_tag(v_e_2379_) {
                    1 => {
                        lean_dec_ref(v___y_2463_);
                        lean_dec_ref(v_maxFVar_2436_);
                        v_fvarId_2465_ = lean_ctor_get(v_e_2379_, 0);
                        v___x_2466_ = lean_unsigned_to_nat(1);
                        v___x_2467_ = lean_nat_sub(v___x_2387_, v___x_2466_);
                        v___x_2468_ = l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsRange_go___redArg(v_start_2380_, v_xs_2381_, v_fvarId_2465_, v___x_2464_, v___x_2467_);
                        if lean_obj_tag(v___x_2468_) == 1 {
                            lean_dec_ref_known(v_e_2379_, 1);
                            v_val_2469_ = lean_ctor_get(v___x_2468_, 0);
                            lean_inc(v_val_2469_);
                            lean_dec_ref_known(v___x_2468_, 1);
                            v___x_2470_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_abstractFVarsRange_spec__2___redArg(v_val_2469_, v_share_2392_);
                            v_fst_2471_ = lean_ctor_get(v___x_2470_, 0);
                            lean_inc(v_fst_2471_);
                            v_snd_2472_ = lean_ctor_get(v___x_2470_, 1);
                            lean_inc(v_snd_2472_);
                            lean_dec_ref(v___x_2470_);
                            v_fst_2412_ = v_fst_2471_;
                            v_snd_2413_ = v_snd_2472_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_2468_);
                            v_fst_2412_ = v_e_2379_;
                            v_snd_2413_ = v_share_2392_;
                            state = 3;
                            continue;
                        }
                    }
                    9 => {
                        lean_dec_ref(v___y_2463_);
                        lean_dec_ref(v_maxFVar_2436_);
                        v_fst_2412_ = v_e_2379_;
                        v_snd_2413_ = v_share_2392_;
                        state = 3;
                        continue;
                    }
                    2 => {
                        lean_dec_ref(v___y_2463_);
                        lean_dec_ref(v_maxFVar_2436_);
                        v_fst_2412_ = v_e_2379_;
                        v_snd_2413_ = v_share_2392_;
                        state = 3;
                        continue;
                    }
                    0 => {
                        lean_dec_ref(v___y_2463_);
                        lean_dec_ref(v_maxFVar_2436_);
                        v_fst_2412_ = v_e_2379_;
                        v_snd_2413_ = v_share_2392_;
                        state = 3;
                        continue;
                    }
                    4 => {
                        lean_dec_ref(v___y_2463_);
                        lean_dec_ref(v_maxFVar_2436_);
                        v_fst_2412_ = v_e_2379_;
                        v_snd_2413_ = v_share_2392_;
                        state = 3;
                        continue;
                    }
                    3 => {
                        lean_dec_ref(v___y_2463_);
                        lean_dec_ref(v_maxFVar_2436_);
                        v_fst_2412_ = v_e_2379_;
                        v_snd_2413_ = v_share_2392_;
                        state = 3;
                        continue;
                    }
                    _ => {
                        if v___x_2385_ == 0 {
                            lean_dec_ref(v___y_2463_);
                            lean_dec_ref(v_maxFVar_2436_);
                            v_fst_2412_ = v_e_2379_;
                            v_snd_2413_ = v_share_2392_;
                            state = 3;
                            continue;
                        } else {
                            v_minIndex_2473_ = l_Lean_LocalDecl_index(v___y_2463_);
                            lean_dec_ref(v___y_2463_);
                            v___x_2474_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_maxFVar_2436_, v_e_2379_);
                            if lean_obj_tag(v___x_2474_) == 1 {
                                v_val_2475_ = lean_ctor_get(v___x_2474_, 0);
                                lean_inc(v_val_2475_);
                                lean_dec_ref_known(v___x_2474_, 1);
                                if lean_obj_tag(v_val_2475_) == 0 {
                                    v___x_2476_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3_once), _init_l___private_Lean_Meta_Sym_AbstractS_0__Lean_Meta_Sym_abstractFVarsCore___lam__0___closed__3);
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
                                    v_val_2478_ = lean_ctor_get(v_val_2475_, 0);
                                    lean_inc(v_val_2478_);
                                    lean_dec_ref_known(v_val_2475_, 1);
                                    v___y_2455_ = v___x_2464_;
                                    v___y_2456_ = v_minIndex_2473_;
                                    v___y_2457_ = v_val_2478_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_2474_);
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
    mut v_e_2487_: *mut LeanObject,
    mut v_start_2488_: *mut LeanObject,
    mut v_xs_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
    mut v_a_2491_: *mut LeanObject,
    mut v_a_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2493_: *mut LeanObject = core::ptr::null_mut();
    v_res_2493_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
        v_e_2487_,
        v_start_2488_,
        v_xs_2489_,
        v_a_2490_,
        v_a_2491_,
    );
    lean_dec_ref(v_a_2491_);
    lean_dec(v_a_2490_);
    lean_dec_ref(v_xs_2489_);
    lean_dec(v_start_2488_);
    return v_res_2493_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVarsRange(
    mut v_e_2494_: *mut LeanObject,
    mut v_start_2495_: *mut LeanObject,
    mut v_xs_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
    mut v_a_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
    mut v_a_2501_: *mut LeanObject,
    mut v_a_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_e_2505_: *mut LeanObject,
    mut v_start_2506_: *mut LeanObject,
    mut v_xs_2507_: *mut LeanObject,
    mut v_a_2508_: *mut LeanObject,
    mut v_a_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
    mut v_a_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2515_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2513_);
    lean_dec_ref(v_a_2512_);
    lean_dec(v_a_2511_);
    lean_dec_ref(v_a_2510_);
    lean_dec(v_a_2509_);
    lean_dec_ref(v_a_2508_);
    lean_dec_ref(v_xs_2507_);
    lean_dec(v_start_2506_);
    return v_res_2515_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(
    mut v_00_u03b2_2516_: *mut LeanObject,
    mut v_x_2517_: *mut LeanObject,
    mut v_x_2518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    v___x_2519_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___redArg(v_x_2517_, v_x_2518_);
    return v___x_2519_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3___boxed(
    mut v_00_u03b2_2520_: *mut LeanObject,
    mut v_x_2521_: *mut LeanObject,
    mut v_x_2522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2523_: *mut LeanObject = core::ptr::null_mut();
    v_res_2523_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3(
            v_00_u03b2_2520_,
            v_x_2521_,
            v_x_2522_,
        );
    lean_dec_ref(v_x_2522_);
    lean_dec_ref(v_x_2521_);
    return v_res_2523_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(
    mut v_00_u03b2_2524_: *mut LeanObject,
    mut v_x_2525_: *mut LeanObject,
    mut v_x_2526_: usize,
    mut v_x_2527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    v___x_2528_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___redArg(v_x_2525_, v_x_2526_, v_x_2527_);
    return v___x_2528_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3___boxed(
    mut v_00_u03b2_2529_: *mut LeanObject,
    mut v_x_2530_: *mut LeanObject,
    mut v_x_2531_: *mut LeanObject,
    mut v_x_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26629__boxed_2533_: usize = 0;
    let mut v_res_2534_: *mut LeanObject = core::ptr::null_mut();
    v_x_26629__boxed_2533_ = lean_unbox_usize(v_x_2531_);
    lean_dec(v_x_2531_);
    v_res_2534_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3(v_00_u03b2_2529_, v_x_2530_, v_x_26629__boxed_2533_, v_x_2532_);
    lean_dec_ref(v_x_2532_);
    lean_dec_ref(v_x_2530_);
    return v_res_2534_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(
    mut v_00_u03b2_2535_: *mut LeanObject,
    mut v_keys_2536_: *mut LeanObject,
    mut v_vals_2537_: *mut LeanObject,
    mut v_heq_2538_: *mut LeanObject,
    mut v_i_2539_: *mut LeanObject,
    mut v_k_2540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    v___x_2541_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___redArg(v_keys_2536_, v_vals_2537_, v_i_2539_, v_k_2540_);
    return v___x_2541_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5___boxed(
    mut v_00_u03b2_2542_: *mut LeanObject,
    mut v_keys_2543_: *mut LeanObject,
    mut v_vals_2544_: *mut LeanObject,
    mut v_heq_2545_: *mut LeanObject,
    mut v_i_2546_: *mut LeanObject,
    mut v_k_2547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2548_: *mut LeanObject = core::ptr::null_mut();
    v_res_2548_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_abstractFVarsRange_spec__3_spec__3_spec__5(v_00_u03b2_2542_, v_keys_2543_, v_vals_2544_, v_heq_2545_, v_i_2546_, v_k_2547_);
    lean_dec_ref(v_k_2547_);
    lean_dec_ref(v_vals_2544_);
    lean_dec_ref(v_keys_2543_);
    return v_res_2548_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(
    mut v_00_u03b2_2549_: *mut LeanObject,
    mut v_m_2550_: *mut LeanObject,
    mut v_a_2551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    v___x_2552_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___redArg(v_m_2550_, v_a_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8___boxed(
    mut v_00_u03b2_2553_: *mut LeanObject,
    mut v_m_2554_: *mut LeanObject,
    mut v_a_2555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2556_: *mut LeanObject = core::ptr::null_mut();
    v_res_2556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8(v_00_u03b2_2553_, v_m_2554_, v_a_2555_);
    lean_dec_ref(v_a_2555_);
    lean_dec_ref(v_m_2554_);
    return v_res_2556_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(
    mut v_00_u03b2_2557_: *mut LeanObject,
    mut v_a_2558_: *mut LeanObject,
    mut v_x_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    v___x_2560_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___redArg(v_a_2558_, v_x_2559_);
    return v___x_2560_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16___boxed(
    mut v_00_u03b2_2561_: *mut LeanObject,
    mut v_a_2562_: *mut LeanObject,
    mut v_x_2563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2564_: *mut LeanObject = core::ptr::null_mut();
    v_res_2564_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_abstractFVarsRange_spec__5_spec__6_spec__8_spec__16(v_00_u03b2_2561_, v_a_2562_, v_x_2563_);
    lean_dec(v_x_2563_);
    lean_dec_ref(v_a_2562_);
    return v_res_2564_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVars___redArg(
    mut v_e_2565_: *mut LeanObject,
    mut v_xs_2566_: *mut LeanObject,
    mut v_a_2567_: *mut LeanObject,
    mut v_a_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    v___x_2570_ = lean_unsigned_to_nat(0);
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
    mut v_e_2572_: *mut LeanObject,
    mut v_xs_2573_: *mut LeanObject,
    mut v_a_2574_: *mut LeanObject,
    mut v_a_2575_: *mut LeanObject,
    mut v_a_2576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2577_: *mut LeanObject = core::ptr::null_mut();
    v_res_2577_ =
        l_Lean_Meta_Sym_abstractFVars___redArg(v_e_2572_, v_xs_2573_, v_a_2574_, v_a_2575_);
    lean_dec_ref(v_a_2575_);
    lean_dec(v_a_2574_);
    lean_dec_ref(v_xs_2573_);
    return v_res_2577_;
}
pub unsafe fn l_Lean_Meta_Sym_abstractFVars(
    mut v_e_2578_: *mut LeanObject,
    mut v_xs_2579_: *mut LeanObject,
    mut v_a_2580_: *mut LeanObject,
    mut v_a_2581_: *mut LeanObject,
    mut v_a_2582_: *mut LeanObject,
    mut v_a_2583_: *mut LeanObject,
    mut v_a_2584_: *mut LeanObject,
    mut v_a_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    v___x_2587_ = lean_unsigned_to_nat(0);
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
    mut v_e_2589_: *mut LeanObject,
    mut v_xs_2590_: *mut LeanObject,
    mut v_a_2591_: *mut LeanObject,
    mut v_a_2592_: *mut LeanObject,
    mut v_a_2593_: *mut LeanObject,
    mut v_a_2594_: *mut LeanObject,
    mut v_a_2595_: *mut LeanObject,
    mut v_a_2596_: *mut LeanObject,
    mut v_a_2597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2598_: *mut LeanObject = core::ptr::null_mut();
    v_res_2598_ = l_Lean_Meta_Sym_abstractFVars(
        v_e_2589_, v_xs_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_,
    );
    lean_dec(v_a_2596_);
    lean_dec_ref(v_a_2595_);
    lean_dec(v_a_2594_);
    lean_dec_ref(v_a_2593_);
    lean_dec(v_a_2592_);
    lean_dec_ref(v_a_2591_);
    lean_dec_ref(v_xs_2590_);
    return v_res_2598_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(
    mut v_x_2599_: *mut LeanObject,
    mut v_bi_2600_: u8,
    mut v_t_2601_: *mut LeanObject,
    mut v_b_2602_: *mut LeanObject,
    mut v___y_2603_: *mut LeanObject,
    mut v___y_2604_: *mut LeanObject,
    mut v___y_2605_: *mut LeanObject,
    mut v___y_2606_: *mut LeanObject,
    mut v___y_2607_: *mut LeanObject,
    mut v___y_2608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2615_: u8 = 0;
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v_a_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2614_ = lean_st_ref_get(v___y_2604_);
                v_debug_2615_ = lean_ctor_get_uint8(
                    v___x_2614_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_2614_);
                if v_debug_2615_ == 0 {
                    v___y_2611_ = v___y_2604_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_t_2601_);
                    v___x_2616_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_t_2601_,
                        v___y_2603_,
                        v___y_2604_,
                        v___y_2605_,
                        v___y_2606_,
                        v___y_2607_,
                        v___y_2608_,
                    );
                    if lean_obj_tag(v___x_2616_) == 0 {
                        lean_dec_ref_known(v___x_2616_, 1);
                        lean_inc_ref(v_b_2602_);
                        v___x_2617_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_b_2602_,
                            v___y_2603_,
                            v___y_2604_,
                            v___y_2605_,
                            v___y_2606_,
                            v___y_2607_,
                            v___y_2608_,
                        );
                        if lean_obj_tag(v___x_2617_) == 0 {
                            lean_dec_ref_known(v___x_2617_, 1);
                            v___y_2611_ = v___y_2604_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_b_2602_);
                            lean_dec_ref(v_t_2601_);
                            lean_dec(v_x_2599_);
                            v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
                            v_isSharedCheck_2625_ = (!lean_is_exclusive(v___x_2617_)) as u8;
                            if v_isSharedCheck_2625_ == 0 {
                                v___x_2620_ = v___x_2617_;
                                v_isShared_2621_ = v_isSharedCheck_2625_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2618_);
                                lean_dec(v___x_2617_);
                                v___x_2620_ = lean_box(0);
                                v_isShared_2621_ = v_isSharedCheck_2625_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_2602_);
                        lean_dec_ref(v_t_2601_);
                        lean_dec(v_x_2599_);
                        v_a_2626_ = lean_ctor_get(v___x_2616_, 0);
                        v_isSharedCheck_2633_ = (!lean_is_exclusive(v___x_2616_)) as u8;
                        if v_isSharedCheck_2633_ == 0 {
                            v___x_2628_ = v___x_2616_;
                            v_isShared_2629_ = v_isSharedCheck_2633_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2626_);
                            lean_dec(v___x_2616_);
                            v___x_2628_ = lean_box(0);
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
                    v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
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
                    v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
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
    mut v_x_2634_: *mut LeanObject,
    mut v_bi_2635_: *mut LeanObject,
    mut v_t_2636_: *mut LeanObject,
    mut v_b_2637_: *mut LeanObject,
    mut v___y_2638_: *mut LeanObject,
    mut v___y_2639_: *mut LeanObject,
    mut v___y_2640_: *mut LeanObject,
    mut v___y_2641_: *mut LeanObject,
    mut v___y_2642_: *mut LeanObject,
    mut v___y_2643_: *mut LeanObject,
    mut v___y_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_2645_: u8 = 0;
    let mut v_res_2646_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_2645_ = (lean_unbox(v_bi_2635_) as u8);
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
    lean_dec(v___y_2643_);
    lean_dec_ref(v___y_2642_);
    lean_dec(v___y_2641_);
    lean_dec_ref(v___y_2640_);
    lean_dec(v___y_2639_);
    lean_dec_ref(v___y_2638_);
    return v_res_2646_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(
    mut v_xs_2647_: *mut LeanObject,
    mut v_i_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
    mut v___y_2651_: *mut LeanObject,
    mut v___y_2652_: *mut LeanObject,
    mut v___y_2653_: *mut LeanObject,
    mut v___y_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2658_: u8 = 0;
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: u8 = 0;
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2679_: u8 = 0;
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2657_ = lean_unsigned_to_nat(0);
                v_isZero_2658_ = lean_nat_dec_eq(v_i_2648_, v_zero_2657_);
                if v_isZero_2658_ == 1 {
                    lean_dec(v_i_2648_);
                    v___x_2659_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2659_, 0, v_a_2649_);
                    return v___x_2659_;
                } else {
                    v_one_2660_ = lean_unsigned_to_nat(1);
                    v_n_2661_ = lean_nat_sub(v_i_2648_, v_one_2660_);
                    lean_dec(v_i_2648_);
                    v___x_2666_ = lean_array_fget_borrowed(v_xs_2647_, v_n_2661_);
                    v___x_2667_ = l_Lean_Expr_fvarId_x21(v___x_2666_);
                    v___x_2668_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_2667_,
                        v___y_2652_,
                        v___y_2654_,
                        v___y_2655_,
                    );
                    if lean_obj_tag(v___x_2668_) == 0 {
                        v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
                        lean_inc(v_a_2669_);
                        lean_dec_ref_known(v___x_2668_, 1);
                        v___x_2670_ = l_Lean_LocalDecl_type(v_a_2669_);
                        v___x_2671_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
                            v___x_2670_,
                            v_n_2661_,
                            v_xs_2647_,
                            v___y_2651_,
                            v___y_2652_,
                        );
                        v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
                        lean_inc(v_a_2672_);
                        lean_dec_ref(v___x_2671_);
                        v___x_2673_ = l_Lean_LocalDecl_userName(v_a_2669_);
                        v___x_2674_ = l_Lean_LocalDecl_binderInfo(v_a_2669_);
                        lean_dec(v_a_2669_);
                        v___x_2675_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__0(v___x_2673_, v___x_2674_, v_a_2672_, v_a_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
                        v___y_2663_ = v___x_2675_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_n_2661_);
                        lean_dec_ref(v_a_2649_);
                        v_a_2676_ = lean_ctor_get(v___x_2668_, 0);
                        v_isSharedCheck_2683_ = (!lean_is_exclusive(v___x_2668_)) as u8;
                        if v_isSharedCheck_2683_ == 0 {
                            v___x_2678_ = v___x_2668_;
                            v_isShared_2679_ = v_isSharedCheck_2683_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2676_);
                            lean_dec(v___x_2668_);
                            v___x_2678_ = lean_box(0);
                            v_isShared_2679_ = v_isSharedCheck_2683_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_2663_) == 0 {
                    v_a_2664_ = lean_ctor_get(v___y_2663_, 0);
                    lean_inc(v_a_2664_);
                    lean_dec_ref_known(v___y_2663_, 1);
                    v_i_2648_ = v_n_2661_;
                    v_a_2649_ = v_a_2664_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_n_2661_);
                    return v___y_2663_;
                }
            }
            2 => {
                if v_isShared_2679_ == 0 {
                    v___x_2681_ = v___x_2678_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
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
    mut v_xs_2684_: *mut LeanObject,
    mut v_i_2685_: *mut LeanObject,
    mut v_a_2686_: *mut LeanObject,
    mut v___y_2687_: *mut LeanObject,
    mut v___y_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
    mut v___y_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2694_: *mut LeanObject = core::ptr::null_mut();
    v_res_2694_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2684_, v_i_2685_, v_a_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
    lean_dec(v___y_2692_);
    lean_dec_ref(v___y_2691_);
    lean_dec(v___y_2690_);
    lean_dec_ref(v___y_2689_);
    lean_dec(v___y_2688_);
    lean_dec_ref(v___y_2687_);
    lean_dec_ref(v_xs_2684_);
    return v_res_2694_;
}
pub unsafe fn l_Lean_Meta_Sym_mkLambdaFVarsS(
    mut v_xs_2695_: *mut LeanObject,
    mut v_e_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
    mut v_a_2699_: *mut LeanObject,
    mut v_a_2700_: *mut LeanObject,
    mut v_a_2701_: *mut LeanObject,
    mut v_a_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    v___x_2704_ = lean_unsigned_to_nat(0);
    v___x_2705_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
        v_e_2696_,
        v___x_2704_,
        v_xs_2695_,
        v_a_2698_,
        v_a_2699_,
    );
    v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
    lean_inc(v_a_2706_);
    lean_dec_ref(v___x_2705_);
    v___x_2707_ = lean_array_get_size(v_xs_2695_);
    v___x_2708_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2695_, v___x_2707_, v_a_2706_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
    return v___x_2708_;
}
pub unsafe fn l_Lean_Meta_Sym_mkLambdaFVarsS___boxed(
    mut v_xs_2709_: *mut LeanObject,
    mut v_e_2710_: *mut LeanObject,
    mut v_a_2711_: *mut LeanObject,
    mut v_a_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
    mut v_a_2717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2718_: *mut LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Lean_Meta_Sym_mkLambdaFVarsS(
        v_xs_2709_, v_e_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_,
    );
    lean_dec(v_a_2716_);
    lean_dec_ref(v_a_2715_);
    lean_dec(v_a_2714_);
    lean_dec_ref(v_a_2713_);
    lean_dec(v_a_2712_);
    lean_dec_ref(v_a_2711_);
    lean_dec_ref(v_xs_2709_);
    return v_res_2718_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(
    mut v_xs_2719_: *mut LeanObject,
    mut v_n_2720_: *mut LeanObject,
    mut v_i_2721_: *mut LeanObject,
    mut v_a_2722_: *mut LeanObject,
    mut v_a_2723_: *mut LeanObject,
    mut v___y_2724_: *mut LeanObject,
    mut v___y_2725_: *mut LeanObject,
    mut v___y_2726_: *mut LeanObject,
    mut v___y_2727_: *mut LeanObject,
    mut v___y_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    v___x_2731_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___redArg(v_xs_2719_, v_i_2721_, v_a_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
    return v___x_2731_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1___boxed(
    mut v_xs_2732_: *mut LeanObject,
    mut v_n_2733_: *mut LeanObject,
    mut v_i_2734_: *mut LeanObject,
    mut v_a_2735_: *mut LeanObject,
    mut v_a_2736_: *mut LeanObject,
    mut v___y_2737_: *mut LeanObject,
    mut v___y_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2744_: *mut LeanObject = core::ptr::null_mut();
    v_res_2744_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkLambdaFVarsS_spec__1(v_xs_2732_, v_n_2733_, v_i_2734_, v_a_2735_, v_a_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
    lean_dec(v___y_2742_);
    lean_dec_ref(v___y_2741_);
    lean_dec(v___y_2740_);
    lean_dec_ref(v___y_2739_);
    lean_dec(v___y_2738_);
    lean_dec_ref(v___y_2737_);
    lean_dec(v_n_2733_);
    lean_dec_ref(v_xs_2732_);
    return v_res_2744_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(
    mut v_x_2745_: *mut LeanObject,
    mut v_bi_2746_: u8,
    mut v_t_2747_: *mut LeanObject,
    mut v_b_2748_: *mut LeanObject,
    mut v___y_2749_: *mut LeanObject,
    mut v___y_2750_: *mut LeanObject,
    mut v___y_2751_: *mut LeanObject,
    mut v___y_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
    mut v___y_2754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2761_: u8 = 0;
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v_a_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2760_ = lean_st_ref_get(v___y_2750_);
                v_debug_2761_ = lean_ctor_get_uint8(
                    v___x_2760_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_2760_);
                if v_debug_2761_ == 0 {
                    v___y_2757_ = v___y_2750_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_t_2747_);
                    v___x_2762_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_t_2747_,
                        v___y_2749_,
                        v___y_2750_,
                        v___y_2751_,
                        v___y_2752_,
                        v___y_2753_,
                        v___y_2754_,
                    );
                    if lean_obj_tag(v___x_2762_) == 0 {
                        lean_dec_ref_known(v___x_2762_, 1);
                        lean_inc_ref(v_b_2748_);
                        v___x_2763_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_b_2748_,
                            v___y_2749_,
                            v___y_2750_,
                            v___y_2751_,
                            v___y_2752_,
                            v___y_2753_,
                            v___y_2754_,
                        );
                        if lean_obj_tag(v___x_2763_) == 0 {
                            lean_dec_ref_known(v___x_2763_, 1);
                            v___y_2757_ = v___y_2750_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_b_2748_);
                            lean_dec_ref(v_t_2747_);
                            lean_dec(v_x_2745_);
                            v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
                            v_isSharedCheck_2771_ = (!lean_is_exclusive(v___x_2763_)) as u8;
                            if v_isSharedCheck_2771_ == 0 {
                                v___x_2766_ = v___x_2763_;
                                v_isShared_2767_ = v_isSharedCheck_2771_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2764_);
                                lean_dec(v___x_2763_);
                                v___x_2766_ = lean_box(0);
                                v_isShared_2767_ = v_isSharedCheck_2771_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_2748_);
                        lean_dec_ref(v_t_2747_);
                        lean_dec(v_x_2745_);
                        v_a_2772_ = lean_ctor_get(v___x_2762_, 0);
                        v_isSharedCheck_2779_ = (!lean_is_exclusive(v___x_2762_)) as u8;
                        if v_isSharedCheck_2779_ == 0 {
                            v___x_2774_ = v___x_2762_;
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2772_);
                            lean_dec(v___x_2762_);
                            v___x_2774_ = lean_box(0);
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
                    v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
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
                    v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
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
    mut v_x_2780_: *mut LeanObject,
    mut v_bi_2781_: *mut LeanObject,
    mut v_t_2782_: *mut LeanObject,
    mut v_b_2783_: *mut LeanObject,
    mut v___y_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
    mut v___y_2786_: *mut LeanObject,
    mut v___y_2787_: *mut LeanObject,
    mut v___y_2788_: *mut LeanObject,
    mut v___y_2789_: *mut LeanObject,
    mut v___y_2790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_2791_: u8 = 0;
    let mut v_res_2792_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_2791_ = (lean_unbox(v_bi_2781_) as u8);
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
    lean_dec(v___y_2789_);
    lean_dec_ref(v___y_2788_);
    lean_dec(v___y_2787_);
    lean_dec_ref(v___y_2786_);
    lean_dec(v___y_2785_);
    lean_dec_ref(v___y_2784_);
    return v_res_2792_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(
    mut v_xs_2793_: *mut LeanObject,
    mut v_i_2794_: *mut LeanObject,
    mut v_a_2795_: *mut LeanObject,
    mut v___y_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
    mut v___y_2798_: *mut LeanObject,
    mut v___y_2799_: *mut LeanObject,
    mut v___y_2800_: *mut LeanObject,
    mut v___y_2801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2804_: u8 = 0;
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2803_ = lean_unsigned_to_nat(0);
                v_isZero_2804_ = lean_nat_dec_eq(v_i_2794_, v_zero_2803_);
                if v_isZero_2804_ == 1 {
                    lean_dec(v_i_2794_);
                    v___x_2805_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2805_, 0, v_a_2795_);
                    return v___x_2805_;
                } else {
                    v_one_2806_ = lean_unsigned_to_nat(1);
                    v_n_2807_ = lean_nat_sub(v_i_2794_, v_one_2806_);
                    lean_dec(v_i_2794_);
                    v___x_2812_ = lean_array_fget_borrowed(v_xs_2793_, v_n_2807_);
                    v___x_2813_ = l_Lean_Expr_fvarId_x21(v___x_2812_);
                    v___x_2814_ = l_Lean_FVarId_getDecl___redArg(
                        v___x_2813_,
                        v___y_2798_,
                        v___y_2800_,
                        v___y_2801_,
                    );
                    if lean_obj_tag(v___x_2814_) == 0 {
                        v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
                        lean_inc(v_a_2815_);
                        lean_dec_ref_known(v___x_2814_, 1);
                        v___x_2816_ = l_Lean_LocalDecl_type(v_a_2815_);
                        v___x_2817_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
                            v___x_2816_,
                            v_n_2807_,
                            v_xs_2793_,
                            v___y_2797_,
                            v___y_2798_,
                        );
                        v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
                        lean_inc(v_a_2818_);
                        lean_dec_ref(v___x_2817_);
                        v___x_2819_ = l_Lean_LocalDecl_userName(v_a_2815_);
                        v___x_2820_ = l_Lean_LocalDecl_binderInfo(v_a_2815_);
                        lean_dec(v_a_2815_);
                        v___x_2821_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Sym_mkForallFVarsS_spec__0(v___x_2819_, v___x_2820_, v_a_2818_, v_a_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_);
                        v___y_2809_ = v___x_2821_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_n_2807_);
                        lean_dec_ref(v_a_2795_);
                        v_a_2822_ = lean_ctor_get(v___x_2814_, 0);
                        v_isSharedCheck_2829_ = (!lean_is_exclusive(v___x_2814_)) as u8;
                        if v_isSharedCheck_2829_ == 0 {
                            v___x_2824_ = v___x_2814_;
                            v_isShared_2825_ = v_isSharedCheck_2829_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2822_);
                            lean_dec(v___x_2814_);
                            v___x_2824_ = lean_box(0);
                            v_isShared_2825_ = v_isSharedCheck_2829_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_2809_) == 0 {
                    v_a_2810_ = lean_ctor_get(v___y_2809_, 0);
                    lean_inc(v_a_2810_);
                    lean_dec_ref_known(v___y_2809_, 1);
                    v_i_2794_ = v_n_2807_;
                    v_a_2795_ = v_a_2810_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_n_2807_);
                    return v___y_2809_;
                }
            }
            2 => {
                if v_isShared_2825_ == 0 {
                    v___x_2827_ = v___x_2824_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
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
    mut v_xs_2830_: *mut LeanObject,
    mut v_i_2831_: *mut LeanObject,
    mut v_a_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
    mut v___y_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
    mut v___y_2836_: *mut LeanObject,
    mut v___y_2837_: *mut LeanObject,
    mut v___y_2838_: *mut LeanObject,
    mut v___y_2839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2840_: *mut LeanObject = core::ptr::null_mut();
    v_res_2840_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2830_, v_i_2831_, v_a_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
    lean_dec(v___y_2838_);
    lean_dec_ref(v___y_2837_);
    lean_dec(v___y_2836_);
    lean_dec_ref(v___y_2835_);
    lean_dec(v___y_2834_);
    lean_dec_ref(v___y_2833_);
    lean_dec_ref(v_xs_2830_);
    return v_res_2840_;
}
pub unsafe fn l_Lean_Meta_Sym_mkForallFVarsS(
    mut v_xs_2841_: *mut LeanObject,
    mut v_e_2842_: *mut LeanObject,
    mut v_a_2843_: *mut LeanObject,
    mut v_a_2844_: *mut LeanObject,
    mut v_a_2845_: *mut LeanObject,
    mut v_a_2846_: *mut LeanObject,
    mut v_a_2847_: *mut LeanObject,
    mut v_a_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    v___x_2850_ = lean_unsigned_to_nat(0);
    v___x_2851_ = l_Lean_Meta_Sym_abstractFVarsRange___redArg(
        v_e_2842_,
        v___x_2850_,
        v_xs_2841_,
        v_a_2844_,
        v_a_2845_,
    );
    v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
    lean_inc(v_a_2852_);
    lean_dec_ref(v___x_2851_);
    v___x_2853_ = lean_array_get_size(v_xs_2841_);
    v___x_2854_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2841_, v___x_2853_, v_a_2852_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
    return v___x_2854_;
}
pub unsafe fn l_Lean_Meta_Sym_mkForallFVarsS___boxed(
    mut v_xs_2855_: *mut LeanObject,
    mut v_e_2856_: *mut LeanObject,
    mut v_a_2857_: *mut LeanObject,
    mut v_a_2858_: *mut LeanObject,
    mut v_a_2859_: *mut LeanObject,
    mut v_a_2860_: *mut LeanObject,
    mut v_a_2861_: *mut LeanObject,
    mut v_a_2862_: *mut LeanObject,
    mut v_a_2863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2864_: *mut LeanObject = core::ptr::null_mut();
    v_res_2864_ = l_Lean_Meta_Sym_mkForallFVarsS(
        v_xs_2855_, v_e_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_,
    );
    lean_dec(v_a_2862_);
    lean_dec_ref(v_a_2861_);
    lean_dec(v_a_2860_);
    lean_dec_ref(v_a_2859_);
    lean_dec(v_a_2858_);
    lean_dec_ref(v_a_2857_);
    lean_dec_ref(v_xs_2855_);
    return v_res_2864_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(
    mut v_xs_2865_: *mut LeanObject,
    mut v_n_2866_: *mut LeanObject,
    mut v_i_2867_: *mut LeanObject,
    mut v_a_2868_: *mut LeanObject,
    mut v_a_2869_: *mut LeanObject,
    mut v___y_2870_: *mut LeanObject,
    mut v___y_2871_: *mut LeanObject,
    mut v___y_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
    mut v___y_2874_: *mut LeanObject,
    mut v___y_2875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    v___x_2877_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___redArg(v_xs_2865_, v_i_2867_, v_a_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
    return v___x_2877_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1___boxed(
    mut v_xs_2878_: *mut LeanObject,
    mut v_n_2879_: *mut LeanObject,
    mut v_i_2880_: *mut LeanObject,
    mut v_a_2881_: *mut LeanObject,
    mut v_a_2882_: *mut LeanObject,
    mut v___y_2883_: *mut LeanObject,
    mut v___y_2884_: *mut LeanObject,
    mut v___y_2885_: *mut LeanObject,
    mut v___y_2886_: *mut LeanObject,
    mut v___y_2887_: *mut LeanObject,
    mut v___y_2888_: *mut LeanObject,
    mut v___y_2889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2890_: *mut LeanObject = core::ptr::null_mut();
    v_res_2890_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_Sym_mkForallFVarsS_spec__1(v_xs_2878_, v_n_2879_, v_i_2880_, v_a_2881_, v_a_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
    lean_dec(v___y_2888_);
    lean_dec_ref(v___y_2887_);
    lean_dec(v___y_2886_);
    lean_dec_ref(v___y_2885_);
    lean_dec(v___y_2884_);
    lean_dec_ref(v___y_2883_);
    lean_dec(v_n_2879_);
    lean_dec_ref(v_xs_2878_);
    return v_res_2890_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_AbstractS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_AbstractS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_AbstractS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_AbstractS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_AbstractS(builtin);
}
