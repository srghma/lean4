// Lean compiler output
// Module: Lean.Meta.Sym.InstantiateS
// Imports: Lean.Meta.Sym.SymM Lean.Meta.Sym.LooseBVarsS Init.Grind
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
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instMonad___redArg, l_instInhabitedForall___redArg___lam__0___boxed,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_bvar___override, l_Lean_Expr_forallE___override,
    l_Lean_Expr_getAppFn, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_isBVar,
    l_Lean_Expr_lam___override, l_Lean_Expr_letE___override, l_Lean_Expr_looseBVarRange,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    l_Lean_Meta_Sym_Internal_Builder_assertShared, l_Lean_Meta_Sym_Internal_Builder_share1___redArg,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::LooseBVarsS::{
    initialize_Lean_Meta_Sym_LooseBVarsS, l_Lean_Meta_Sym_liftLooseBVarsS_x27,
    runtime_initialize_Lean_Meta_Sym_LooseBVarsS,
};
use crate::r#gen::Lean::Meta::Sym::ReplaceS::l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, l_Lean_Meta_Sym_instInhabitedSymM,
    runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_uint64_mix_hash,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instantiateRevRangeS___closed__3_value: crate::leanh::LeanStringObject<
    27,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 73, 110, 115, 116, 97, 110,
        116, 105, 97, 116, 101, 83, 0,
    ],
};
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_instantiateRevRangeS___closed__4_value: crate::leanh::LeanStringObject<
    35,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 105, 110, 115, 116, 97, 110,
        116, 105, 97, 116, 101, 82, 101, 118, 82, 97, 110, 103, 101, 83, 0,
    ],
};
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value: crate::leanh::LeanStringObject<71> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 73, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 82, 97, 110, 103, 101, 83, 39, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 65, 112, 112, 83, 33, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 65, 108, 112, 104, 97, 83, 104, 97, 114, 101, 66, 117, 105, 108, 100, 101, 114, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value: crate::leanh::LeanStringObject<86> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 86, m_capacity: 86, m_length: 85, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 73, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 82, 101, 118, 66, 101, 116, 97, 83, 39, 46, 118, 105, 115, 105, 116, 65, 112, 112, 66, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 73, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 82, 101, 118, 66, 101, 116, 97, 83, 39, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2259_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2259_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0);
    v___x_2261_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2261_, 0, v___x_2260_);
    return v___x_2261_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(
    mut v_00_u03b2_2262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2263_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1);
    return v___x_2263_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(
    mut v_idx_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2266_ = l_Lean_Expr_bvar___override(v_idx_2264_);
    v___x_2267_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2266_, v___y_2265_);
    return v___x_2267_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(
    mut v_idx_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: u8,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2271_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v_idx_2268_, v___y_2270_);
    return v___x_2271_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(
    mut v_idx_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_22951__boxed_2275_: u8 = 0;
    let mut v_res_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_22951__boxed_2275_ = (crate::leanh::lean_unbox(v___y_2273_) as u8);
    v_res_2276_ =
        l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(
            v_idx_2272_,
            v___y_22951__boxed_2275_,
            v___y_2274_,
        );
    return v_res_2276_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2277_ = l_Lean_Meta_Sym_instInhabitedSymM(crate::leanh::lean_box(0));
    return v___x_2277_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(
    mut v_msg_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191__overap_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0_once
        ),
        _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0,
    );
    v___x_3191__overap_2287_ = lean_panic_fn_borrowed(v___x_2286_, v_msg_2278_);
    crate::leanh::lean_inc(v___y_2284_);
    crate::leanh::lean_inc_ref(v___y_2283_);
    crate::leanh::lean_inc(v___y_2282_);
    crate::leanh::lean_inc_ref(v___y_2281_);
    crate::leanh::lean_inc(v___y_2280_);
    crate::leanh::lean_inc_ref(v___y_2279_);
    v___x_2288_ = crate::leanh::lean_apply_7(
        v___x_3191__overap_2287_,
        v___y_2279_,
        v___y_2280_,
        v___y_2281_,
        v___y_2282_,
        v___y_2283_,
        v___y_2284_,
        crate::leanh::lean_box(0),
    );
    return v___x_2288_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___boxed(
    mut v_msg_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2297_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(
        v_msg_2289_,
        v___y_2290_,
        v___y_2291_,
        v___y_2292_,
        v___y_2293_,
        v___y_2294_,
        v___y_2295_,
    );
    crate::leanh::lean_dec(v___y_2295_);
    crate::leanh::lean_dec_ref(v___y_2294_);
    crate::leanh::lean_dec(v___y_2293_);
    crate::leanh::lean_dec_ref(v___y_2292_);
    crate::leanh::lean_dec(v___y_2291_);
    crate::leanh::lean_dec_ref(v___y_2290_);
    return v_res_2297_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(
    mut v_x_2298_: *mut crate::leanh::LeanObject,
    mut v_bi_2299_: u8,
    mut v_t_2300_: *mut crate::leanh::LeanObject,
    mut v_b_2301_: *mut crate::leanh::LeanObject,
    mut v___y_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: u8,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_2303_ == 0 {
                    v___y_2306_ = v___y_2302_;
                    v___y_2307_ = v___y_2304_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_t_2300_);
                    v___x_2320_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_2300_,
                        v___y_2303_,
                        v___y_2304_,
                    );
                    v_snd_2321_ = crate::leanh::lean_ctor_get(v___x_2320_, 1);
                    crate::leanh::lean_inc(v_snd_2321_);
                    crate::leanh::lean_dec_ref(v___x_2320_);
                    crate::leanh::lean_inc_ref(v_b_2301_);
                    v___x_2322_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_2301_,
                        v___y_2303_,
                        v_snd_2321_,
                    );
                    v_snd_2323_ = crate::leanh::lean_ctor_get(v___x_2322_, 1);
                    crate::leanh::lean_inc(v_snd_2323_);
                    crate::leanh::lean_dec_ref(v___x_2322_);
                    v___y_2306_ = v___y_2302_;
                    v___y_2307_ = v_snd_2323_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2308_ =
                    l_Lean_Expr_forallE___override(v_x_2298_, v_t_2300_, v_b_2301_, v_bi_2299_);
                v___x_2309_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2308_, v___y_2307_);
                v_fst_2310_ = crate::leanh::lean_ctor_get(v___x_2309_, 0);
                v_snd_2311_ = crate::leanh::lean_ctor_get(v___x_2309_, 1);
                v_isSharedCheck_2319_ = (!crate::leanh::lean_is_exclusive(v___x_2309_)) as u8;
                if v_isSharedCheck_2319_ == 0 {
                    v___x_2313_ = v___x_2309_;
                    v_isShared_2314_ = v_isSharedCheck_2319_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2311_);
                    crate::leanh::lean_inc(v_fst_2310_);
                    crate::leanh::lean_dec(v___x_2309_);
                    v___x_2313_ = crate::leanh::lean_box(0);
                    v_isShared_2314_ = v_isSharedCheck_2319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2314_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2313_, 1, v___y_2306_);
                    v___x_2316_ = v___x_2313_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_fst_2310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___y_2306_);
                    v___x_2316_ = v_reuseFailAlloc_2318_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2317_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2317_, 0, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2317_, 1, v_snd_2311_);
                return v___x_2317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5___boxed(
    mut v_x_2324_: *mut crate::leanh::LeanObject,
    mut v_bi_2325_: *mut crate::leanh::LeanObject,
    mut v_t_2326_: *mut crate::leanh::LeanObject,
    mut v_b_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_2331_: u8 = 0;
    let mut v___y_22988__boxed_2332_: u8 = 0;
    let mut v_res_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2331_ = (crate::leanh::lean_unbox(v_bi_2325_) as u8);
    v___y_22988__boxed_2332_ = (crate::leanh::lean_unbox(v___y_2329_) as u8);
    v_res_2333_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_x_2324_, v_bi_boxed_2331_, v_t_2326_, v_b_2327_, v___y_2328_, v___y_22988__boxed_2332_, v___y_2330_);
    return v_res_2333_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(
    mut v_msg_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: u8,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_22617__overap_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2345_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0;
    v___f_2346_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1;
    v___f_2347_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2;
    v___f_2348_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3;
    v___f_2349_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4;
    v___f_2350_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5;
    v___f_2351_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6;
    v___x_2352_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2352_, 0, v___f_2345_);
    crate::leanh::lean_ctor_set(v___x_2352_, 1, v___f_2346_);
    v___x_2353_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2353_, 0, v___x_2352_);
    crate::leanh::lean_ctor_set(v___x_2353_, 1, v___f_2347_);
    crate::leanh::lean_ctor_set(v___x_2353_, 2, v___f_2348_);
    crate::leanh::lean_ctor_set(v___x_2353_, 3, v___f_2349_);
    crate::leanh::lean_ctor_set(v___x_2353_, 4, v___f_2350_);
    v___x_2354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2354_, 0, v___x_2353_);
    crate::leanh::lean_ctor_set(v___x_2354_, 1, v___f_2351_);
    crate::leanh::lean_inc_ref_n(v___x_2354_, 6);
    v___f_2355_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2355_, 0, v___x_2354_);
    v___f_2356_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2356_, 0, v___x_2354_);
    v___f_2357_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2357_, 0, v___x_2354_);
    v___f_2358_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2358_, 0, v___x_2354_);
    v___x_2359_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_2359_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2359_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2359_, 2, v___x_2354_);
    v___x_2360_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2360_, 0, v___x_2359_);
    crate::leanh::lean_ctor_set(v___x_2360_, 1, v___f_2355_);
    v___x_2361_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_2361_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2361_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2361_, 2, v___x_2354_);
    v___x_2362_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2362_, 0, v___x_2360_);
    crate::leanh::lean_ctor_set(v___x_2362_, 1, v___x_2361_);
    crate::leanh::lean_ctor_set(v___x_2362_, 2, v___f_2356_);
    crate::leanh::lean_ctor_set(v___x_2362_, 3, v___f_2357_);
    crate::leanh::lean_ctor_set(v___x_2362_, 4, v___f_2358_);
    v___x_2363_ = crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_2363_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2363_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2363_, 2, v___x_2354_);
    v___x_2364_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2364_, 0, v___x_2362_);
    crate::leanh::lean_ctor_set(v___x_2364_, 1, v___x_2363_);
    v___x_2365_ = l_ReaderT_instMonad___redArg(v___x_2364_);
    crate::leanh::lean_inc_ref_n(v___x_2365_, 6);
    v___f_2366_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2366_, 0, v___x_2365_);
    v___f_2367_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2367_, 0, v___x_2365_);
    v___f_2368_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2368_, 0, v___x_2365_);
    v___f_2369_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2369_, 0, v___x_2365_);
    v___x_2370_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_2370_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2370_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2370_, 2, v___x_2365_);
    v___x_2371_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2371_, 0, v___x_2370_);
    crate::leanh::lean_ctor_set(v___x_2371_, 1, v___f_2366_);
    v___x_2372_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_2372_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2372_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2372_, 2, v___x_2365_);
    v___x_2373_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2373_, 0, v___x_2371_);
    crate::leanh::lean_ctor_set(v___x_2373_, 1, v___x_2372_);
    crate::leanh::lean_ctor_set(v___x_2373_, 2, v___f_2367_);
    crate::leanh::lean_ctor_set(v___x_2373_, 3, v___f_2368_);
    crate::leanh::lean_ctor_set(v___x_2373_, 4, v___f_2369_);
    v___x_2374_ = crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_2374_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2374_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2374_, 2, v___x_2365_);
    v___x_2375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2375_, 0, v___x_2373_);
    crate::leanh::lean_ctor_set(v___x_2375_, 1, v___x_2374_);
    v___x_2376_ = l_Lean_instInhabitedExpr;
    v___x_2377_ = l_instInhabitedOfMonad___redArg(v___x_2375_, v___x_2376_);
    v___x_22617__overap_2378_ = lean_panic_fn_borrowed(v___x_2377_, v_msg_2341_);
    crate::leanh::lean_dec(v___x_2377_);
    v___x_2379_ = crate::leanh::lean_box((v___y_2343_) as usize);
    v___x_2380_ = crate::leanh::lean_apply_3(
        v___x_22617__overap_2378_,
        v___y_2342_,
        v___x_2379_,
        v___y_2344_,
    );
    return v___x_2380_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___boxed(
    mut v_msg_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_23051__boxed_2385_: u8 = 0;
    let mut v_res_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_23051__boxed_2385_ = (crate::leanh::lean_unbox(v___y_2383_) as u8);
    v_res_2386_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v_msg_2381_, v___y_2382_, v___y_23051__boxed_2385_, v___y_2384_);
    return v_res_2386_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(
    mut v_structName_2387_: *mut crate::leanh::LeanObject,
    mut v_idx_2388_: *mut crate::leanh::LeanObject,
    mut v_struct_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: u8,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2407_: u8 = 0;
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_2391_ == 0 {
                    v___y_2394_ = v___y_2390_;
                    v___y_2395_ = v___y_2392_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_struct_2389_);
                    v___x_2408_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_struct_2389_,
                        v___y_2391_,
                        v___y_2392_,
                    );
                    v_snd_2409_ = crate::leanh::lean_ctor_get(v___x_2408_, 1);
                    crate::leanh::lean_inc(v_snd_2409_);
                    crate::leanh::lean_dec_ref(v___x_2408_);
                    v___y_2394_ = v___y_2390_;
                    v___y_2395_ = v_snd_2409_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2396_ =
                    l_Lean_Expr_proj___override(v_structName_2387_, v_idx_2388_, v_struct_2389_);
                v___x_2397_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2396_, v___y_2395_);
                v_fst_2398_ = crate::leanh::lean_ctor_get(v___x_2397_, 0);
                v_snd_2399_ = crate::leanh::lean_ctor_get(v___x_2397_, 1);
                v_isSharedCheck_2407_ = (!crate::leanh::lean_is_exclusive(v___x_2397_)) as u8;
                if v_isSharedCheck_2407_ == 0 {
                    v___x_2401_ = v___x_2397_;
                    v_isShared_2402_ = v_isSharedCheck_2407_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2399_);
                    crate::leanh::lean_inc(v_fst_2398_);
                    crate::leanh::lean_dec(v___x_2397_);
                    v___x_2401_ = crate::leanh::lean_box(0);
                    v_isShared_2402_ = v_isSharedCheck_2407_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2402_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2401_, 1, v___y_2394_);
                    v___x_2404_ = v___x_2401_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2406_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_fst_2398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___y_2394_);
                    v___x_2404_ = v_reuseFailAlloc_2406_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2405_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2404_);
                crate::leanh::lean_ctor_set(v___x_2405_, 1, v_snd_2399_);
                return v___x_2405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8___boxed(
    mut v_structName_2410_: *mut crate::leanh::LeanObject,
    mut v_idx_2411_: *mut crate::leanh::LeanObject,
    mut v_struct_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
    mut v___y_2414_: *mut crate::leanh::LeanObject,
    mut v___y_2415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_23137__boxed_2416_: u8 = 0;
    let mut v_res_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_23137__boxed_2416_ = (crate::leanh::lean_unbox(v___y_2414_) as u8);
    v_res_2417_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_structName_2410_, v_idx_2411_, v_struct_2412_, v___y_2413_, v___y_23137__boxed_2416_, v___y_2415_);
    return v_res_2417_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(
    mut v_x_2418_: *mut crate::leanh::LeanObject,
    mut v_bi_2419_: u8,
    mut v_t_2420_: *mut crate::leanh::LeanObject,
    mut v_b_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
    mut v___y_2423_: u8,
    mut v___y_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2434_: u8 = 0;
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2439_: u8 = 0;
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_2423_ == 0 {
                    v___y_2426_ = v___y_2422_;
                    v___y_2427_ = v___y_2424_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_t_2420_);
                    v___x_2440_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_2420_,
                        v___y_2423_,
                        v___y_2424_,
                    );
                    v_snd_2441_ = crate::leanh::lean_ctor_get(v___x_2440_, 1);
                    crate::leanh::lean_inc(v_snd_2441_);
                    crate::leanh::lean_dec_ref(v___x_2440_);
                    crate::leanh::lean_inc_ref(v_b_2421_);
                    v___x_2442_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_2421_,
                        v___y_2423_,
                        v_snd_2441_,
                    );
                    v_snd_2443_ = crate::leanh::lean_ctor_get(v___x_2442_, 1);
                    crate::leanh::lean_inc(v_snd_2443_);
                    crate::leanh::lean_dec_ref(v___x_2442_);
                    v___y_2426_ = v___y_2422_;
                    v___y_2427_ = v_snd_2443_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2428_ =
                    l_Lean_Expr_lam___override(v_x_2418_, v_t_2420_, v_b_2421_, v_bi_2419_);
                v___x_2429_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2428_, v___y_2427_);
                v_fst_2430_ = crate::leanh::lean_ctor_get(v___x_2429_, 0);
                v_snd_2431_ = crate::leanh::lean_ctor_get(v___x_2429_, 1);
                v_isSharedCheck_2439_ = (!crate::leanh::lean_is_exclusive(v___x_2429_)) as u8;
                if v_isSharedCheck_2439_ == 0 {
                    v___x_2433_ = v___x_2429_;
                    v_isShared_2434_ = v_isSharedCheck_2439_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2431_);
                    crate::leanh::lean_inc(v_fst_2430_);
                    crate::leanh::lean_dec(v___x_2429_);
                    v___x_2433_ = crate::leanh::lean_box(0);
                    v_isShared_2434_ = v_isSharedCheck_2439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2434_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2433_, 1, v___y_2426_);
                    v___x_2436_ = v___x_2433_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2438_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_fst_2430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___y_2426_);
                    v___x_2436_ = v_reuseFailAlloc_2438_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2437_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2437_, 0, v___x_2436_);
                crate::leanh::lean_ctor_set(v___x_2437_, 1, v_snd_2431_);
                return v___x_2437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4___boxed(
    mut v_x_2444_: *mut crate::leanh::LeanObject,
    mut v_bi_2445_: *mut crate::leanh::LeanObject,
    mut v_t_2446_: *mut crate::leanh::LeanObject,
    mut v_b_2447_: *mut crate::leanh::LeanObject,
    mut v___y_2448_: *mut crate::leanh::LeanObject,
    mut v___y_2449_: *mut crate::leanh::LeanObject,
    mut v___y_2450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_2451_: u8 = 0;
    let mut v___y_23181__boxed_2452_: u8 = 0;
    let mut v_res_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_2451_ = (crate::leanh::lean_unbox(v_bi_2445_) as u8);
    v___y_23181__boxed_2452_ = (crate::leanh::lean_unbox(v___y_2449_) as u8);
    v_res_2453_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_x_2444_, v_bi_boxed_2451_, v_t_2446_, v_b_2447_, v___y_2448_, v___y_23181__boxed_2452_, v___y_2450_);
    return v_res_2453_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(
    mut v_d_2454_: *mut crate::leanh::LeanObject,
    mut v_e_2455_: *mut crate::leanh::LeanObject,
    mut v___y_2456_: *mut crate::leanh::LeanObject,
    mut v___y_2457_: u8,
    mut v___y_2458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2468_: u8 = 0;
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_2457_ == 0 {
                    v___y_2460_ = v___y_2456_;
                    v___y_2461_ = v___y_2458_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_e_2455_);
                    v___x_2474_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_e_2455_,
                        v___y_2457_,
                        v___y_2458_,
                    );
                    v_snd_2475_ = crate::leanh::lean_ctor_get(v___x_2474_, 1);
                    crate::leanh::lean_inc(v_snd_2475_);
                    crate::leanh::lean_dec_ref(v___x_2474_);
                    v___y_2460_ = v___y_2456_;
                    v___y_2461_ = v_snd_2475_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2462_ = l_Lean_Expr_mdata___override(v_d_2454_, v_e_2455_);
                v___x_2463_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2462_, v___y_2461_);
                v_fst_2464_ = crate::leanh::lean_ctor_get(v___x_2463_, 0);
                v_snd_2465_ = crate::leanh::lean_ctor_get(v___x_2463_, 1);
                v_isSharedCheck_2473_ = (!crate::leanh::lean_is_exclusive(v___x_2463_)) as u8;
                if v_isSharedCheck_2473_ == 0 {
                    v___x_2467_ = v___x_2463_;
                    v_isShared_2468_ = v_isSharedCheck_2473_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2465_);
                    crate::leanh::lean_inc(v_fst_2464_);
                    crate::leanh::lean_dec(v___x_2463_);
                    v___x_2467_ = crate::leanh::lean_box(0);
                    v_isShared_2468_ = v_isSharedCheck_2473_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2467_, 1, v___y_2460_);
                    v___x_2470_ = v___x_2467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2472_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_fst_2464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___y_2460_);
                    v___x_2470_ = v_reuseFailAlloc_2472_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2471_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2471_, 0, v___x_2470_);
                crate::leanh::lean_ctor_set(v___x_2471_, 1, v_snd_2465_);
                return v___x_2471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7___boxed(
    mut v_d_2476_: *mut crate::leanh::LeanObject,
    mut v_e_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_23230__boxed_2481_: u8 = 0;
    let mut v_res_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_23230__boxed_2481_ = (crate::leanh::lean_unbox(v___y_2479_) as u8);
    v_res_2482_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_d_2476_, v_e_2477_, v___y_2478_, v___y_23230__boxed_2481_, v___y_2480_);
    return v_res_2482_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(
    mut v_a_2483_: *mut crate::leanh::LeanObject,
    mut v_x_2484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2490_: u8 = 0;
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: u8 = 0;
    let mut v___x_2498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2484_) == 0 {
                    v___x_2485_ = crate::leanh::lean_box(0);
                    return v___x_2485_;
                } else {
                    v_key_2486_ = crate::leanh::lean_ctor_get(v_x_2484_, 0);
                    v_value_2487_ = crate::leanh::lean_ctor_get(v_x_2484_, 1);
                    v_tail_2488_ = crate::leanh::lean_ctor_get(v_x_2484_, 2);
                    v_fst_2493_ = crate::leanh::lean_ctor_get(v_key_2486_, 0);
                    v_snd_2494_ = crate::leanh::lean_ctor_get(v_key_2486_, 1);
                    v_fst_2495_ = crate::leanh::lean_ctor_get(v_a_2483_, 0);
                    v_snd_2496_ = crate::leanh::lean_ctor_get(v_a_2483_, 1);
                    v___x_2497_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_2493_,
                            v_fst_2495_,
                        );
                    if v___x_2497_ == 0 {
                        v___y_2490_ = v___x_2497_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2498_ = lean_nat_dec_eq(v_snd_2494_, v_snd_2496_);
                        v___y_2490_ = v___x_2498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2490_ == 0 {
                    v_x_2484_ = v_tail_2488_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_value_2487_);
                    v___x_2492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2492_, 0, v_value_2487_);
                    return v___x_2492_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg___boxed(
    mut v_a_2499_: *mut crate::leanh::LeanObject,
    mut v_x_2500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2501_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_2499_, v_x_2500_);
    crate::leanh::lean_dec(v_x_2500_);
    crate::leanh::lean_dec_ref(v_a_2499_);
    return v_res_2501_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(
    mut v_m_2502_: *mut crate::leanh::LeanObject,
    mut v_a_2503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: u64 = 0;
    let mut v___x_2509_: u64 = 0;
    let mut v___x_2510_: u64 = 0;
    let mut v___x_2511_: u64 = 0;
    let mut v___x_2512_: u64 = 0;
    let mut v_fold_2513_: u64 = 0;
    let mut v___x_2514_: u64 = 0;
    let mut v___x_2515_: u64 = 0;
    let mut v___x_2516_: u64 = 0;
    let mut v___x_2517_: usize = 0;
    let mut v___x_2518_: usize = 0;
    let mut v___x_2519_: usize = 0;
    let mut v___x_2520_: usize = 0;
    let mut v___x_2521_: usize = 0;
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2504_ = crate::leanh::lean_ctor_get(v_m_2502_, 1);
    v_fst_2505_ = crate::leanh::lean_ctor_get(v_a_2503_, 0);
    v_snd_2506_ = crate::leanh::lean_ctor_get(v_a_2503_, 1);
    v___x_2507_ = lean_array_get_size(v_buckets_2504_);
    v___x_2508_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_2505_);
    v___x_2509_ = lean_uint64_of_nat(v_snd_2506_);
    v___x_2510_ = lean_uint64_mix_hash(v___x_2508_, v___x_2509_);
    v___x_2511_ = 32u64;
    v___x_2512_ = lean_uint64_shift_right(v___x_2510_, v___x_2511_);
    v_fold_2513_ = lean_uint64_xor(v___x_2510_, v___x_2512_);
    v___x_2514_ = 16u64;
    v___x_2515_ = lean_uint64_shift_right(v_fold_2513_, v___x_2514_);
    v___x_2516_ = lean_uint64_xor(v_fold_2513_, v___x_2515_);
    v___x_2517_ = lean_uint64_to_usize(v___x_2516_);
    v___x_2518_ = lean_usize_of_nat(v___x_2507_);
    v___x_2519_ = 1usize;
    v___x_2520_ = lean_usize_sub(v___x_2518_, v___x_2519_);
    v___x_2521_ = lean_usize_land(v___x_2517_, v___x_2520_);
    v___x_2522_ = lean_array_uget_borrowed(v_buckets_2504_, v___x_2521_);
    v___x_2523_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_2503_, v___x_2522_);
    return v___x_2523_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_m_2524_: *mut crate::leanh::LeanObject,
    mut v_a_2525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_2524_, v_a_2525_);
    crate::leanh::lean_dec_ref(v_a_2525_);
    crate::leanh::lean_dec_ref(v_m_2524_);
    return v_res_2526_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(
    mut v_f_2527_: *mut crate::leanh::LeanObject,
    mut v_a_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: u8,
    mut v___y_2531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_2530_ == 0 {
                    v___y_2533_ = v___y_2529_;
                    v___y_2534_ = v___y_2531_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_2527_);
                    v___x_2547_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_f_2527_,
                        v___y_2530_,
                        v___y_2531_,
                    );
                    v_snd_2548_ = crate::leanh::lean_ctor_get(v___x_2547_, 1);
                    crate::leanh::lean_inc(v_snd_2548_);
                    crate::leanh::lean_dec_ref(v___x_2547_);
                    crate::leanh::lean_inc_ref(v_a_2528_);
                    v___x_2549_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_a_2528_,
                        v___y_2530_,
                        v_snd_2548_,
                    );
                    v_snd_2550_ = crate::leanh::lean_ctor_get(v___x_2549_, 1);
                    crate::leanh::lean_inc(v_snd_2550_);
                    crate::leanh::lean_dec_ref(v___x_2549_);
                    v___y_2533_ = v___y_2529_;
                    v___y_2534_ = v_snd_2550_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2535_ = l_Lean_Expr_app___override(v_f_2527_, v_a_2528_);
                v___x_2536_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2535_, v___y_2534_);
                v_fst_2537_ = crate::leanh::lean_ctor_get(v___x_2536_, 0);
                v_snd_2538_ = crate::leanh::lean_ctor_get(v___x_2536_, 1);
                v_isSharedCheck_2546_ = (!crate::leanh::lean_is_exclusive(v___x_2536_)) as u8;
                if v_isSharedCheck_2546_ == 0 {
                    v___x_2540_ = v___x_2536_;
                    v_isShared_2541_ = v_isSharedCheck_2546_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2538_);
                    crate::leanh::lean_inc(v_fst_2537_);
                    crate::leanh::lean_dec(v___x_2536_);
                    v___x_2540_ = crate::leanh::lean_box(0);
                    v_isShared_2541_ = v_isSharedCheck_2546_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2541_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2540_, 1, v___y_2533_);
                    v___x_2543_ = v___x_2540_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_fst_2537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___y_2533_);
                    v___x_2543_ = v_reuseFailAlloc_2545_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2544_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2544_, 0, v___x_2543_);
                crate::leanh::lean_ctor_set(v___x_2544_, 1, v_snd_2538_);
                return v___x_2544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3___boxed(
    mut v_f_2551_: *mut crate::leanh::LeanObject,
    mut v_a_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_23343__boxed_2556_: u8 = 0;
    let mut v_res_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_23343__boxed_2556_ = (crate::leanh::lean_unbox(v___y_2554_) as u8);
    v_res_2557_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_f_2551_, v_a_2552_, v___y_2553_, v___y_23343__boxed_2556_, v___y_2555_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(
    mut v_x_2558_: *mut crate::leanh::LeanObject,
    mut v_t_2559_: *mut crate::leanh::LeanObject,
    mut v_v_2560_: *mut crate::leanh::LeanObject,
    mut v_b_2561_: *mut crate::leanh::LeanObject,
    mut v_nondep_2562_: u8,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: u8,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2580_: u8 = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_2564_ == 0 {
                    v___y_2567_ = v___y_2563_;
                    v___y_2568_ = v___y_2565_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_t_2559_);
                    v___x_2581_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_2559_,
                        v___y_2564_,
                        v___y_2565_,
                    );
                    v_snd_2582_ = crate::leanh::lean_ctor_get(v___x_2581_, 1);
                    crate::leanh::lean_inc(v_snd_2582_);
                    crate::leanh::lean_dec_ref(v___x_2581_);
                    crate::leanh::lean_inc_ref(v_v_2560_);
                    v___x_2583_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_v_2560_,
                        v___y_2564_,
                        v_snd_2582_,
                    );
                    v_snd_2584_ = crate::leanh::lean_ctor_get(v___x_2583_, 1);
                    crate::leanh::lean_inc(v_snd_2584_);
                    crate::leanh::lean_dec_ref(v___x_2583_);
                    crate::leanh::lean_inc_ref(v_b_2561_);
                    v___x_2585_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_2561_,
                        v___y_2564_,
                        v_snd_2584_,
                    );
                    v_snd_2586_ = crate::leanh::lean_ctor_get(v___x_2585_, 1);
                    crate::leanh::lean_inc(v_snd_2586_);
                    crate::leanh::lean_dec_ref(v___x_2585_);
                    v___y_2567_ = v___y_2563_;
                    v___y_2568_ = v_snd_2586_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2569_ = l_Lean_Expr_letE___override(
                    v_x_2558_,
                    v_t_2559_,
                    v_v_2560_,
                    v_b_2561_,
                    v_nondep_2562_,
                );
                v___x_2570_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2569_, v___y_2568_);
                v_fst_2571_ = crate::leanh::lean_ctor_get(v___x_2570_, 0);
                v_snd_2572_ = crate::leanh::lean_ctor_get(v___x_2570_, 1);
                v_isSharedCheck_2580_ = (!crate::leanh::lean_is_exclusive(v___x_2570_)) as u8;
                if v_isSharedCheck_2580_ == 0 {
                    v___x_2574_ = v___x_2570_;
                    v_isShared_2575_ = v_isSharedCheck_2580_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2572_);
                    crate::leanh::lean_inc(v_fst_2571_);
                    crate::leanh::lean_dec(v___x_2570_);
                    v___x_2574_ = crate::leanh::lean_box(0);
                    v_isShared_2575_ = v_isSharedCheck_2580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2574_, 1, v___y_2567_);
                    v___x_2577_ = v___x_2574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2579_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_fst_2571_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___y_2567_);
                    v___x_2577_ = v_reuseFailAlloc_2579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2578_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2578_, 0, v___x_2577_);
                crate::leanh::lean_ctor_set(v___x_2578_, 1, v_snd_2572_);
                return v___x_2578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6___boxed(
    mut v_x_2587_: *mut crate::leanh::LeanObject,
    mut v_t_2588_: *mut crate::leanh::LeanObject,
    mut v_v_2589_: *mut crate::leanh::LeanObject,
    mut v_b_2590_: *mut crate::leanh::LeanObject,
    mut v_nondep_2591_: *mut crate::leanh::LeanObject,
    mut v___y_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_2595_: u8 = 0;
    let mut v___y_23392__boxed_2596_: u8 = 0;
    let mut v_res_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_2595_ = (crate::leanh::lean_unbox(v_nondep_2591_) as u8);
    v___y_23392__boxed_2596_ = (crate::leanh::lean_unbox(v___y_2593_) as u8);
    v_res_2597_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_x_2587_, v_t_2588_, v_v_2589_, v_b_2590_, v_nondep_boxed_2595_, v___y_2592_, v___y_23392__boxed_2596_, v___y_2594_);
    return v_res_2597_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2601_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_2602_ = crate::leanh::lean_unsigned_to_nat(67);
    v___x_2603_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_2604_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1;
    v___x_2605_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0;
    v___x_2606_ = l_mkPanicMessageWithDecl(
        v___x_2605_,
        v___x_2604_,
        v___x_2603_,
        v___x_2602_,
        v___x_2601_,
    );
    return v___x_2606_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(
    mut v_beginIdx_2607_: *mut crate::leanh::LeanObject,
    mut v_n_2608_: *mut crate::leanh::LeanObject,
    mut v_subst_2609_: *mut crate::leanh::LeanObject,
    mut v_e_2610_: *mut crate::leanh::LeanObject,
    mut v_offset_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: u8,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2627_: u8 = 0;
    let mut v_fst_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2632_: u8 = 0;
    let mut v___y_2634_: u8 = 0;
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: u8 = 0;
    let mut v___x_2643_: u8 = 0;
    let mut v_isSharedCheck_2644_: u8 = 0;
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut v_binderName_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2649_: u8 = 0;
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v_fst_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2667_: u8 = 0;
    let mut v___y_2669_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: u8 = 0;
    let mut v___x_2678_: u8 = 0;
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v_isSharedCheck_2680_: u8 = 0;
    let mut v_binderName_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2684_: u8 = 0;
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v_fst_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2702_: u8 = 0;
    let mut v___y_2704_: u8 = 0;
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    let mut v___x_2713_: u8 = 0;
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v_declName_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2720_: u8 = 0;
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2738_: u8 = 0;
    let mut v_fst_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2743_: u8 = 0;
    let mut v___y_2745_: u8 = 0;
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: u8 = 0;
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___x_2756_: u8 = 0;
    let mut v_isSharedCheck_2757_: u8 = 0;
    let mut v_isSharedCheck_2758_: u8 = 0;
    let mut v_data_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v_fst_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2780_: u8 = 0;
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v_typeName_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2790_: u8 = 0;
    let mut v_fst_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_2610_) {
                5 => {
                    v_fn_2615_ = crate::leanh::lean_ctor_get(v_e_2610_, 0);
                    v_arg_2616_ = crate::leanh::lean_ctor_get(v_e_2610_, 1);
                    crate::leanh::lean_inc(v_offset_2611_);
                    crate::leanh::lean_inc_ref(v_fn_2615_);
                    v___x_2617_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_fn_2615_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2618_ = crate::leanh::lean_ctor_get(v___x_2617_, 0);
                    crate::leanh::lean_inc(v_fst_2618_);
                    v_snd_2619_ = crate::leanh::lean_ctor_get(v___x_2617_, 1);
                    crate::leanh::lean_inc(v_snd_2619_);
                    crate::leanh::lean_dec_ref(v___x_2617_);
                    v_fst_2620_ = crate::leanh::lean_ctor_get(v_fst_2618_, 0);
                    crate::leanh::lean_inc(v_fst_2620_);
                    v_snd_2621_ = crate::leanh::lean_ctor_get(v_fst_2618_, 1);
                    crate::leanh::lean_inc(v_snd_2621_);
                    crate::leanh::lean_dec(v_fst_2618_);
                    crate::leanh::lean_inc_ref(v_arg_2616_);
                    v___x_2622_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_arg_2616_, v_offset_2611_, v_snd_2621_, v_a_2613_, v_snd_2619_);
                    v_fst_2623_ = crate::leanh::lean_ctor_get(v___x_2622_, 0);
                    v_snd_2624_ = crate::leanh::lean_ctor_get(v___x_2622_, 1);
                    v_isSharedCheck_2645_ = (!crate::leanh::lean_is_exclusive(v___x_2622_)) as u8;
                    if v_isSharedCheck_2645_ == 0 {
                        v___x_2626_ = v___x_2622_;
                        v_isShared_2627_ = v_isSharedCheck_2645_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2624_);
                        crate::leanh::lean_inc(v_fst_2623_);
                        crate::leanh::lean_dec(v___x_2622_);
                        v___x_2626_ = crate::leanh::lean_box(0);
                        v_isShared_2627_ = v_isSharedCheck_2645_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_2646_ = crate::leanh::lean_ctor_get(v_e_2610_, 0);
                    v_binderType_2647_ = crate::leanh::lean_ctor_get(v_e_2610_, 1);
                    v_body_2648_ = crate::leanh::lean_ctor_get(v_e_2610_, 2);
                    v_binderInfo_2649_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_2610_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc(v_offset_2611_);
                    crate::leanh::lean_inc_ref(v_binderType_2647_);
                    v___x_2650_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_binderType_2647_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2651_ = crate::leanh::lean_ctor_get(v___x_2650_, 0);
                    crate::leanh::lean_inc(v_fst_2651_);
                    v_snd_2652_ = crate::leanh::lean_ctor_get(v___x_2650_, 1);
                    crate::leanh::lean_inc(v_snd_2652_);
                    crate::leanh::lean_dec_ref(v___x_2650_);
                    v_fst_2653_ = crate::leanh::lean_ctor_get(v_fst_2651_, 0);
                    crate::leanh::lean_inc(v_fst_2653_);
                    v_snd_2654_ = crate::leanh::lean_ctor_get(v_fst_2651_, 1);
                    crate::leanh::lean_inc(v_snd_2654_);
                    crate::leanh::lean_dec(v_fst_2651_);
                    v___x_2655_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2656_ = lean_nat_add(v_offset_2611_, v___x_2655_);
                    crate::leanh::lean_dec(v_offset_2611_);
                    crate::leanh::lean_inc_ref(v_body_2648_);
                    v___x_2657_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_body_2648_, v___x_2656_, v_snd_2654_, v_a_2613_, v_snd_2652_);
                    v_fst_2658_ = crate::leanh::lean_ctor_get(v___x_2657_, 0);
                    v_snd_2659_ = crate::leanh::lean_ctor_get(v___x_2657_, 1);
                    v_isSharedCheck_2680_ = (!crate::leanh::lean_is_exclusive(v___x_2657_)) as u8;
                    if v_isSharedCheck_2680_ == 0 {
                        v___x_2661_ = v___x_2657_;
                        v_isShared_2662_ = v_isSharedCheck_2680_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2659_);
                        crate::leanh::lean_inc(v_fst_2658_);
                        crate::leanh::lean_dec(v___x_2657_);
                        v___x_2661_ = crate::leanh::lean_box(0);
                        v_isShared_2662_ = v_isSharedCheck_2680_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_2681_ = crate::leanh::lean_ctor_get(v_e_2610_, 0);
                    v_binderType_2682_ = crate::leanh::lean_ctor_get(v_e_2610_, 1);
                    v_body_2683_ = crate::leanh::lean_ctor_get(v_e_2610_, 2);
                    v_binderInfo_2684_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_2610_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc(v_offset_2611_);
                    crate::leanh::lean_inc_ref(v_binderType_2682_);
                    v___x_2685_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_binderType_2682_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2686_ = crate::leanh::lean_ctor_get(v___x_2685_, 0);
                    crate::leanh::lean_inc(v_fst_2686_);
                    v_snd_2687_ = crate::leanh::lean_ctor_get(v___x_2685_, 1);
                    crate::leanh::lean_inc(v_snd_2687_);
                    crate::leanh::lean_dec_ref(v___x_2685_);
                    v_fst_2688_ = crate::leanh::lean_ctor_get(v_fst_2686_, 0);
                    crate::leanh::lean_inc(v_fst_2688_);
                    v_snd_2689_ = crate::leanh::lean_ctor_get(v_fst_2686_, 1);
                    crate::leanh::lean_inc(v_snd_2689_);
                    crate::leanh::lean_dec(v_fst_2686_);
                    v___x_2690_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2691_ = lean_nat_add(v_offset_2611_, v___x_2690_);
                    crate::leanh::lean_dec(v_offset_2611_);
                    crate::leanh::lean_inc_ref(v_body_2683_);
                    v___x_2692_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_body_2683_, v___x_2691_, v_snd_2689_, v_a_2613_, v_snd_2687_);
                    v_fst_2693_ = crate::leanh::lean_ctor_get(v___x_2692_, 0);
                    v_snd_2694_ = crate::leanh::lean_ctor_get(v___x_2692_, 1);
                    v_isSharedCheck_2715_ = (!crate::leanh::lean_is_exclusive(v___x_2692_)) as u8;
                    if v_isSharedCheck_2715_ == 0 {
                        v___x_2696_ = v___x_2692_;
                        v_isShared_2697_ = v_isSharedCheck_2715_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2694_);
                        crate::leanh::lean_inc(v_fst_2693_);
                        crate::leanh::lean_dec(v___x_2692_);
                        v___x_2696_ = crate::leanh::lean_box(0);
                        v_isShared_2697_ = v_isSharedCheck_2715_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_2716_ = crate::leanh::lean_ctor_get(v_e_2610_, 0);
                    v_type_2717_ = crate::leanh::lean_ctor_get(v_e_2610_, 1);
                    v_value_2718_ = crate::leanh::lean_ctor_get(v_e_2610_, 2);
                    v_body_2719_ = crate::leanh::lean_ctor_get(v_e_2610_, 3);
                    v_nondep_2720_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_2610_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_n(v_offset_2611_, 2);
                    crate::leanh::lean_inc_ref(v_type_2717_);
                    v___x_2721_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_type_2717_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2722_ = crate::leanh::lean_ctor_get(v___x_2721_, 0);
                    crate::leanh::lean_inc(v_fst_2722_);
                    v_snd_2723_ = crate::leanh::lean_ctor_get(v___x_2721_, 1);
                    crate::leanh::lean_inc(v_snd_2723_);
                    crate::leanh::lean_dec_ref(v___x_2721_);
                    v_fst_2724_ = crate::leanh::lean_ctor_get(v_fst_2722_, 0);
                    crate::leanh::lean_inc(v_fst_2724_);
                    v_snd_2725_ = crate::leanh::lean_ctor_get(v_fst_2722_, 1);
                    crate::leanh::lean_inc(v_snd_2725_);
                    crate::leanh::lean_dec(v_fst_2722_);
                    crate::leanh::lean_inc_ref(v_value_2718_);
                    v___x_2726_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_value_2718_, v_offset_2611_, v_snd_2725_, v_a_2613_, v_snd_2723_);
                    v_fst_2727_ = crate::leanh::lean_ctor_get(v___x_2726_, 0);
                    crate::leanh::lean_inc(v_fst_2727_);
                    v_snd_2728_ = crate::leanh::lean_ctor_get(v___x_2726_, 1);
                    crate::leanh::lean_inc(v_snd_2728_);
                    crate::leanh::lean_dec_ref(v___x_2726_);
                    v_fst_2729_ = crate::leanh::lean_ctor_get(v_fst_2727_, 0);
                    crate::leanh::lean_inc(v_fst_2729_);
                    v_snd_2730_ = crate::leanh::lean_ctor_get(v_fst_2727_, 1);
                    crate::leanh::lean_inc(v_snd_2730_);
                    crate::leanh::lean_dec(v_fst_2727_);
                    v___x_2731_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2732_ = lean_nat_add(v_offset_2611_, v___x_2731_);
                    crate::leanh::lean_dec(v_offset_2611_);
                    crate::leanh::lean_inc_ref(v_body_2719_);
                    v___x_2733_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_body_2719_, v___x_2732_, v_snd_2730_, v_a_2613_, v_snd_2728_);
                    v_fst_2734_ = crate::leanh::lean_ctor_get(v___x_2733_, 0);
                    v_snd_2735_ = crate::leanh::lean_ctor_get(v___x_2733_, 1);
                    v_isSharedCheck_2758_ = (!crate::leanh::lean_is_exclusive(v___x_2733_)) as u8;
                    if v_isSharedCheck_2758_ == 0 {
                        v___x_2737_ = v___x_2733_;
                        v_isShared_2738_ = v_isSharedCheck_2758_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2735_);
                        crate::leanh::lean_inc(v_fst_2734_);
                        crate::leanh::lean_dec(v___x_2733_);
                        v___x_2737_ = crate::leanh::lean_box(0);
                        v_isShared_2738_ = v_isSharedCheck_2758_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_2759_ = crate::leanh::lean_ctor_get(v_e_2610_, 0);
                    v_expr_2760_ = crate::leanh::lean_ctor_get(v_e_2610_, 1);
                    crate::leanh::lean_inc_ref(v_expr_2760_);
                    v___x_2761_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_expr_2760_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2762_ = crate::leanh::lean_ctor_get(v___x_2761_, 0);
                    v_snd_2763_ = crate::leanh::lean_ctor_get(v___x_2761_, 1);
                    v_isSharedCheck_2781_ = (!crate::leanh::lean_is_exclusive(v___x_2761_)) as u8;
                    if v_isSharedCheck_2781_ == 0 {
                        v___x_2765_ = v___x_2761_;
                        v_isShared_2766_ = v_isSharedCheck_2781_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2763_);
                        crate::leanh::lean_inc(v_fst_2762_);
                        crate::leanh::lean_dec(v___x_2761_);
                        v___x_2765_ = crate::leanh::lean_box(0);
                        v_isShared_2766_ = v_isSharedCheck_2781_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_2782_ = crate::leanh::lean_ctor_get(v_e_2610_, 0);
                    v_idx_2783_ = crate::leanh::lean_ctor_get(v_e_2610_, 1);
                    v_struct_2784_ = crate::leanh::lean_ctor_get(v_e_2610_, 2);
                    crate::leanh::lean_inc_ref(v_struct_2784_);
                    v___x_2785_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_struct_2784_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2786_ = crate::leanh::lean_ctor_get(v___x_2785_, 0);
                    v_snd_2787_ = crate::leanh::lean_ctor_get(v___x_2785_, 1);
                    v_isSharedCheck_2805_ = (!crate::leanh::lean_is_exclusive(v___x_2785_)) as u8;
                    if v_isSharedCheck_2805_ == 0 {
                        v___x_2789_ = v___x_2785_;
                        v_isShared_2790_ = v_isSharedCheck_2805_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2787_);
                        crate::leanh::lean_inc(v_fst_2786_);
                        crate::leanh::lean_dec(v___x_2785_);
                        v___x_2789_ = crate::leanh::lean_box(0);
                        v_isShared_2790_ = v_isSharedCheck_2805_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_offset_2611_);
                    crate::leanh::lean_dec_ref(v_e_2610_);
                    v___x_2806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
                    v___x_2807_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_2806_, v_a_2612_, v_a_2613_, v_a_2614_);
                    return v___x_2807_;
                }
            },
            1 => {
                v_fst_2628_ = crate::leanh::lean_ctor_get(v_fst_2623_, 0);
                v_snd_2629_ = crate::leanh::lean_ctor_get(v_fst_2623_, 1);
                v_isSharedCheck_2644_ = (!crate::leanh::lean_is_exclusive(v_fst_2623_)) as u8;
                if v_isSharedCheck_2644_ == 0 {
                    v___x_2631_ = v_fst_2623_;
                    v_isShared_2632_ = v_isSharedCheck_2644_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2629_);
                    crate::leanh::lean_inc(v_fst_2628_);
                    crate::leanh::lean_dec(v_fst_2623_);
                    v___x_2631_ = crate::leanh::lean_box(0);
                    v_isShared_2632_ = v_isSharedCheck_2644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2642_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_fn_2615_,
                        v_fst_2620_,
                    );
                if v___x_2642_ == 0 {
                    v___y_2634_ = v___x_2642_;
                    state = 3;
                    continue;
                } else {
                    v___x_2643_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_2616_,
                            v_fst_2628_,
                        );
                    v___y_2634_ = v___x_2643_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_2634_ == 0 {
                    crate::leanh::lean_del_object(v___x_2631_);
                    crate::leanh::lean_del_object(v___x_2626_);
                    crate::leanh::lean_dec_ref_known(v_e_2610_, 2);
                    v___x_2635_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_2620_, v_fst_2628_, v_snd_2629_, v_a_2613_, v_snd_2624_);
                    return v___x_2635_;
                } else {
                    crate::leanh::lean_dec(v_fst_2628_);
                    crate::leanh::lean_dec(v_fst_2620_);
                    if v_isShared_2632_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2631_, 0, v_e_2610_);
                        v___x_2637_ = v___x_2631_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_e_2610_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_snd_2629_);
                        v___x_2637_ = v_reuseFailAlloc_2641_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2627_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2626_, 0, v___x_2637_);
                    v___x_2639_ = v___x_2626_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2640_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_snd_2624_);
                    v___x_2639_ = v_reuseFailAlloc_2640_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2639_;
            }
            6 => {
                v_fst_2663_ = crate::leanh::lean_ctor_get(v_fst_2658_, 0);
                v_snd_2664_ = crate::leanh::lean_ctor_get(v_fst_2658_, 1);
                v_isSharedCheck_2679_ = (!crate::leanh::lean_is_exclusive(v_fst_2658_)) as u8;
                if v_isSharedCheck_2679_ == 0 {
                    v___x_2666_ = v_fst_2658_;
                    v_isShared_2667_ = v_isSharedCheck_2679_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2664_);
                    crate::leanh::lean_inc(v_fst_2663_);
                    crate::leanh::lean_dec(v_fst_2658_);
                    v___x_2666_ = crate::leanh::lean_box(0);
                    v_isShared_2667_ = v_isSharedCheck_2679_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2677_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_2647_,
                        v_fst_2653_,
                    );
                if v___x_2677_ == 0 {
                    v___y_2669_ = v___x_2677_;
                    state = 8;
                    continue;
                } else {
                    v___x_2678_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_2648_,
                            v_fst_2663_,
                        );
                    v___y_2669_ = v___x_2678_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_2669_ == 0 {
                    crate::leanh::lean_inc(v_binderName_2646_);
                    crate::leanh::lean_del_object(v___x_2666_);
                    crate::leanh::lean_del_object(v___x_2661_);
                    crate::leanh::lean_dec_ref_known(v_e_2610_, 3);
                    v___x_2670_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_2646_, v_binderInfo_2649_, v_fst_2653_, v_fst_2663_, v_snd_2664_, v_a_2613_, v_snd_2659_);
                    return v___x_2670_;
                } else {
                    crate::leanh::lean_dec(v_fst_2663_);
                    crate::leanh::lean_dec(v_fst_2653_);
                    if v_isShared_2667_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2666_, 0, v_e_2610_);
                        v___x_2672_ = v___x_2666_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2676_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_e_2610_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_snd_2664_);
                        v___x_2672_ = v_reuseFailAlloc_2676_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2662_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2661_, 0, v___x_2672_);
                    v___x_2674_ = v___x_2661_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2675_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_snd_2659_);
                    v___x_2674_ = v_reuseFailAlloc_2675_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2674_;
            }
            11 => {
                v_fst_2698_ = crate::leanh::lean_ctor_get(v_fst_2693_, 0);
                v_snd_2699_ = crate::leanh::lean_ctor_get(v_fst_2693_, 1);
                v_isSharedCheck_2714_ = (!crate::leanh::lean_is_exclusive(v_fst_2693_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v___x_2701_ = v_fst_2693_;
                    v_isShared_2702_ = v_isSharedCheck_2714_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2699_);
                    crate::leanh::lean_inc(v_fst_2698_);
                    crate::leanh::lean_dec(v_fst_2693_);
                    v___x_2701_ = crate::leanh::lean_box(0);
                    v_isShared_2702_ = v_isSharedCheck_2714_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2712_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_2682_,
                        v_fst_2688_,
                    );
                if v___x_2712_ == 0 {
                    v___y_2704_ = v___x_2712_;
                    state = 13;
                    continue;
                } else {
                    v___x_2713_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_2683_,
                            v_fst_2698_,
                        );
                    v___y_2704_ = v___x_2713_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_2704_ == 0 {
                    crate::leanh::lean_inc(v_binderName_2681_);
                    crate::leanh::lean_del_object(v___x_2701_);
                    crate::leanh::lean_del_object(v___x_2696_);
                    crate::leanh::lean_dec_ref_known(v_e_2610_, 3);
                    v___x_2705_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_2681_, v_binderInfo_2684_, v_fst_2688_, v_fst_2698_, v_snd_2699_, v_a_2613_, v_snd_2694_);
                    return v___x_2705_;
                } else {
                    crate::leanh::lean_dec(v_fst_2698_);
                    crate::leanh::lean_dec(v_fst_2688_);
                    if v_isShared_2702_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2701_, 0, v_e_2610_);
                        v___x_2707_ = v___x_2701_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2711_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_e_2610_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_snd_2699_);
                        v___x_2707_ = v_reuseFailAlloc_2711_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2697_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2696_, 0, v___x_2707_);
                    v___x_2709_ = v___x_2696_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_snd_2694_);
                    v___x_2709_ = v_reuseFailAlloc_2710_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2709_;
            }
            16 => {
                v_fst_2739_ = crate::leanh::lean_ctor_get(v_fst_2734_, 0);
                v_snd_2740_ = crate::leanh::lean_ctor_get(v_fst_2734_, 1);
                v_isSharedCheck_2757_ = (!crate::leanh::lean_is_exclusive(v_fst_2734_)) as u8;
                if v_isSharedCheck_2757_ == 0 {
                    v___x_2742_ = v_fst_2734_;
                    v_isShared_2743_ = v_isSharedCheck_2757_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2740_);
                    crate::leanh::lean_inc(v_fst_2739_);
                    crate::leanh::lean_dec(v_fst_2734_);
                    v___x_2742_ = crate::leanh::lean_box(0);
                    v_isShared_2743_ = v_isSharedCheck_2757_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2755_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_2717_,
                        v_fst_2724_,
                    );
                if v___x_2755_ == 0 {
                    v___y_2745_ = v___x_2755_;
                    state = 18;
                    continue;
                } else {
                    v___x_2756_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_value_2718_,
                            v_fst_2729_,
                        );
                    v___y_2745_ = v___x_2756_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_2745_ == 0 {
                    crate::leanh::lean_inc(v_declName_2716_);
                    crate::leanh::lean_del_object(v___x_2742_);
                    crate::leanh::lean_del_object(v___x_2737_);
                    crate::leanh::lean_dec_ref_known(v_e_2610_, 4);
                    v___x_2746_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_2716_, v_fst_2724_, v_fst_2729_, v_fst_2739_, v_nondep_2720_, v_snd_2740_, v_a_2613_, v_snd_2735_);
                    return v___x_2746_;
                } else {
                    v___x_2747_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_2719_,
                            v_fst_2739_,
                        );
                    if v___x_2747_ == 0 {
                        crate::leanh::lean_inc(v_declName_2716_);
                        crate::leanh::lean_del_object(v___x_2742_);
                        crate::leanh::lean_del_object(v___x_2737_);
                        crate::leanh::lean_dec_ref_known(v_e_2610_, 4);
                        v___x_2748_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_2716_, v_fst_2724_, v_fst_2729_, v_fst_2739_, v_nondep_2720_, v_snd_2740_, v_a_2613_, v_snd_2735_);
                        return v___x_2748_;
                    } else {
                        crate::leanh::lean_dec(v_fst_2739_);
                        crate::leanh::lean_dec(v_fst_2729_);
                        crate::leanh::lean_dec(v_fst_2724_);
                        if v_isShared_2743_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2742_, 0, v_e_2610_);
                            v___x_2750_ = v___x_2742_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_2754_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_e_2610_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_snd_2740_);
                            v___x_2750_ = v_reuseFailAlloc_2754_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_2738_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2737_, 0, v___x_2750_);
                    v___x_2752_ = v___x_2737_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2753_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_snd_2735_);
                    v___x_2752_ = v_reuseFailAlloc_2753_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2752_;
            }
            21 => {
                v_fst_2767_ = crate::leanh::lean_ctor_get(v_fst_2762_, 0);
                v_snd_2768_ = crate::leanh::lean_ctor_get(v_fst_2762_, 1);
                v_isSharedCheck_2780_ = (!crate::leanh::lean_is_exclusive(v_fst_2762_)) as u8;
                if v_isSharedCheck_2780_ == 0 {
                    v___x_2770_ = v_fst_2762_;
                    v_isShared_2771_ = v_isSharedCheck_2780_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2768_);
                    crate::leanh::lean_inc(v_fst_2767_);
                    crate::leanh::lean_dec(v_fst_2762_);
                    v___x_2770_ = crate::leanh::lean_box(0);
                    v_isShared_2771_ = v_isSharedCheck_2780_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_2772_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_expr_2760_,
                        v_fst_2767_,
                    );
                if v___x_2772_ == 0 {
                    crate::leanh::lean_inc(v_data_2759_);
                    crate::leanh::lean_del_object(v___x_2770_);
                    crate::leanh::lean_del_object(v___x_2765_);
                    crate::leanh::lean_dec_ref_known(v_e_2610_, 2);
                    v___x_2773_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_2759_, v_fst_2767_, v_snd_2768_, v_a_2613_, v_snd_2763_);
                    return v___x_2773_;
                } else {
                    crate::leanh::lean_dec(v_fst_2767_);
                    if v_isShared_2771_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2770_, 0, v_e_2610_);
                        v___x_2775_ = v___x_2770_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2779_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_e_2610_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_snd_2768_);
                        v___x_2775_ = v_reuseFailAlloc_2779_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_2766_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2765_, 0, v___x_2775_);
                    v___x_2777_ = v___x_2765_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_snd_2763_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2777_;
            }
            25 => {
                v_fst_2791_ = crate::leanh::lean_ctor_get(v_fst_2786_, 0);
                v_snd_2792_ = crate::leanh::lean_ctor_get(v_fst_2786_, 1);
                v_isSharedCheck_2804_ = (!crate::leanh::lean_is_exclusive(v_fst_2786_)) as u8;
                if v_isSharedCheck_2804_ == 0 {
                    v___x_2794_ = v_fst_2786_;
                    v_isShared_2795_ = v_isSharedCheck_2804_;
                    state = 26;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2792_);
                    crate::leanh::lean_inc(v_fst_2791_);
                    crate::leanh::lean_dec(v_fst_2786_);
                    v___x_2794_ = crate::leanh::lean_box(0);
                    v_isShared_2795_ = v_isSharedCheck_2804_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_2796_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_struct_2784_,
                        v_fst_2791_,
                    );
                if v___x_2796_ == 0 {
                    crate::leanh::lean_inc(v_idx_2783_);
                    crate::leanh::lean_inc(v_typeName_2782_);
                    crate::leanh::lean_del_object(v___x_2794_);
                    crate::leanh::lean_del_object(v___x_2789_);
                    crate::leanh::lean_dec_ref_known(v_e_2610_, 3);
                    v___x_2797_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_2782_, v_idx_2783_, v_fst_2791_, v_snd_2792_, v_a_2613_, v_snd_2787_);
                    return v___x_2797_;
                } else {
                    crate::leanh::lean_dec(v_fst_2791_);
                    if v_isShared_2795_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2794_, 0, v_e_2610_);
                        v___x_2799_ = v___x_2794_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_2803_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_e_2610_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_snd_2792_);
                        v___x_2799_ = v_reuseFailAlloc_2803_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2790_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2789_, 0, v___x_2799_);
                    v___x_2801_ = v___x_2789_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_snd_2787_);
                    v___x_2801_ = v_reuseFailAlloc_2802_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(
    mut v_beginIdx_2808_: *mut crate::leanh::LeanObject,
    mut v_n_2809_: *mut crate::leanh::LeanObject,
    mut v_subst_2810_: *mut crate::leanh::LeanObject,
    mut v_e_2811_: *mut crate::leanh::LeanObject,
    mut v_offset_2812_: *mut crate::leanh::LeanObject,
    mut v_a_2813_: *mut crate::leanh::LeanObject,
    mut v_a_2814_: u8,
    mut v_a_2815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_offset_2812_);
    crate::leanh::lean_inc_ref(v_e_2811_);
    v_key_2816_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_key_2816_, 0, v_e_2811_);
    crate::leanh::lean_ctor_set(v_key_2816_, 1, v_offset_2812_);
    v___x_2817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_2813_, v_key_2816_);
    if crate::leanh::lean_obj_tag(v___x_2817_) == 1 {
        let mut v_val_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v_key_2816_, 2);
        crate::leanh::lean_dec(v_offset_2812_);
        crate::leanh::lean_dec_ref(v_e_2811_);
        v_val_2818_ = crate::leanh::lean_ctor_get(v___x_2817_, 0);
        crate::leanh::lean_inc(v_val_2818_);
        crate::leanh::lean_dec_ref_known(v___x_2817_, 1);
        v___x_2819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2819_, 0, v_val_2818_);
        crate::leanh::lean_ctor_set(v___x_2819_, 1, v_a_2813_);
        v___x_2820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2820_, 0, v___x_2819_);
        crate::leanh::lean_ctor_set(v___x_2820_, 1, v_a_2815_);
        return v___x_2820_;
    } else {
        let mut v_s_u2081_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_2817_);
        v_s_u2081_2821_ = lean_nat_add(v_beginIdx_2808_, v_offset_2812_);
        match crate::leanh::lean_obj_tag(v_e_2811_) {
            0 => {
                let mut v_deBruijnIndex_2822_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v___x_2823_: u8 = 0;
                v_deBruijnIndex_2822_ = crate::leanh::lean_ctor_get(v_e_2811_, 0);
                v___x_2823_ = lean_nat_dec_le(v_s_u2081_2821_, v_deBruijnIndex_2822_);
                crate::leanh::lean_dec(v_s_u2081_2821_);
                if v___x_2823_ == 0 {
                    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_offset_2812_);
                    v___x_2824_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2816_,
                        v_e_2811_,
                        v_a_2813_,
                        v_a_2814_,
                        v_a_2815_,
                    );
                    return v___x_2824_;
                } else {
                    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2826_: u8 = 0;
                    crate::leanh::lean_inc(v_deBruijnIndex_2822_);
                    crate::leanh::lean_dec_ref_known(v_e_2811_, 1);
                    v___x_2825_ = lean_nat_add(v_offset_2812_, v_n_2809_);
                    v___x_2826_ = lean_nat_dec_lt(v_deBruijnIndex_2822_, v___x_2825_);
                    crate::leanh::lean_dec(v___x_2825_);
                    if v___x_2826_ == 0 {
                        let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_fst_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_snd_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_offset_2812_);
                        v___x_2827_ = lean_nat_sub(v_deBruijnIndex_2822_, v_n_2809_);
                        crate::leanh::lean_dec(v_deBruijnIndex_2822_);
                        v___x_2828_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_2827_, v_a_2815_);
                        v_fst_2829_ = crate::leanh::lean_ctor_get(v___x_2828_, 0);
                        crate::leanh::lean_inc(v_fst_2829_);
                        v_snd_2830_ = crate::leanh::lean_ctor_get(v___x_2828_, 1);
                        crate::leanh::lean_inc(v_snd_2830_);
                        crate::leanh::lean_dec_ref(v___x_2828_);
                        v___x_2831_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                            v_key_2816_,
                            v_fst_2829_,
                            v_a_2813_,
                            v_a_2814_,
                            v_snd_2830_,
                        );
                        return v___x_2831_;
                    } else {
                        let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_v_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_fst_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_snd_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2832_ = lean_nat_sub(v_deBruijnIndex_2822_, v_offset_2812_);
                        crate::leanh::lean_dec(v_deBruijnIndex_2822_);
                        v___x_2833_ = lean_nat_sub(v_n_2809_, v___x_2832_);
                        crate::leanh::lean_dec(v___x_2832_);
                        v___x_2834_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2835_ = lean_nat_sub(v___x_2833_, v___x_2834_);
                        crate::leanh::lean_dec(v___x_2833_);
                        v_v_2836_ = lean_array_fget_borrowed(v_subst_2810_, v___x_2835_);
                        crate::leanh::lean_dec(v___x_2835_);
                        v___x_2837_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc(v_v_2836_);
                        v___x_2838_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                            v_v_2836_,
                            v___x_2837_,
                            v_offset_2812_,
                            v_a_2814_,
                            v_a_2815_,
                        );
                        crate::leanh::lean_dec(v_offset_2812_);
                        v_fst_2839_ = crate::leanh::lean_ctor_get(v___x_2838_, 0);
                        crate::leanh::lean_inc(v_fst_2839_);
                        v_snd_2840_ = crate::leanh::lean_ctor_get(v___x_2838_, 1);
                        crate::leanh::lean_inc(v_snd_2840_);
                        crate::leanh::lean_dec_ref(v___x_2838_);
                        v___x_2841_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                            v_key_2816_,
                            v_fst_2839_,
                            v_a_2813_,
                            v_a_2814_,
                            v_snd_2840_,
                        );
                        return v___x_2841_;
                    }
                }
            }
            9 => {
                let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_s_u2081_2821_);
                crate::leanh::lean_dec(v_offset_2812_);
                v___x_2842_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                    v_key_2816_,
                    v_e_2811_,
                    v_a_2813_,
                    v_a_2814_,
                    v_a_2815_,
                );
                return v___x_2842_;
            }
            2 => {
                let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_s_u2081_2821_);
                crate::leanh::lean_dec(v_offset_2812_);
                v___x_2843_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                    v_key_2816_,
                    v_e_2811_,
                    v_a_2813_,
                    v_a_2814_,
                    v_a_2815_,
                );
                return v___x_2843_;
            }
            1 => {
                let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_s_u2081_2821_);
                crate::leanh::lean_dec(v_offset_2812_);
                v___x_2844_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                    v_key_2816_,
                    v_e_2811_,
                    v_a_2813_,
                    v_a_2814_,
                    v_a_2815_,
                );
                return v___x_2844_;
            }
            4 => {
                let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_s_u2081_2821_);
                crate::leanh::lean_dec(v_offset_2812_);
                v___x_2845_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                    v_key_2816_,
                    v_e_2811_,
                    v_a_2813_,
                    v_a_2814_,
                    v_a_2815_,
                );
                return v___x_2845_;
            }
            3 => {
                let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_s_u2081_2821_);
                crate::leanh::lean_dec(v_offset_2812_);
                v___x_2846_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                    v_key_2816_,
                    v_e_2811_,
                    v_a_2813_,
                    v_a_2814_,
                    v_a_2815_,
                );
                return v___x_2846_;
            }
            _ => {
                let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2848_: u8 = 0;
                v___x_2847_ = l_Lean_Expr_looseBVarRange(v_e_2811_);
                v___x_2848_ = lean_nat_dec_le(v___x_2847_, v_s_u2081_2821_);
                crate::leanh::lean_dec(v_s_u2081_2821_);
                crate::leanh::lean_dec(v___x_2847_);
                if v___x_2848_ == 0 {
                    match crate::leanh::lean_obj_tag(v_e_2811_) {
                        9 => {
                            let mut v___x_2849_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_2812_);
                            v___x_2849_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2816_,
                                v_e_2811_,
                                v_a_2813_,
                                v_a_2814_,
                                v_a_2815_,
                            );
                            return v___x_2849_;
                        }
                        2 => {
                            let mut v___x_2850_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_2812_);
                            v___x_2850_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2816_,
                                v_e_2811_,
                                v_a_2813_,
                                v_a_2814_,
                                v_a_2815_,
                            );
                            return v___x_2850_;
                        }
                        0 => {
                            let mut v___x_2851_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_2812_);
                            v___x_2851_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2816_,
                                v_e_2811_,
                                v_a_2813_,
                                v_a_2814_,
                                v_a_2815_,
                            );
                            return v___x_2851_;
                        }
                        1 => {
                            let mut v___x_2852_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_2812_);
                            v___x_2852_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2816_,
                                v_e_2811_,
                                v_a_2813_,
                                v_a_2814_,
                                v_a_2815_,
                            );
                            return v___x_2852_;
                        }
                        4 => {
                            let mut v___x_2853_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_2812_);
                            v___x_2853_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2816_,
                                v_e_2811_,
                                v_a_2813_,
                                v_a_2814_,
                                v_a_2815_,
                            );
                            return v___x_2853_;
                        }
                        3 => {
                            let mut v___x_2854_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_2812_);
                            v___x_2854_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2816_,
                                v_e_2811_,
                                v_a_2813_,
                                v_a_2814_,
                                v_a_2815_,
                            );
                            return v___x_2854_;
                        }
                        _ => {
                            let mut v___x_2855_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_fst_2856_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_snd_2857_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_fst_2858_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_snd_2859_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2860_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_2855_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_2808_, v_n_2809_, v_subst_2810_, v_e_2811_, v_offset_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
                            v_fst_2856_ = crate::leanh::lean_ctor_get(v___x_2855_, 0);
                            crate::leanh::lean_inc(v_fst_2856_);
                            v_snd_2857_ = crate::leanh::lean_ctor_get(v___x_2855_, 1);
                            crate::leanh::lean_inc(v_snd_2857_);
                            crate::leanh::lean_dec_ref(v___x_2855_);
                            v_fst_2858_ = crate::leanh::lean_ctor_get(v_fst_2856_, 0);
                            crate::leanh::lean_inc(v_fst_2858_);
                            v_snd_2859_ = crate::leanh::lean_ctor_get(v_fst_2856_, 1);
                            crate::leanh::lean_inc(v_snd_2859_);
                            crate::leanh::lean_dec(v_fst_2856_);
                            v___x_2860_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_2816_,
                                v_fst_2858_,
                                v_snd_2859_,
                                v_a_2814_,
                                v_snd_2857_,
                            );
                            return v___x_2860_;
                        }
                    }
                } else {
                    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_offset_2812_);
                    v___x_2861_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2816_,
                        v_e_2811_,
                        v_a_2813_,
                        v_a_2814_,
                        v_a_2815_,
                    );
                    return v___x_2861_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2___boxed(
    mut v_beginIdx_2862_: *mut crate::leanh::LeanObject,
    mut v_n_2863_: *mut crate::leanh::LeanObject,
    mut v_subst_2864_: *mut crate::leanh::LeanObject,
    mut v_e_2865_: *mut crate::leanh::LeanObject,
    mut v_offset_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
    mut v_a_2868_: *mut crate::leanh::LeanObject,
    mut v_a_2869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2870_: u8 = 0;
    let mut v_res_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2870_ = (crate::leanh::lean_unbox(v_a_2868_) as u8);
    v_res_2871_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2862_, v_n_2863_, v_subst_2864_, v_e_2865_, v_offset_2866_, v_a_2867_, v_a_boxed_2870_, v_a_2869_);
    crate::leanh::lean_dec_ref(v_subst_2864_);
    crate::leanh::lean_dec(v_n_2863_);
    crate::leanh::lean_dec(v_beginIdx_2862_);
    return v_res_2871_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(
    mut v_beginIdx_2872_: *mut crate::leanh::LeanObject,
    mut v_n_2873_: *mut crate::leanh::LeanObject,
    mut v_subst_2874_: *mut crate::leanh::LeanObject,
    mut v_e_2875_: *mut crate::leanh::LeanObject,
    mut v_offset_2876_: *mut crate::leanh::LeanObject,
    mut v_a_2877_: *mut crate::leanh::LeanObject,
    mut v_a_2878_: *mut crate::leanh::LeanObject,
    mut v_a_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_2880_: u8 = 0;
    let mut v_res_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2880_ = (crate::leanh::lean_unbox(v_a_2878_) as u8);
    v_res_2881_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_2872_, v_n_2873_, v_subst_2874_, v_e_2875_, v_offset_2876_, v_a_2877_, v_a_boxed_2880_, v_a_2879_);
    crate::leanh::lean_dec_ref(v_subst_2874_);
    crate::leanh::lean_dec(v_n_2873_);
    crate::leanh::lean_dec(v_beginIdx_2872_);
    return v_res_2881_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2882_ =
        l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(
            crate::leanh::lean_box(0),
        );
    return v___x_2882_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2883_ = crate::leanh::lean_box(0);
    v___x_2884_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2885_ = lean_mk_array(v___x_2884_, v___x_2883_);
    return v___x_2885_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2886_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_once),
        _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1,
    );
    v___x_2887_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2888_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2888_, 0, v___x_2887_);
    crate::leanh::lean_ctor_set(v___x_2888_, 1, v___x_2886_);
    return v___x_2888_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2891_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_2892_ = crate::leanh::lean_unsigned_to_nat(34);
    v___x_2893_ = crate::leanh::lean_unsigned_to_nat(20);
    v___x_2894_ = l_Lean_Meta_Sym_instantiateRevRangeS___closed__4;
    v___x_2895_ = l_Lean_Meta_Sym_instantiateRevRangeS___closed__3;
    v___x_2896_ = l_mkPanicMessageWithDecl(
        v___x_2895_,
        v___x_2894_,
        v___x_2893_,
        v___x_2892_,
        v___x_2891_,
    );
    return v___x_2896_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2897_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_2898_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2899_ = crate::leanh::lean_unsigned_to_nat(19);
    v___x_2900_ = l_Lean_Meta_Sym_instantiateRevRangeS___closed__4;
    v___x_2901_ = l_Lean_Meta_Sym_instantiateRevRangeS___closed__3;
    v___x_2902_ = l_mkPanicMessageWithDecl(
        v___x_2901_,
        v___x_2900_,
        v___x_2899_,
        v___x_2898_,
        v___x_2897_,
    );
    return v___x_2902_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevRangeS(
    mut v_e_2903_: *mut crate::leanh::LeanObject,
    mut v_beginIdx_2904_: *mut crate::leanh::LeanObject,
    mut v_endIdx_2905_: *mut crate::leanh::LeanObject,
    mut v_subst_2906_: *mut crate::leanh::LeanObject,
    mut v_a_2907_: *mut crate::leanh::LeanObject,
    mut v_a_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
    mut v_a_2912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2914_: u8 = 0;
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: u8 = 0;
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2928_: u8 = 0;
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2950_: u8 = 0;
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2953_: u8 = 0;
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2959_: u8 = 0;
    let mut v_unused_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_2961_: u8 = 0;
    let mut v_n_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: u8 = 0;
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2986_: u8 = 0;
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2914_ = lean_nat_dec_lt(v_endIdx_2905_, v_beginIdx_2904_);
                if v___x_2914_ == 0 {
                    v___x_2915_ = lean_array_get_size(v_subst_2906_);
                    v___x_2916_ = lean_nat_dec_lt(v___x_2915_, v_endIdx_2905_);
                    if v___x_2916_ == 0 {
                        v___x_2917_ = lean_st_ref_take(v_a_2908_);
                        v_share_2918_ = crate::leanh::lean_ctor_get(v___x_2917_, 0);
                        v_maxFVar_2919_ = crate::leanh::lean_ctor_get(v___x_2917_, 1);
                        v_proofInstInfo_2920_ = crate::leanh::lean_ctor_get(v___x_2917_, 2);
                        v_inferType_2921_ = crate::leanh::lean_ctor_get(v___x_2917_, 3);
                        v_getLevel_2922_ = crate::leanh::lean_ctor_get(v___x_2917_, 4);
                        v_congrInfo_2923_ = crate::leanh::lean_ctor_get(v___x_2917_, 5);
                        v_defEqI_2924_ = crate::leanh::lean_ctor_get(v___x_2917_, 6);
                        v_extensions_2925_ = crate::leanh::lean_ctor_get(v___x_2917_, 7);
                        v_issues_2926_ = crate::leanh::lean_ctor_get(v___x_2917_, 8);
                        v_canon_2927_ = crate::leanh::lean_ctor_get(v___x_2917_, 9);
                        v_debug_2928_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_2917_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        );
                        v_isSharedCheck_2986_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2917_)) as u8;
                        if v_isSharedCheck_2986_ == 0 {
                            v___x_2930_ = v___x_2917_;
                            v_isShared_2931_ = v_isSharedCheck_2986_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_canon_2927_);
                            crate::leanh::lean_inc(v_issues_2926_);
                            crate::leanh::lean_inc(v_extensions_2925_);
                            crate::leanh::lean_inc(v_defEqI_2924_);
                            crate::leanh::lean_inc(v_congrInfo_2923_);
                            crate::leanh::lean_inc(v_getLevel_2922_);
                            crate::leanh::lean_inc(v_inferType_2921_);
                            crate::leanh::lean_inc(v_proofInstInfo_2920_);
                            crate::leanh::lean_inc(v_maxFVar_2919_);
                            crate::leanh::lean_inc(v_share_2918_);
                            crate::leanh::lean_dec(v___x_2917_);
                            v___x_2930_ = crate::leanh::lean_box(0);
                            v_isShared_2931_ = v_isSharedCheck_2986_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2903_);
                        v___x_2987_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Sym_instantiateRevRangeS___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once
                            ),
                            _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5,
                        );
                        v___x_2988_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(
                            v___x_2987_,
                            v_a_2907_,
                            v_a_2908_,
                            v_a_2909_,
                            v_a_2910_,
                            v_a_2911_,
                            v_a_2912_,
                        );
                        return v___x_2988_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2903_);
                    v___x_2989_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once
                        ),
                        _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6,
                    );
                    v___x_2990_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(
                        v___x_2989_,
                        v_a_2907_,
                        v_a_2908_,
                        v_a_2909_,
                        v_a_2910_,
                        v_a_2911_,
                        v_a_2912_,
                    );
                    return v___x_2990_;
                }
            }
            1 => {
                v___x_2932_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once),
                    _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0,
                );
                if v_isShared_2931_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2930_, 0, v___x_2932_);
                    v___x_2934_ = v___x_2930_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2985_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_maxFVar_2919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_proofInstInfo_2920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 3, v_inferType_2921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 4, v_getLevel_2922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 5, v_congrInfo_2923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 6, v_defEqI_2924_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 7, v_extensions_2925_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 8, v_issues_2926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2985_, 9, v_canon_2927_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2985_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_2928_,
                    );
                    v___x_2934_ = v_reuseFailAlloc_2985_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2935_ = lean_st_ref_set(v_a_2908_, v___x_2934_);
                v___x_2936_ = lean_st_ref_get(v_a_2908_);
                v_debug_2961_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2936_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_2936_);
                v_n_2962_ = lean_nat_sub(v_endIdx_2905_, v_beginIdx_2904_);
                v___x_2963_ = crate::leanh::lean_unsigned_to_nat(0);
                match crate::leanh::lean_obj_tag(v_e_2903_) {
                    0 => {
                        v_deBruijnIndex_2964_ = crate::leanh::lean_ctor_get(v_e_2903_, 0);
                        v___x_2965_ = lean_nat_dec_le(v_beginIdx_2904_, v_deBruijnIndex_2964_);
                        if v___x_2965_ == 0 {
                            crate::leanh::lean_dec(v_n_2962_);
                            v_fst_2938_ = v_e_2903_;
                            v_snd_2939_ = v_share_2918_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_deBruijnIndex_2964_);
                            crate::leanh::lean_dec_ref_known(v_e_2903_, 1);
                            v___x_2966_ = lean_nat_dec_lt(v_deBruijnIndex_2964_, v_n_2962_);
                            if v___x_2966_ == 0 {
                                v___x_2967_ = lean_nat_sub(v_deBruijnIndex_2964_, v_n_2962_);
                                crate::leanh::lean_dec(v_n_2962_);
                                crate::leanh::lean_dec(v_deBruijnIndex_2964_);
                                v___x_2968_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_2967_, v_share_2918_);
                                v_fst_2969_ = crate::leanh::lean_ctor_get(v___x_2968_, 0);
                                crate::leanh::lean_inc(v_fst_2969_);
                                v_snd_2970_ = crate::leanh::lean_ctor_get(v___x_2968_, 1);
                                crate::leanh::lean_inc(v_snd_2970_);
                                crate::leanh::lean_dec_ref(v___x_2968_);
                                v_fst_2938_ = v_fst_2969_;
                                v_snd_2939_ = v_snd_2970_;
                                state = 3;
                                continue;
                            } else {
                                v___x_2971_ = lean_nat_sub(v_n_2962_, v_deBruijnIndex_2964_);
                                crate::leanh::lean_dec(v_deBruijnIndex_2964_);
                                crate::leanh::lean_dec(v_n_2962_);
                                v___x_2972_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2973_ = lean_nat_sub(v___x_2971_, v___x_2972_);
                                crate::leanh::lean_dec(v___x_2971_);
                                v_v_2974_ = lean_array_fget_borrowed(v_subst_2906_, v___x_2973_);
                                crate::leanh::lean_dec(v___x_2973_);
                                crate::leanh::lean_inc(v_v_2974_);
                                v___x_2975_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                                    v_v_2974_,
                                    v___x_2963_,
                                    v___x_2963_,
                                    v_debug_2961_,
                                    v_share_2918_,
                                );
                                v_fst_2976_ = crate::leanh::lean_ctor_get(v___x_2975_, 0);
                                crate::leanh::lean_inc(v_fst_2976_);
                                v_snd_2977_ = crate::leanh::lean_ctor_get(v___x_2975_, 1);
                                crate::leanh::lean_inc(v_snd_2977_);
                                crate::leanh::lean_dec_ref(v___x_2975_);
                                v_fst_2938_ = v_fst_2976_;
                                v_snd_2939_ = v_snd_2977_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    9 => {
                        crate::leanh::lean_dec(v_n_2962_);
                        v_fst_2938_ = v_e_2903_;
                        v_snd_2939_ = v_share_2918_;
                        state = 3;
                        continue;
                    }
                    2 => {
                        crate::leanh::lean_dec(v_n_2962_);
                        v_fst_2938_ = v_e_2903_;
                        v_snd_2939_ = v_share_2918_;
                        state = 3;
                        continue;
                    }
                    1 => {
                        crate::leanh::lean_dec(v_n_2962_);
                        v_fst_2938_ = v_e_2903_;
                        v_snd_2939_ = v_share_2918_;
                        state = 3;
                        continue;
                    }
                    4 => {
                        crate::leanh::lean_dec(v_n_2962_);
                        v_fst_2938_ = v_e_2903_;
                        v_snd_2939_ = v_share_2918_;
                        state = 3;
                        continue;
                    }
                    3 => {
                        crate::leanh::lean_dec(v_n_2962_);
                        v_fst_2938_ = v_e_2903_;
                        v_snd_2939_ = v_share_2918_;
                        state = 3;
                        continue;
                    }
                    _ => {
                        v___x_2978_ = l_Lean_Expr_looseBVarRange(v_e_2903_);
                        v___x_2979_ = lean_nat_dec_le(v___x_2978_, v_beginIdx_2904_);
                        crate::leanh::lean_dec(v___x_2978_);
                        if v___x_2979_ == 0 {
                            match crate::leanh::lean_obj_tag(v_e_2903_) {
                                9 => {
                                    crate::leanh::lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                2 => {
                                    crate::leanh::lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                0 => {
                                    crate::leanh::lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                1 => {
                                    crate::leanh::lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                4 => {
                                    crate::leanh::lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                3 => {
                                    crate::leanh::lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                _ => {
                                    v___x_2980_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_instantiateRevRangeS___closed__2
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once
                                        ),
                                        _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2,
                                    );
                                    v___x_2981_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_2904_, v_n_2962_, v_subst_2906_, v_e_2903_, v___x_2963_, v___x_2980_, v_debug_2961_, v_share_2918_);
                                    crate::leanh::lean_dec(v_n_2962_);
                                    v_fst_2982_ = crate::leanh::lean_ctor_get(v___x_2981_, 0);
                                    crate::leanh::lean_inc(v_fst_2982_);
                                    v_snd_2983_ = crate::leanh::lean_ctor_get(v___x_2981_, 1);
                                    crate::leanh::lean_inc(v_snd_2983_);
                                    crate::leanh::lean_dec_ref(v___x_2981_);
                                    v_fst_2984_ = crate::leanh::lean_ctor_get(v_fst_2982_, 0);
                                    crate::leanh::lean_inc(v_fst_2984_);
                                    crate::leanh::lean_dec(v_fst_2982_);
                                    v_fst_2938_ = v_fst_2984_;
                                    v_snd_2939_ = v_snd_2983_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_n_2962_);
                            v_fst_2938_ = v_e_2903_;
                            v_snd_2939_ = v_share_2918_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2940_ = lean_st_ref_take(v_a_2908_);
                v_maxFVar_2941_ = crate::leanh::lean_ctor_get(v___x_2940_, 1);
                v_proofInstInfo_2942_ = crate::leanh::lean_ctor_get(v___x_2940_, 2);
                v_inferType_2943_ = crate::leanh::lean_ctor_get(v___x_2940_, 3);
                v_getLevel_2944_ = crate::leanh::lean_ctor_get(v___x_2940_, 4);
                v_congrInfo_2945_ = crate::leanh::lean_ctor_get(v___x_2940_, 5);
                v_defEqI_2946_ = crate::leanh::lean_ctor_get(v___x_2940_, 6);
                v_extensions_2947_ = crate::leanh::lean_ctor_get(v___x_2940_, 7);
                v_issues_2948_ = crate::leanh::lean_ctor_get(v___x_2940_, 8);
                v_canon_2949_ = crate::leanh::lean_ctor_get(v___x_2940_, 9);
                v_debug_2950_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2940_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2959_ = (!crate::leanh::lean_is_exclusive(v___x_2940_)) as u8;
                if v_isSharedCheck_2959_ == 0 {
                    v_unused_2960_ = crate::leanh::lean_ctor_get(v___x_2940_, 0);
                    crate::leanh::lean_dec(v_unused_2960_);
                    v___x_2952_ = v___x_2940_;
                    v_isShared_2953_ = v_isSharedCheck_2959_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_2949_);
                    crate::leanh::lean_inc(v_issues_2948_);
                    crate::leanh::lean_inc(v_extensions_2947_);
                    crate::leanh::lean_inc(v_defEqI_2946_);
                    crate::leanh::lean_inc(v_congrInfo_2945_);
                    crate::leanh::lean_inc(v_getLevel_2944_);
                    crate::leanh::lean_inc(v_inferType_2943_);
                    crate::leanh::lean_inc(v_proofInstInfo_2942_);
                    crate::leanh::lean_inc(v_maxFVar_2941_);
                    crate::leanh::lean_dec(v___x_2940_);
                    v___x_2952_ = crate::leanh::lean_box(0);
                    v_isShared_2953_ = v_isSharedCheck_2959_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2952_, 0, v_snd_2939_);
                    v___x_2955_ = v___x_2952_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2958_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_snd_2939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_maxFVar_2941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 2, v_proofInstInfo_2942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 3, v_inferType_2943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 4, v_getLevel_2944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 5, v_congrInfo_2945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 6, v_defEqI_2946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 7, v_extensions_2947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 8, v_issues_2948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 9, v_canon_2949_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2958_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_2950_,
                    );
                    v___x_2955_ = v_reuseFailAlloc_2958_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2956_ = lean_st_ref_set(v_a_2908_, v___x_2955_);
                v___x_2957_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2957_, 0, v_fst_2938_);
                return v___x_2957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevRangeS___boxed(
    mut v_e_2991_: *mut crate::leanh::LeanObject,
    mut v_beginIdx_2992_: *mut crate::leanh::LeanObject,
    mut v_endIdx_2993_: *mut crate::leanh::LeanObject,
    mut v_subst_2994_: *mut crate::leanh::LeanObject,
    mut v_a_2995_: *mut crate::leanh::LeanObject,
    mut v_a_2996_: *mut crate::leanh::LeanObject,
    mut v_a_2997_: *mut crate::leanh::LeanObject,
    mut v_a_2998_: *mut crate::leanh::LeanObject,
    mut v_a_2999_: *mut crate::leanh::LeanObject,
    mut v_a_3000_: *mut crate::leanh::LeanObject,
    mut v_a_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3002_ = l_Lean_Meta_Sym_instantiateRevRangeS(
        v_e_2991_,
        v_beginIdx_2992_,
        v_endIdx_2993_,
        v_subst_2994_,
        v_a_2995_,
        v_a_2996_,
        v_a_2997_,
        v_a_2998_,
        v_a_2999_,
        v_a_3000_,
    );
    crate::leanh::lean_dec(v_a_3000_);
    crate::leanh::lean_dec_ref(v_a_2999_);
    crate::leanh::lean_dec(v_a_2998_);
    crate::leanh::lean_dec_ref(v_a_2997_);
    crate::leanh::lean_dec(v_a_2996_);
    crate::leanh::lean_dec_ref(v_a_2995_);
    crate::leanh::lean_dec_ref(v_subst_2994_);
    crate::leanh::lean_dec(v_endIdx_2993_);
    crate::leanh::lean_dec(v_beginIdx_2992_);
    return v_res_3002_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(
    mut v_00_u03b2_3003_: *mut crate::leanh::LeanObject,
    mut v_m_3004_: *mut crate::leanh::LeanObject,
    mut v_a_3005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_3004_, v_a_3005_);
    return v___x_3006_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_3007_: *mut crate::leanh::LeanObject,
    mut v_m_3008_: *mut crate::leanh::LeanObject,
    mut v_a_3009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3010_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(v_00_u03b2_3007_, v_m_3008_, v_a_3009_);
    crate::leanh::lean_dec_ref(v_a_3009_);
    crate::leanh::lean_dec_ref(v_m_3008_);
    return v_res_3010_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(
    mut v_00_u03b2_3011_: *mut crate::leanh::LeanObject,
    mut v_a_3012_: *mut crate::leanh::LeanObject,
    mut v_x_3013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3014_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_3012_, v_x_3013_);
    return v___x_3014_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___boxed(
    mut v_00_u03b2_3015_: *mut crate::leanh::LeanObject,
    mut v_a_3016_: *mut crate::leanh::LeanObject,
    mut v_x_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3018_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_3015_, v_a_3016_, v_x_3017_);
    crate::leanh::lean_dec(v_x_3017_);
    crate::leanh::lean_dec_ref(v_a_3016_);
    return v_res_3018_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevS(
    mut v_e_3019_: *mut crate::leanh::LeanObject,
    mut v_subst_3020_: *mut crate::leanh::LeanObject,
    mut v_a_3021_: *mut crate::leanh::LeanObject,
    mut v_a_3022_: *mut crate::leanh::LeanObject,
    mut v_a_3023_: *mut crate::leanh::LeanObject,
    mut v_a_3024_: *mut crate::leanh::LeanObject,
    mut v_a_3025_: *mut crate::leanh::LeanObject,
    mut v_a_3026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3028_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3029_ = lean_array_get_size(v_subst_3020_);
    v___x_3030_ = l_Lean_Meta_Sym_instantiateRevRangeS(
        v_e_3019_,
        v___x_3028_,
        v___x_3029_,
        v_subst_3020_,
        v_a_3021_,
        v_a_3022_,
        v_a_3023_,
        v_a_3024_,
        v_a_3025_,
        v_a_3026_,
    );
    return v___x_3030_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevS___boxed(
    mut v_e_3031_: *mut crate::leanh::LeanObject,
    mut v_subst_3032_: *mut crate::leanh::LeanObject,
    mut v_a_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
    mut v_a_3035_: *mut crate::leanh::LeanObject,
    mut v_a_3036_: *mut crate::leanh::LeanObject,
    mut v_a_3037_: *mut crate::leanh::LeanObject,
    mut v_a_3038_: *mut crate::leanh::LeanObject,
    mut v_a_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3040_ = l_Lean_Meta_Sym_instantiateRevS(
        v_e_3031_,
        v_subst_3032_,
        v_a_3033_,
        v_a_3034_,
        v_a_3035_,
        v_a_3036_,
        v_a_3037_,
        v_a_3038_,
    );
    crate::leanh::lean_dec(v_a_3038_);
    crate::leanh::lean_dec_ref(v_a_3037_);
    crate::leanh::lean_dec(v_a_3036_);
    crate::leanh::lean_dec_ref(v_a_3035_);
    crate::leanh::lean_dec(v_a_3034_);
    crate::leanh::lean_dec_ref(v_a_3033_);
    crate::leanh::lean_dec_ref(v_subst_3032_);
    return v_res_3040_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(
    mut v_msg_3041_: *mut crate::leanh::LeanObject,
    mut v___y_3042_: u8,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111__overap_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3044_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0;
    v___f_3045_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1;
    v___f_3046_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2;
    v___f_3047_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3;
    v___f_3048_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4;
    v___f_3049_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5;
    v___f_3050_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6;
    v___x_3051_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3051_, 0, v___f_3044_);
    crate::leanh::lean_ctor_set(v___x_3051_, 1, v___f_3045_);
    v___x_3052_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3052_, 0, v___x_3051_);
    crate::leanh::lean_ctor_set(v___x_3052_, 1, v___f_3046_);
    crate::leanh::lean_ctor_set(v___x_3052_, 2, v___f_3047_);
    crate::leanh::lean_ctor_set(v___x_3052_, 3, v___f_3048_);
    crate::leanh::lean_ctor_set(v___x_3052_, 4, v___f_3049_);
    v___x_3053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3053_, 0, v___x_3052_);
    crate::leanh::lean_ctor_set(v___x_3053_, 1, v___f_3050_);
    crate::leanh::lean_inc_ref_n(v___x_3053_, 6);
    v___f_3054_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3054_, 0, v___x_3053_);
    v___f_3055_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3055_, 0, v___x_3053_);
    v___f_3056_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3056_, 0, v___x_3053_);
    v___f_3057_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3057_, 0, v___x_3053_);
    v___x_3058_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_3058_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3058_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3058_, 2, v___x_3053_);
    v___x_3059_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3059_, 0, v___x_3058_);
    crate::leanh::lean_ctor_set(v___x_3059_, 1, v___f_3054_);
    v___x_3060_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_3060_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3060_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3060_, 2, v___x_3053_);
    v___x_3061_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3061_, 0, v___x_3059_);
    crate::leanh::lean_ctor_set(v___x_3061_, 1, v___x_3060_);
    crate::leanh::lean_ctor_set(v___x_3061_, 2, v___f_3055_);
    crate::leanh::lean_ctor_set(v___x_3061_, 3, v___f_3056_);
    crate::leanh::lean_ctor_set(v___x_3061_, 4, v___f_3057_);
    v___x_3062_ = crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_3062_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3062_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_3062_, 2, v___x_3053_);
    v___x_3063_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3063_, 0, v___x_3061_);
    crate::leanh::lean_ctor_set(v___x_3063_, 1, v___x_3062_);
    v___x_3064_ = l_Lean_instInhabitedExpr;
    v___x_3065_ = l_instInhabitedOfMonad___redArg(v___x_3063_, v___x_3064_);
    v___f_3066_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3066_, 0, v___x_3065_);
    v___x_3111__overap_3067_ = lean_panic_fn_borrowed(v___f_3066_, v_msg_3041_);
    crate::leanh::lean_dec_ref(v___f_3066_);
    v___x_3068_ = crate::leanh::lean_box((v___y_3042_) as usize);
    v___x_3069_ = crate::leanh::lean_apply_2(v___x_3111__overap_3067_, v___x_3068_, v___y_3043_);
    return v___x_3069_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(
    mut v_msg_3070_: *mut crate::leanh::LeanObject,
    mut v___y_3071_: *mut crate::leanh::LeanObject,
    mut v___y_3072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3548__boxed_3073_: u8 = 0;
    let mut v_res_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3548__boxed_3073_ = (crate::leanh::lean_unbox(v___y_3071_) as u8);
    v_res_3074_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_3070_, v___y_3548__boxed_3073_, v___y_3072_);
    return v_res_3074_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(
    mut v_n_3075_: *mut crate::leanh::LeanObject,
    mut v_beginIdx_3076_: *mut crate::leanh::LeanObject,
    mut v_subst_3077_: *mut crate::leanh::LeanObject,
    mut v_e_3078_: *mut crate::leanh::LeanObject,
    mut v_offset_3079_: *mut crate::leanh::LeanObject,
    mut v_a_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: u8,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3095_: u8 = 0;
    let mut v_fst_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3100_: u8 = 0;
    let mut v___y_3102_: u8 = 0;
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: u8 = 0;
    let mut v___x_3111_: u8 = 0;
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_binderName_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3117_: u8 = 0;
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v_fst_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3135_: u8 = 0;
    let mut v___y_3137_: u8 = 0;
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3146_: u8 = 0;
    let mut v_isSharedCheck_3147_: u8 = 0;
    let mut v_isSharedCheck_3148_: u8 = 0;
    let mut v_binderName_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3152_: u8 = 0;
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3165_: u8 = 0;
    let mut v_fst_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3170_: u8 = 0;
    let mut v___y_3172_: u8 = 0;
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: u8 = 0;
    let mut v___x_3181_: u8 = 0;
    let mut v_isSharedCheck_3182_: u8 = 0;
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_declName_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_3188_: u8 = 0;
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3206_: u8 = 0;
    let mut v_fst_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3211_: u8 = 0;
    let mut v___y_3213_: u8 = 0;
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: u8 = 0;
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut v_isSharedCheck_3226_: u8 = 0;
    let mut v_data_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3234_: u8 = 0;
    let mut v_fst_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3239_: u8 = 0;
    let mut v___x_3240_: u8 = 0;
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut v_isSharedCheck_3249_: u8 = 0;
    let mut v_typeName_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v_fst_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3263_: u8 = 0;
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_3078_) {
                5 => {
                    v_fn_3083_ = crate::leanh::lean_ctor_get(v_e_3078_, 0);
                    v_arg_3084_ = crate::leanh::lean_ctor_get(v_e_3078_, 1);
                    crate::leanh::lean_inc(v_offset_3079_);
                    crate::leanh::lean_inc_ref(v_fn_3083_);
                    v___x_3085_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_fn_3083_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3086_ = crate::leanh::lean_ctor_get(v___x_3085_, 0);
                    crate::leanh::lean_inc(v_fst_3086_);
                    v_snd_3087_ = crate::leanh::lean_ctor_get(v___x_3085_, 1);
                    crate::leanh::lean_inc(v_snd_3087_);
                    crate::leanh::lean_dec_ref(v___x_3085_);
                    v_fst_3088_ = crate::leanh::lean_ctor_get(v_fst_3086_, 0);
                    crate::leanh::lean_inc(v_fst_3088_);
                    v_snd_3089_ = crate::leanh::lean_ctor_get(v_fst_3086_, 1);
                    crate::leanh::lean_inc(v_snd_3089_);
                    crate::leanh::lean_dec(v_fst_3086_);
                    crate::leanh::lean_inc_ref(v_arg_3084_);
                    v___x_3090_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_arg_3084_, v_offset_3079_, v_snd_3089_, v_a_3081_, v_snd_3087_);
                    v_fst_3091_ = crate::leanh::lean_ctor_get(v___x_3090_, 0);
                    v_snd_3092_ = crate::leanh::lean_ctor_get(v___x_3090_, 1);
                    v_isSharedCheck_3113_ = (!crate::leanh::lean_is_exclusive(v___x_3090_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v___x_3094_ = v___x_3090_;
                        v_isShared_3095_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3092_);
                        crate::leanh::lean_inc(v_fst_3091_);
                        crate::leanh::lean_dec(v___x_3090_);
                        v___x_3094_ = crate::leanh::lean_box(0);
                        v_isShared_3095_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_3114_ = crate::leanh::lean_ctor_get(v_e_3078_, 0);
                    v_binderType_3115_ = crate::leanh::lean_ctor_get(v_e_3078_, 1);
                    v_body_3116_ = crate::leanh::lean_ctor_get(v_e_3078_, 2);
                    v_binderInfo_3117_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_3078_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc(v_offset_3079_);
                    crate::leanh::lean_inc_ref(v_binderType_3115_);
                    v___x_3118_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_binderType_3115_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3119_ = crate::leanh::lean_ctor_get(v___x_3118_, 0);
                    crate::leanh::lean_inc(v_fst_3119_);
                    v_snd_3120_ = crate::leanh::lean_ctor_get(v___x_3118_, 1);
                    crate::leanh::lean_inc(v_snd_3120_);
                    crate::leanh::lean_dec_ref(v___x_3118_);
                    v_fst_3121_ = crate::leanh::lean_ctor_get(v_fst_3119_, 0);
                    crate::leanh::lean_inc(v_fst_3121_);
                    v_snd_3122_ = crate::leanh::lean_ctor_get(v_fst_3119_, 1);
                    crate::leanh::lean_inc(v_snd_3122_);
                    crate::leanh::lean_dec(v_fst_3119_);
                    v___x_3123_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3124_ = lean_nat_add(v_offset_3079_, v___x_3123_);
                    crate::leanh::lean_dec(v_offset_3079_);
                    crate::leanh::lean_inc_ref(v_body_3116_);
                    v___x_3125_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_body_3116_, v___x_3124_, v_snd_3122_, v_a_3081_, v_snd_3120_);
                    v_fst_3126_ = crate::leanh::lean_ctor_get(v___x_3125_, 0);
                    v_snd_3127_ = crate::leanh::lean_ctor_get(v___x_3125_, 1);
                    v_isSharedCheck_3148_ = (!crate::leanh::lean_is_exclusive(v___x_3125_)) as u8;
                    if v_isSharedCheck_3148_ == 0 {
                        v___x_3129_ = v___x_3125_;
                        v_isShared_3130_ = v_isSharedCheck_3148_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3127_);
                        crate::leanh::lean_inc(v_fst_3126_);
                        crate::leanh::lean_dec(v___x_3125_);
                        v___x_3129_ = crate::leanh::lean_box(0);
                        v_isShared_3130_ = v_isSharedCheck_3148_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_3149_ = crate::leanh::lean_ctor_get(v_e_3078_, 0);
                    v_binderType_3150_ = crate::leanh::lean_ctor_get(v_e_3078_, 1);
                    v_body_3151_ = crate::leanh::lean_ctor_get(v_e_3078_, 2);
                    v_binderInfo_3152_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_3078_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc(v_offset_3079_);
                    crate::leanh::lean_inc_ref(v_binderType_3150_);
                    v___x_3153_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_binderType_3150_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3154_ = crate::leanh::lean_ctor_get(v___x_3153_, 0);
                    crate::leanh::lean_inc(v_fst_3154_);
                    v_snd_3155_ = crate::leanh::lean_ctor_get(v___x_3153_, 1);
                    crate::leanh::lean_inc(v_snd_3155_);
                    crate::leanh::lean_dec_ref(v___x_3153_);
                    v_fst_3156_ = crate::leanh::lean_ctor_get(v_fst_3154_, 0);
                    crate::leanh::lean_inc(v_fst_3156_);
                    v_snd_3157_ = crate::leanh::lean_ctor_get(v_fst_3154_, 1);
                    crate::leanh::lean_inc(v_snd_3157_);
                    crate::leanh::lean_dec(v_fst_3154_);
                    v___x_3158_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3159_ = lean_nat_add(v_offset_3079_, v___x_3158_);
                    crate::leanh::lean_dec(v_offset_3079_);
                    crate::leanh::lean_inc_ref(v_body_3151_);
                    v___x_3160_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_body_3151_, v___x_3159_, v_snd_3157_, v_a_3081_, v_snd_3155_);
                    v_fst_3161_ = crate::leanh::lean_ctor_get(v___x_3160_, 0);
                    v_snd_3162_ = crate::leanh::lean_ctor_get(v___x_3160_, 1);
                    v_isSharedCheck_3183_ = (!crate::leanh::lean_is_exclusive(v___x_3160_)) as u8;
                    if v_isSharedCheck_3183_ == 0 {
                        v___x_3164_ = v___x_3160_;
                        v_isShared_3165_ = v_isSharedCheck_3183_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3162_);
                        crate::leanh::lean_inc(v_fst_3161_);
                        crate::leanh::lean_dec(v___x_3160_);
                        v___x_3164_ = crate::leanh::lean_box(0);
                        v_isShared_3165_ = v_isSharedCheck_3183_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_3184_ = crate::leanh::lean_ctor_get(v_e_3078_, 0);
                    v_type_3185_ = crate::leanh::lean_ctor_get(v_e_3078_, 1);
                    v_value_3186_ = crate::leanh::lean_ctor_get(v_e_3078_, 2);
                    v_body_3187_ = crate::leanh::lean_ctor_get(v_e_3078_, 3);
                    v_nondep_3188_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_3078_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_n(v_offset_3079_, 2);
                    crate::leanh::lean_inc_ref(v_type_3185_);
                    v___x_3189_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_type_3185_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3190_ = crate::leanh::lean_ctor_get(v___x_3189_, 0);
                    crate::leanh::lean_inc(v_fst_3190_);
                    v_snd_3191_ = crate::leanh::lean_ctor_get(v___x_3189_, 1);
                    crate::leanh::lean_inc(v_snd_3191_);
                    crate::leanh::lean_dec_ref(v___x_3189_);
                    v_fst_3192_ = crate::leanh::lean_ctor_get(v_fst_3190_, 0);
                    crate::leanh::lean_inc(v_fst_3192_);
                    v_snd_3193_ = crate::leanh::lean_ctor_get(v_fst_3190_, 1);
                    crate::leanh::lean_inc(v_snd_3193_);
                    crate::leanh::lean_dec(v_fst_3190_);
                    crate::leanh::lean_inc_ref(v_value_3186_);
                    v___x_3194_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_value_3186_, v_offset_3079_, v_snd_3193_, v_a_3081_, v_snd_3191_);
                    v_fst_3195_ = crate::leanh::lean_ctor_get(v___x_3194_, 0);
                    crate::leanh::lean_inc(v_fst_3195_);
                    v_snd_3196_ = crate::leanh::lean_ctor_get(v___x_3194_, 1);
                    crate::leanh::lean_inc(v_snd_3196_);
                    crate::leanh::lean_dec_ref(v___x_3194_);
                    v_fst_3197_ = crate::leanh::lean_ctor_get(v_fst_3195_, 0);
                    crate::leanh::lean_inc(v_fst_3197_);
                    v_snd_3198_ = crate::leanh::lean_ctor_get(v_fst_3195_, 1);
                    crate::leanh::lean_inc(v_snd_3198_);
                    crate::leanh::lean_dec(v_fst_3195_);
                    v___x_3199_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3200_ = lean_nat_add(v_offset_3079_, v___x_3199_);
                    crate::leanh::lean_dec(v_offset_3079_);
                    crate::leanh::lean_inc_ref(v_body_3187_);
                    v___x_3201_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_body_3187_, v___x_3200_, v_snd_3198_, v_a_3081_, v_snd_3196_);
                    v_fst_3202_ = crate::leanh::lean_ctor_get(v___x_3201_, 0);
                    v_snd_3203_ = crate::leanh::lean_ctor_get(v___x_3201_, 1);
                    v_isSharedCheck_3226_ = (!crate::leanh::lean_is_exclusive(v___x_3201_)) as u8;
                    if v_isSharedCheck_3226_ == 0 {
                        v___x_3205_ = v___x_3201_;
                        v_isShared_3206_ = v_isSharedCheck_3226_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3203_);
                        crate::leanh::lean_inc(v_fst_3202_);
                        crate::leanh::lean_dec(v___x_3201_);
                        v___x_3205_ = crate::leanh::lean_box(0);
                        v_isShared_3206_ = v_isSharedCheck_3226_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_3227_ = crate::leanh::lean_ctor_get(v_e_3078_, 0);
                    v_expr_3228_ = crate::leanh::lean_ctor_get(v_e_3078_, 1);
                    crate::leanh::lean_inc_ref(v_expr_3228_);
                    v___x_3229_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_expr_3228_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3230_ = crate::leanh::lean_ctor_get(v___x_3229_, 0);
                    v_snd_3231_ = crate::leanh::lean_ctor_get(v___x_3229_, 1);
                    v_isSharedCheck_3249_ = (!crate::leanh::lean_is_exclusive(v___x_3229_)) as u8;
                    if v_isSharedCheck_3249_ == 0 {
                        v___x_3233_ = v___x_3229_;
                        v_isShared_3234_ = v_isSharedCheck_3249_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3231_);
                        crate::leanh::lean_inc(v_fst_3230_);
                        crate::leanh::lean_dec(v___x_3229_);
                        v___x_3233_ = crate::leanh::lean_box(0);
                        v_isShared_3234_ = v_isSharedCheck_3249_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_3250_ = crate::leanh::lean_ctor_get(v_e_3078_, 0);
                    v_idx_3251_ = crate::leanh::lean_ctor_get(v_e_3078_, 1);
                    v_struct_3252_ = crate::leanh::lean_ctor_get(v_e_3078_, 2);
                    crate::leanh::lean_inc_ref(v_struct_3252_);
                    v___x_3253_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_struct_3252_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3254_ = crate::leanh::lean_ctor_get(v___x_3253_, 0);
                    v_snd_3255_ = crate::leanh::lean_ctor_get(v___x_3253_, 1);
                    v_isSharedCheck_3273_ = (!crate::leanh::lean_is_exclusive(v___x_3253_)) as u8;
                    if v_isSharedCheck_3273_ == 0 {
                        v___x_3257_ = v___x_3253_;
                        v_isShared_3258_ = v_isSharedCheck_3273_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3255_);
                        crate::leanh::lean_inc(v_fst_3254_);
                        crate::leanh::lean_dec(v___x_3253_);
                        v___x_3257_ = crate::leanh::lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3273_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_offset_3079_);
                    crate::leanh::lean_dec_ref(v_e_3078_);
                    v___x_3274_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
                    v___x_3275_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_3274_, v_a_3080_, v_a_3081_, v_a_3082_);
                    return v___x_3275_;
                }
            },
            1 => {
                v_fst_3096_ = crate::leanh::lean_ctor_get(v_fst_3091_, 0);
                v_snd_3097_ = crate::leanh::lean_ctor_get(v_fst_3091_, 1);
                v_isSharedCheck_3112_ = (!crate::leanh::lean_is_exclusive(v_fst_3091_)) as u8;
                if v_isSharedCheck_3112_ == 0 {
                    v___x_3099_ = v_fst_3091_;
                    v_isShared_3100_ = v_isSharedCheck_3112_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3097_);
                    crate::leanh::lean_inc(v_fst_3096_);
                    crate::leanh::lean_dec(v_fst_3091_);
                    v___x_3099_ = crate::leanh::lean_box(0);
                    v_isShared_3100_ = v_isSharedCheck_3112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3110_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_fn_3083_,
                        v_fst_3088_,
                    );
                if v___x_3110_ == 0 {
                    v___y_3102_ = v___x_3110_;
                    state = 3;
                    continue;
                } else {
                    v___x_3111_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_3084_,
                            v_fst_3096_,
                        );
                    v___y_3102_ = v___x_3111_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_3102_ == 0 {
                    crate::leanh::lean_del_object(v___x_3099_);
                    crate::leanh::lean_del_object(v___x_3094_);
                    crate::leanh::lean_dec_ref_known(v_e_3078_, 2);
                    v___x_3103_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_3088_, v_fst_3096_, v_snd_3097_, v_a_3081_, v_snd_3092_);
                    return v___x_3103_;
                } else {
                    crate::leanh::lean_dec(v_fst_3096_);
                    crate::leanh::lean_dec(v_fst_3088_);
                    if v_isShared_3100_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3099_, 0, v_e_3078_);
                        v___x_3105_ = v___x_3099_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3109_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_e_3078_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_snd_3097_);
                        v___x_3105_ = v_reuseFailAlloc_3109_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3095_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3094_, 0, v___x_3105_);
                    v___x_3107_ = v___x_3094_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3108_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_snd_3092_);
                    v___x_3107_ = v_reuseFailAlloc_3108_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3107_;
            }
            6 => {
                v_fst_3131_ = crate::leanh::lean_ctor_get(v_fst_3126_, 0);
                v_snd_3132_ = crate::leanh::lean_ctor_get(v_fst_3126_, 1);
                v_isSharedCheck_3147_ = (!crate::leanh::lean_is_exclusive(v_fst_3126_)) as u8;
                if v_isSharedCheck_3147_ == 0 {
                    v___x_3134_ = v_fst_3126_;
                    v_isShared_3135_ = v_isSharedCheck_3147_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3132_);
                    crate::leanh::lean_inc(v_fst_3131_);
                    crate::leanh::lean_dec(v_fst_3126_);
                    v___x_3134_ = crate::leanh::lean_box(0);
                    v_isShared_3135_ = v_isSharedCheck_3147_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3145_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_3115_,
                        v_fst_3121_,
                    );
                if v___x_3145_ == 0 {
                    v___y_3137_ = v___x_3145_;
                    state = 8;
                    continue;
                } else {
                    v___x_3146_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_3116_,
                            v_fst_3131_,
                        );
                    v___y_3137_ = v___x_3146_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_3137_ == 0 {
                    crate::leanh::lean_inc(v_binderName_3114_);
                    crate::leanh::lean_del_object(v___x_3134_);
                    crate::leanh::lean_del_object(v___x_3129_);
                    crate::leanh::lean_dec_ref_known(v_e_3078_, 3);
                    v___x_3138_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_3114_, v_binderInfo_3117_, v_fst_3121_, v_fst_3131_, v_snd_3132_, v_a_3081_, v_snd_3127_);
                    return v___x_3138_;
                } else {
                    crate::leanh::lean_dec(v_fst_3131_);
                    crate::leanh::lean_dec(v_fst_3121_);
                    if v_isShared_3135_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3134_, 0, v_e_3078_);
                        v___x_3140_ = v___x_3134_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3144_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_e_3078_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_snd_3132_);
                        v___x_3140_ = v_reuseFailAlloc_3144_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3130_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3129_, 0, v___x_3140_);
                    v___x_3142_ = v___x_3129_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3143_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_snd_3127_);
                    v___x_3142_ = v_reuseFailAlloc_3143_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3142_;
            }
            11 => {
                v_fst_3166_ = crate::leanh::lean_ctor_get(v_fst_3161_, 0);
                v_snd_3167_ = crate::leanh::lean_ctor_get(v_fst_3161_, 1);
                v_isSharedCheck_3182_ = (!crate::leanh::lean_is_exclusive(v_fst_3161_)) as u8;
                if v_isSharedCheck_3182_ == 0 {
                    v___x_3169_ = v_fst_3161_;
                    v_isShared_3170_ = v_isSharedCheck_3182_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3167_);
                    crate::leanh::lean_inc(v_fst_3166_);
                    crate::leanh::lean_dec(v_fst_3161_);
                    v___x_3169_ = crate::leanh::lean_box(0);
                    v_isShared_3170_ = v_isSharedCheck_3182_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3180_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_3150_,
                        v_fst_3156_,
                    );
                if v___x_3180_ == 0 {
                    v___y_3172_ = v___x_3180_;
                    state = 13;
                    continue;
                } else {
                    v___x_3181_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_3151_,
                            v_fst_3166_,
                        );
                    v___y_3172_ = v___x_3181_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_3172_ == 0 {
                    crate::leanh::lean_inc(v_binderName_3149_);
                    crate::leanh::lean_del_object(v___x_3169_);
                    crate::leanh::lean_del_object(v___x_3164_);
                    crate::leanh::lean_dec_ref_known(v_e_3078_, 3);
                    v___x_3173_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_3149_, v_binderInfo_3152_, v_fst_3156_, v_fst_3166_, v_snd_3167_, v_a_3081_, v_snd_3162_);
                    return v___x_3173_;
                } else {
                    crate::leanh::lean_dec(v_fst_3166_);
                    crate::leanh::lean_dec(v_fst_3156_);
                    if v_isShared_3170_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3169_, 0, v_e_3078_);
                        v___x_3175_ = v___x_3169_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_e_3078_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_snd_3167_);
                        v___x_3175_ = v_reuseFailAlloc_3179_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_3165_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3164_, 0, v___x_3175_);
                    v___x_3177_ = v___x_3164_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_snd_3162_);
                    v___x_3177_ = v_reuseFailAlloc_3178_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3177_;
            }
            16 => {
                v_fst_3207_ = crate::leanh::lean_ctor_get(v_fst_3202_, 0);
                v_snd_3208_ = crate::leanh::lean_ctor_get(v_fst_3202_, 1);
                v_isSharedCheck_3225_ = (!crate::leanh::lean_is_exclusive(v_fst_3202_)) as u8;
                if v_isSharedCheck_3225_ == 0 {
                    v___x_3210_ = v_fst_3202_;
                    v_isShared_3211_ = v_isSharedCheck_3225_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3208_);
                    crate::leanh::lean_inc(v_fst_3207_);
                    crate::leanh::lean_dec(v_fst_3202_);
                    v___x_3210_ = crate::leanh::lean_box(0);
                    v_isShared_3211_ = v_isSharedCheck_3225_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3223_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_3185_,
                        v_fst_3192_,
                    );
                if v___x_3223_ == 0 {
                    v___y_3213_ = v___x_3223_;
                    state = 18;
                    continue;
                } else {
                    v___x_3224_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_value_3186_,
                            v_fst_3197_,
                        );
                    v___y_3213_ = v___x_3224_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_3213_ == 0 {
                    crate::leanh::lean_inc(v_declName_3184_);
                    crate::leanh::lean_del_object(v___x_3210_);
                    crate::leanh::lean_del_object(v___x_3205_);
                    crate::leanh::lean_dec_ref_known(v_e_3078_, 4);
                    v___x_3214_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_3184_, v_fst_3192_, v_fst_3197_, v_fst_3207_, v_nondep_3188_, v_snd_3208_, v_a_3081_, v_snd_3203_);
                    return v___x_3214_;
                } else {
                    v___x_3215_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_3187_,
                            v_fst_3207_,
                        );
                    if v___x_3215_ == 0 {
                        crate::leanh::lean_inc(v_declName_3184_);
                        crate::leanh::lean_del_object(v___x_3210_);
                        crate::leanh::lean_del_object(v___x_3205_);
                        crate::leanh::lean_dec_ref_known(v_e_3078_, 4);
                        v___x_3216_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_3184_, v_fst_3192_, v_fst_3197_, v_fst_3207_, v_nondep_3188_, v_snd_3208_, v_a_3081_, v_snd_3203_);
                        return v___x_3216_;
                    } else {
                        crate::leanh::lean_dec(v_fst_3207_);
                        crate::leanh::lean_dec(v_fst_3197_);
                        crate::leanh::lean_dec(v_fst_3192_);
                        if v_isShared_3211_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3210_, 0, v_e_3078_);
                            v___x_3218_ = v___x_3210_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_3222_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_e_3078_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_snd_3208_);
                            v___x_3218_ = v_reuseFailAlloc_3222_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_3206_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3205_, 0, v___x_3218_);
                    v___x_3220_ = v___x_3205_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_snd_3203_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3220_;
            }
            21 => {
                v_fst_3235_ = crate::leanh::lean_ctor_get(v_fst_3230_, 0);
                v_snd_3236_ = crate::leanh::lean_ctor_get(v_fst_3230_, 1);
                v_isSharedCheck_3248_ = (!crate::leanh::lean_is_exclusive(v_fst_3230_)) as u8;
                if v_isSharedCheck_3248_ == 0 {
                    v___x_3238_ = v_fst_3230_;
                    v_isShared_3239_ = v_isSharedCheck_3248_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3236_);
                    crate::leanh::lean_inc(v_fst_3235_);
                    crate::leanh::lean_dec(v_fst_3230_);
                    v___x_3238_ = crate::leanh::lean_box(0);
                    v_isShared_3239_ = v_isSharedCheck_3248_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_3240_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_expr_3228_,
                        v_fst_3235_,
                    );
                if v___x_3240_ == 0 {
                    crate::leanh::lean_inc(v_data_3227_);
                    crate::leanh::lean_del_object(v___x_3238_);
                    crate::leanh::lean_del_object(v___x_3233_);
                    crate::leanh::lean_dec_ref_known(v_e_3078_, 2);
                    v___x_3241_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_3227_, v_fst_3235_, v_snd_3236_, v_a_3081_, v_snd_3231_);
                    return v___x_3241_;
                } else {
                    crate::leanh::lean_dec(v_fst_3235_);
                    if v_isShared_3239_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3238_, 0, v_e_3078_);
                        v___x_3243_ = v___x_3238_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_3247_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_e_3078_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_snd_3236_);
                        v___x_3243_ = v_reuseFailAlloc_3247_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_3234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3233_, 0, v___x_3243_);
                    v___x_3245_ = v___x_3233_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3246_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_snd_3231_);
                    v___x_3245_ = v_reuseFailAlloc_3246_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3245_;
            }
            25 => {
                v_fst_3259_ = crate::leanh::lean_ctor_get(v_fst_3254_, 0);
                v_snd_3260_ = crate::leanh::lean_ctor_get(v_fst_3254_, 1);
                v_isSharedCheck_3272_ = (!crate::leanh::lean_is_exclusive(v_fst_3254_)) as u8;
                if v_isSharedCheck_3272_ == 0 {
                    v___x_3262_ = v_fst_3254_;
                    v_isShared_3263_ = v_isSharedCheck_3272_;
                    state = 26;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3260_);
                    crate::leanh::lean_inc(v_fst_3259_);
                    crate::leanh::lean_dec(v_fst_3254_);
                    v___x_3262_ = crate::leanh::lean_box(0);
                    v_isShared_3263_ = v_isSharedCheck_3272_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_3264_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_struct_3252_,
                        v_fst_3259_,
                    );
                if v___x_3264_ == 0 {
                    crate::leanh::lean_inc(v_idx_3251_);
                    crate::leanh::lean_inc(v_typeName_3250_);
                    crate::leanh::lean_del_object(v___x_3262_);
                    crate::leanh::lean_del_object(v___x_3257_);
                    crate::leanh::lean_dec_ref_known(v_e_3078_, 3);
                    v___x_3265_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_3250_, v_idx_3251_, v_fst_3259_, v_snd_3260_, v_a_3081_, v_snd_3255_);
                    return v___x_3265_;
                } else {
                    crate::leanh::lean_dec(v_fst_3259_);
                    if v_isShared_3263_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3262_, 0, v_e_3078_);
                        v___x_3267_ = v___x_3262_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_3271_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_e_3078_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_snd_3260_);
                        v___x_3267_ = v_reuseFailAlloc_3271_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_3258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3257_, 0, v___x_3267_);
                    v___x_3269_ = v___x_3257_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3270_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_snd_3255_);
                    v___x_3269_ = v_reuseFailAlloc_3270_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(
    mut v_n_3276_: *mut crate::leanh::LeanObject,
    mut v_beginIdx_3277_: *mut crate::leanh::LeanObject,
    mut v_subst_3278_: *mut crate::leanh::LeanObject,
    mut v_e_3279_: *mut crate::leanh::LeanObject,
    mut v_offset_3280_: *mut crate::leanh::LeanObject,
    mut v_a_3281_: *mut crate::leanh::LeanObject,
    mut v_a_3282_: u8,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_offset_3280_);
    crate::leanh::lean_inc_ref(v_e_3279_);
    v_key_3284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_key_3284_, 0, v_e_3279_);
    crate::leanh::lean_ctor_set(v_key_3284_, 1, v_offset_3280_);
    v___x_3285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_3281_, v_key_3284_);
    if crate::leanh::lean_obj_tag(v___x_3285_) == 1 {
        let mut v_val_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v_key_3284_, 2);
        crate::leanh::lean_dec(v_offset_3280_);
        crate::leanh::lean_dec_ref(v_e_3279_);
        v_val_3286_ = crate::leanh::lean_ctor_get(v___x_3285_, 0);
        crate::leanh::lean_inc(v_val_3286_);
        crate::leanh::lean_dec_ref_known(v___x_3285_, 1);
        v___x_3287_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3287_, 0, v_val_3286_);
        crate::leanh::lean_ctor_set(v___x_3287_, 1, v_a_3281_);
        v___x_3288_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3288_, 0, v___x_3287_);
        crate::leanh::lean_ctor_set(v___x_3288_, 1, v_a_3283_);
        return v___x_3288_;
    } else {
        crate::leanh::lean_dec(v___x_3285_);
        match crate::leanh::lean_obj_tag(v_e_3279_) {
            0 => {
                let mut v_deBruijnIndex_3289_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v___x_3290_: u8 = 0;
                v_deBruijnIndex_3289_ = crate::leanh::lean_ctor_get(v_e_3279_, 0);
                v___x_3290_ = lean_nat_dec_le(v_offset_3280_, v_deBruijnIndex_3289_);
                if v___x_3290_ == 0 {
                    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_offset_3280_);
                    v___x_3291_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_3284_,
                        v_e_3279_,
                        v_a_3281_,
                        v_a_3282_,
                        v_a_3283_,
                    );
                    return v___x_3291_;
                } else {
                    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3293_: u8 = 0;
                    crate::leanh::lean_inc(v_deBruijnIndex_3289_);
                    crate::leanh::lean_dec_ref_known(v_e_3279_, 1);
                    v___x_3292_ = lean_nat_add(v_offset_3280_, v_n_3276_);
                    v___x_3293_ = lean_nat_dec_lt(v_deBruijnIndex_3289_, v___x_3292_);
                    crate::leanh::lean_dec(v___x_3292_);
                    if v___x_3293_ == 0 {
                        let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_fst_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_snd_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec(v_offset_3280_);
                        v___x_3294_ = lean_nat_sub(v_deBruijnIndex_3289_, v_n_3276_);
                        crate::leanh::lean_dec(v_deBruijnIndex_3289_);
                        v___x_3295_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_3294_, v_a_3283_);
                        v_fst_3296_ = crate::leanh::lean_ctor_get(v___x_3295_, 0);
                        crate::leanh::lean_inc(v_fst_3296_);
                        v_snd_3297_ = crate::leanh::lean_ctor_get(v___x_3295_, 1);
                        crate::leanh::lean_inc(v_snd_3297_);
                        crate::leanh::lean_dec_ref(v___x_3295_);
                        v___x_3298_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                            v_key_3284_,
                            v_fst_3296_,
                            v_a_3281_,
                            v_a_3282_,
                            v_snd_3297_,
                        );
                        return v___x_3298_;
                    } else {
                        let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_v_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_fst_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_snd_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_3299_ = lean_nat_add(v_beginIdx_3277_, v_deBruijnIndex_3289_);
                        crate::leanh::lean_dec(v_deBruijnIndex_3289_);
                        v___x_3300_ = lean_nat_sub(v___x_3299_, v_offset_3280_);
                        crate::leanh::lean_dec(v___x_3299_);
                        v_v_3301_ = lean_array_fget_borrowed(v_subst_3278_, v___x_3300_);
                        crate::leanh::lean_dec(v___x_3300_);
                        v___x_3302_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc(v_v_3301_);
                        v___x_3303_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                            v_v_3301_,
                            v___x_3302_,
                            v_offset_3280_,
                            v_a_3282_,
                            v_a_3283_,
                        );
                        crate::leanh::lean_dec(v_offset_3280_);
                        v_fst_3304_ = crate::leanh::lean_ctor_get(v___x_3303_, 0);
                        crate::leanh::lean_inc(v_fst_3304_);
                        v_snd_3305_ = crate::leanh::lean_ctor_get(v___x_3303_, 1);
                        crate::leanh::lean_inc(v_snd_3305_);
                        crate::leanh::lean_dec_ref(v___x_3303_);
                        v___x_3306_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                            v_key_3284_,
                            v_fst_3304_,
                            v_a_3281_,
                            v_a_3282_,
                            v_snd_3305_,
                        );
                        return v___x_3306_;
                    }
                }
            }
            9 => {
                let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_offset_3280_);
                v___x_3307_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                    v_key_3284_,
                    v_e_3279_,
                    v_a_3281_,
                    v_a_3282_,
                    v_a_3283_,
                );
                return v___x_3307_;
            }
            2 => {
                let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_offset_3280_);
                v___x_3308_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                    v_key_3284_,
                    v_e_3279_,
                    v_a_3281_,
                    v_a_3282_,
                    v_a_3283_,
                );
                return v___x_3308_;
            }
            1 => {
                let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_offset_3280_);
                v___x_3309_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                    v_key_3284_,
                    v_e_3279_,
                    v_a_3281_,
                    v_a_3282_,
                    v_a_3283_,
                );
                return v___x_3309_;
            }
            4 => {
                let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_offset_3280_);
                v___x_3310_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                    v_key_3284_,
                    v_e_3279_,
                    v_a_3281_,
                    v_a_3282_,
                    v_a_3283_,
                );
                return v___x_3310_;
            }
            3 => {
                let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_offset_3280_);
                v___x_3311_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                    v_key_3284_,
                    v_e_3279_,
                    v_a_3281_,
                    v_a_3282_,
                    v_a_3283_,
                );
                return v___x_3311_;
            }
            _ => {
                let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3313_: u8 = 0;
                v___x_3312_ = l_Lean_Expr_looseBVarRange(v_e_3279_);
                v___x_3313_ = lean_nat_dec_le(v___x_3312_, v_offset_3280_);
                crate::leanh::lean_dec(v___x_3312_);
                if v___x_3313_ == 0 {
                    match crate::leanh::lean_obj_tag(v_e_3279_) {
                        9 => {
                            let mut v___x_3314_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_3280_);
                            v___x_3314_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_3284_,
                                v_e_3279_,
                                v_a_3281_,
                                v_a_3282_,
                                v_a_3283_,
                            );
                            return v___x_3314_;
                        }
                        2 => {
                            let mut v___x_3315_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_3280_);
                            v___x_3315_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_3284_,
                                v_e_3279_,
                                v_a_3281_,
                                v_a_3282_,
                                v_a_3283_,
                            );
                            return v___x_3315_;
                        }
                        0 => {
                            let mut v___x_3316_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_3280_);
                            v___x_3316_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_3284_,
                                v_e_3279_,
                                v_a_3281_,
                                v_a_3282_,
                                v_a_3283_,
                            );
                            return v___x_3316_;
                        }
                        1 => {
                            let mut v___x_3317_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_3280_);
                            v___x_3317_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_3284_,
                                v_e_3279_,
                                v_a_3281_,
                                v_a_3282_,
                                v_a_3283_,
                            );
                            return v___x_3317_;
                        }
                        4 => {
                            let mut v___x_3318_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_3280_);
                            v___x_3318_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_3284_,
                                v_e_3279_,
                                v_a_3281_,
                                v_a_3282_,
                                v_a_3283_,
                            );
                            return v___x_3318_;
                        }
                        3 => {
                            let mut v___x_3319_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v_offset_3280_);
                            v___x_3319_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_3284_,
                                v_e_3279_,
                                v_a_3281_,
                                v_a_3282_,
                                v_a_3283_,
                            );
                            return v___x_3319_;
                        }
                        _ => {
                            let mut v___x_3320_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_fst_3321_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_snd_3322_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_fst_3323_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_snd_3324_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3325_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_3320_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_3276_, v_beginIdx_3277_, v_subst_3278_, v_e_3279_, v_offset_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
                            v_fst_3321_ = crate::leanh::lean_ctor_get(v___x_3320_, 0);
                            crate::leanh::lean_inc(v_fst_3321_);
                            v_snd_3322_ = crate::leanh::lean_ctor_get(v___x_3320_, 1);
                            crate::leanh::lean_inc(v_snd_3322_);
                            crate::leanh::lean_dec_ref(v___x_3320_);
                            v_fst_3323_ = crate::leanh::lean_ctor_get(v_fst_3321_, 0);
                            crate::leanh::lean_inc(v_fst_3323_);
                            v_snd_3324_ = crate::leanh::lean_ctor_get(v_fst_3321_, 1);
                            crate::leanh::lean_inc(v_snd_3324_);
                            crate::leanh::lean_dec(v_fst_3321_);
                            v___x_3325_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                                v_key_3284_,
                                v_fst_3323_,
                                v_snd_3324_,
                                v_a_3282_,
                                v_snd_3322_,
                            );
                            return v___x_3325_;
                        }
                    }
                } else {
                    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_offset_3280_);
                    v___x_3326_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_3284_,
                        v_e_3279_,
                        v_a_3281_,
                        v_a_3282_,
                        v_a_3283_,
                    );
                    return v___x_3326_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0___boxed(
    mut v_n_3327_: *mut crate::leanh::LeanObject,
    mut v_beginIdx_3328_: *mut crate::leanh::LeanObject,
    mut v_subst_3329_: *mut crate::leanh::LeanObject,
    mut v_e_3330_: *mut crate::leanh::LeanObject,
    mut v_offset_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3335_: u8 = 0;
    let mut v_res_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3335_ = (crate::leanh::lean_unbox(v_a_3333_) as u8);
    v_res_3336_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3327_, v_beginIdx_3328_, v_subst_3329_, v_e_3330_, v_offset_3331_, v_a_3332_, v_a_boxed_3335_, v_a_3334_);
    crate::leanh::lean_dec_ref(v_subst_3329_);
    crate::leanh::lean_dec(v_beginIdx_3328_);
    crate::leanh::lean_dec(v_n_3327_);
    return v_res_3336_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(
    mut v_n_3337_: *mut crate::leanh::LeanObject,
    mut v_beginIdx_3338_: *mut crate::leanh::LeanObject,
    mut v_subst_3339_: *mut crate::leanh::LeanObject,
    mut v_e_3340_: *mut crate::leanh::LeanObject,
    mut v_offset_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3345_: u8 = 0;
    let mut v_res_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3345_ = (crate::leanh::lean_unbox(v_a_3343_) as u8);
    v_res_3346_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_3337_, v_beginIdx_3338_, v_subst_3339_, v_e_3340_, v_offset_3341_, v_a_3342_, v_a_boxed_3345_, v_a_3344_);
    crate::leanh::lean_dec_ref(v_subst_3339_);
    crate::leanh::lean_dec(v_beginIdx_3338_);
    crate::leanh::lean_dec(v_n_3337_);
    return v_res_3346_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3348_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_3349_ = crate::leanh::lean_unsigned_to_nat(34);
    v___x_3350_ = crate::leanh::lean_unsigned_to_nat(57);
    v___x_3351_ =
        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0;
    v___x_3352_ = l_Lean_Meta_Sym_instantiateRevRangeS___closed__3;
    v___x_3353_ = l_mkPanicMessageWithDecl(
        v___x_3352_,
        v___x_3351_,
        v___x_3350_,
        v___x_3349_,
        v___x_3348_,
    );
    return v___x_3353_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3354_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_3355_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3356_ = crate::leanh::lean_unsigned_to_nat(56);
    v___x_3357_ =
        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0;
    v___x_3358_ = l_Lean_Meta_Sym_instantiateRevRangeS___closed__3;
    v___x_3359_ = l_mkPanicMessageWithDecl(
        v___x_3358_,
        v___x_3357_,
        v___x_3356_,
        v___x_3355_,
        v___x_3354_,
    );
    return v___x_3359_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(
    mut v_e_3360_: *mut crate::leanh::LeanObject,
    mut v_beginIdx_3361_: *mut crate::leanh::LeanObject,
    mut v_endIdx_3362_: *mut crate::leanh::LeanObject,
    mut v_subst_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: u8,
    mut v_a_3365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3366_: u8 = 0;
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: u8 = 0;
    let mut v_n_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: u8 = 0;
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: u8 = 0;
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3400_: u8 = 0;
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3404_: u8 = 0;
    let mut v_unused_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3366_ = lean_nat_dec_lt(v_endIdx_3362_, v_beginIdx_3361_);
                if v___x_3366_ == 0 {
                    v___x_3367_ = lean_array_get_size(v_subst_3363_);
                    v___x_3368_ = lean_nat_dec_lt(v___x_3367_, v_endIdx_3362_);
                    if v___x_3368_ == 0 {
                        v_n_3369_ = lean_nat_sub(v_endIdx_3362_, v_beginIdx_3361_);
                        v___x_3370_ = crate::leanh::lean_unsigned_to_nat(0);
                        match crate::leanh::lean_obj_tag(v_e_3360_) {
                            0 => {
                                v_deBruijnIndex_3371_ = crate::leanh::lean_ctor_get(v_e_3360_, 0);
                                v___x_3372_ = lean_nat_dec_le(v___x_3370_, v_deBruijnIndex_3371_);
                                if v___x_3372_ == 0 {
                                    crate::leanh::lean_dec(v_n_3369_);
                                    v___x_3373_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3373_, 0, v_e_3360_);
                                    crate::leanh::lean_ctor_set(v___x_3373_, 1, v_a_3365_);
                                    return v___x_3373_;
                                } else {
                                    crate::leanh::lean_inc(v_deBruijnIndex_3371_);
                                    crate::leanh::lean_dec_ref_known(v_e_3360_, 1);
                                    v___x_3374_ = lean_nat_dec_lt(v_deBruijnIndex_3371_, v_n_3369_);
                                    if v___x_3374_ == 0 {
                                        v___x_3375_ =
                                            lean_nat_sub(v_deBruijnIndex_3371_, v_n_3369_);
                                        crate::leanh::lean_dec(v_n_3369_);
                                        crate::leanh::lean_dec(v_deBruijnIndex_3371_);
                                        v___x_3376_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_3375_, v_a_3365_);
                                        return v___x_3376_;
                                    } else {
                                        crate::leanh::lean_dec(v_n_3369_);
                                        v___x_3377_ =
                                            lean_nat_add(v_beginIdx_3361_, v_deBruijnIndex_3371_);
                                        crate::leanh::lean_dec(v_deBruijnIndex_3371_);
                                        v_v_3378_ =
                                            lean_array_fget_borrowed(v_subst_3363_, v___x_3377_);
                                        crate::leanh::lean_dec(v___x_3377_);
                                        crate::leanh::lean_inc(v_v_3378_);
                                        v___x_3379_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                                            v_v_3378_,
                                            v___x_3370_,
                                            v___x_3370_,
                                            v_a_3364_,
                                            v_a_3365_,
                                        );
                                        return v___x_3379_;
                                    }
                                }
                            }
                            9 => {
                                crate::leanh::lean_dec(v_n_3369_);
                                v___x_3380_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3380_, 0, v_e_3360_);
                                crate::leanh::lean_ctor_set(v___x_3380_, 1, v_a_3365_);
                                return v___x_3380_;
                            }
                            2 => {
                                crate::leanh::lean_dec(v_n_3369_);
                                v___x_3381_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3381_, 0, v_e_3360_);
                                crate::leanh::lean_ctor_set(v___x_3381_, 1, v_a_3365_);
                                return v___x_3381_;
                            }
                            1 => {
                                crate::leanh::lean_dec(v_n_3369_);
                                v___x_3382_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3382_, 0, v_e_3360_);
                                crate::leanh::lean_ctor_set(v___x_3382_, 1, v_a_3365_);
                                return v___x_3382_;
                            }
                            4 => {
                                crate::leanh::lean_dec(v_n_3369_);
                                v___x_3383_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3383_, 0, v_e_3360_);
                                crate::leanh::lean_ctor_set(v___x_3383_, 1, v_a_3365_);
                                return v___x_3383_;
                            }
                            3 => {
                                crate::leanh::lean_dec(v_n_3369_);
                                v___x_3384_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3384_, 0, v_e_3360_);
                                crate::leanh::lean_ctor_set(v___x_3384_, 1, v_a_3365_);
                                return v___x_3384_;
                            }
                            _ => {
                                v___x_3385_ = l_Lean_Expr_looseBVarRange(v_e_3360_);
                                v___x_3386_ = lean_nat_dec_le(v___x_3385_, v___x_3370_);
                                crate::leanh::lean_dec(v___x_3385_);
                                if v___x_3386_ == 0 {
                                    match crate::leanh::lean_obj_tag(v_e_3360_) {
                                        9 => {
                                            crate::leanh::lean_dec(v_n_3369_);
                                            v___x_3387_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_3387_, 0, v_e_3360_);
                                            crate::leanh::lean_ctor_set(v___x_3387_, 1, v_a_3365_);
                                            return v___x_3387_;
                                        }
                                        2 => {
                                            crate::leanh::lean_dec(v_n_3369_);
                                            v___x_3388_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_3388_, 0, v_e_3360_);
                                            crate::leanh::lean_ctor_set(v___x_3388_, 1, v_a_3365_);
                                            return v___x_3388_;
                                        }
                                        0 => {
                                            crate::leanh::lean_dec(v_n_3369_);
                                            v___x_3389_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_3389_, 0, v_e_3360_);
                                            crate::leanh::lean_ctor_set(v___x_3389_, 1, v_a_3365_);
                                            return v___x_3389_;
                                        }
                                        1 => {
                                            crate::leanh::lean_dec(v_n_3369_);
                                            v___x_3390_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_3390_, 0, v_e_3360_);
                                            crate::leanh::lean_ctor_set(v___x_3390_, 1, v_a_3365_);
                                            return v___x_3390_;
                                        }
                                        4 => {
                                            crate::leanh::lean_dec(v_n_3369_);
                                            v___x_3391_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_3391_, 0, v_e_3360_);
                                            crate::leanh::lean_ctor_set(v___x_3391_, 1, v_a_3365_);
                                            return v___x_3391_;
                                        }
                                        3 => {
                                            crate::leanh::lean_dec(v_n_3369_);
                                            v___x_3392_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_3392_, 0, v_e_3360_);
                                            crate::leanh::lean_ctor_set(v___x_3392_, 1, v_a_3365_);
                                            return v___x_3392_;
                                        }
                                        _ => {
                                            v___x_3393_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once), _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
                                            v___x_3394_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_3369_, v_beginIdx_3361_, v_subst_3363_, v_e_3360_, v___x_3370_, v___x_3393_, v_a_3364_, v_a_3365_);
                                            crate::leanh::lean_dec(v_n_3369_);
                                            v_fst_3395_ =
                                                crate::leanh::lean_ctor_get(v___x_3394_, 0);
                                            crate::leanh::lean_inc(v_fst_3395_);
                                            v_snd_3396_ =
                                                crate::leanh::lean_ctor_get(v___x_3394_, 1);
                                            crate::leanh::lean_inc(v_snd_3396_);
                                            crate::leanh::lean_dec_ref(v___x_3394_);
                                            v_fst_3397_ =
                                                crate::leanh::lean_ctor_get(v_fst_3395_, 0);
                                            v_isSharedCheck_3404_ =
                                                (!crate::leanh::lean_is_exclusive(v_fst_3395_))
                                                    as u8;
                                            if v_isSharedCheck_3404_ == 0 {
                                                v_unused_3405_ =
                                                    crate::leanh::lean_ctor_get(v_fst_3395_, 1);
                                                crate::leanh::lean_dec(v_unused_3405_);
                                                v___x_3399_ = v_fst_3395_;
                                                v_isShared_3400_ = v_isSharedCheck_3404_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_fst_3397_);
                                                crate::leanh::lean_dec(v_fst_3395_);
                                                v___x_3399_ = crate::leanh::lean_box(0);
                                                v_isShared_3400_ = v_isSharedCheck_3404_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_n_3369_);
                                    v___x_3406_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3406_, 0, v_e_3360_);
                                    crate::leanh::lean_ctor_set(v___x_3406_, 1, v_a_3365_);
                                    return v___x_3406_;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3360_);
                        v___x_3407_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once), _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
                        v___x_3408_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_3407_, v_a_3364_, v_a_3365_);
                        return v___x_3408_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3360_);
                    v___x_3409_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once), _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
                    v___x_3410_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_3409_, v_a_3364_, v_a_3365_);
                    return v___x_3410_;
                }
            }
            1 => {
                if v_isShared_3400_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3399_, 1, v_snd_3396_);
                    v___x_3402_ = v___x_3399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3403_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_fst_3397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3403_, 1, v_snd_3396_);
                    v___x_3402_ = v_reuseFailAlloc_3403_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___boxed(
    mut v_e_3411_: *mut crate::leanh::LeanObject,
    mut v_beginIdx_3412_: *mut crate::leanh::LeanObject,
    mut v_endIdx_3413_: *mut crate::leanh::LeanObject,
    mut v_subst_3414_: *mut crate::leanh::LeanObject,
    mut v_a_3415_: *mut crate::leanh::LeanObject,
    mut v_a_3416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3417_: u8 = 0;
    let mut v_res_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3417_ = (crate::leanh::lean_unbox(v_a_3415_) as u8);
    v_res_3418_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(
        v_e_3411_,
        v_beginIdx_3412_,
        v_endIdx_3413_,
        v_subst_3414_,
        v_a_boxed_3417_,
        v_a_3416_,
    );
    crate::leanh::lean_dec_ref(v_subst_3414_);
    crate::leanh::lean_dec(v_endIdx_3413_);
    crate::leanh::lean_dec(v_beginIdx_3412_);
    return v_res_3418_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(
    mut v_e_3419_: *mut crate::leanh::LeanObject,
    mut v_subst_3420_: *mut crate::leanh::LeanObject,
    mut v_a_3421_: u8,
    mut v_a_3422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3423_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3424_ = lean_array_get_size(v_subst_3420_);
    v___x_3425_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(
        v_e_3419_,
        v___x_3423_,
        v___x_3424_,
        v_subst_3420_,
        v_a_3421_,
        v_a_3422_,
    );
    return v___x_3425_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27___boxed(
    mut v_e_3426_: *mut crate::leanh::LeanObject,
    mut v_subst_3427_: *mut crate::leanh::LeanObject,
    mut v_a_3428_: *mut crate::leanh::LeanObject,
    mut v_a_3429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3430_: u8 = 0;
    let mut v_res_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3430_ = (crate::leanh::lean_unbox(v_a_3428_) as u8);
    v_res_3431_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(
        v_e_3426_,
        v_subst_3427_,
        v_a_boxed_3430_,
        v_a_3429_,
    );
    crate::leanh::lean_dec_ref(v_subst_3427_);
    return v_res_3431_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateS___redArg(
    mut v_e_3432_: *mut crate::leanh::LeanObject,
    mut v_subst_3433_: *mut crate::leanh::LeanObject,
    mut v_a_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3447_: u8 = 0;
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3450_: u8 = 0;
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3456_: u8 = 0;
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_3470_: u8 = 0;
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3479_: u8 = 0;
    let mut v_unused_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3436_ = lean_st_ref_take(v_a_3434_);
                v_share_3437_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                v_maxFVar_3438_ = crate::leanh::lean_ctor_get(v___x_3436_, 1);
                v_proofInstInfo_3439_ = crate::leanh::lean_ctor_get(v___x_3436_, 2);
                v_inferType_3440_ = crate::leanh::lean_ctor_get(v___x_3436_, 3);
                v_getLevel_3441_ = crate::leanh::lean_ctor_get(v___x_3436_, 4);
                v_congrInfo_3442_ = crate::leanh::lean_ctor_get(v___x_3436_, 5);
                v_defEqI_3443_ = crate::leanh::lean_ctor_get(v___x_3436_, 6);
                v_extensions_3444_ = crate::leanh::lean_ctor_get(v___x_3436_, 7);
                v_issues_3445_ = crate::leanh::lean_ctor_get(v___x_3436_, 8);
                v_canon_3446_ = crate::leanh::lean_ctor_get(v___x_3436_, 9);
                v_debug_3447_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3436_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3482_ = (!crate::leanh::lean_is_exclusive(v___x_3436_)) as u8;
                if v_isSharedCheck_3482_ == 0 {
                    v___x_3449_ = v___x_3436_;
                    v_isShared_3450_ = v_isSharedCheck_3482_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_3446_);
                    crate::leanh::lean_inc(v_issues_3445_);
                    crate::leanh::lean_inc(v_extensions_3444_);
                    crate::leanh::lean_inc(v_defEqI_3443_);
                    crate::leanh::lean_inc(v_congrInfo_3442_);
                    crate::leanh::lean_inc(v_getLevel_3441_);
                    crate::leanh::lean_inc(v_inferType_3440_);
                    crate::leanh::lean_inc(v_proofInstInfo_3439_);
                    crate::leanh::lean_inc(v_maxFVar_3438_);
                    crate::leanh::lean_inc(v_share_3437_);
                    crate::leanh::lean_dec(v___x_3436_);
                    v___x_3449_ = crate::leanh::lean_box(0);
                    v_isShared_3450_ = v_isSharedCheck_3482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3451_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once),
                    _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0,
                );
                if v_isShared_3450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3449_, 0, v___x_3451_);
                    v___x_3453_ = v___x_3449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3481_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_maxFVar_3438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 2, v_proofInstInfo_3439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 3, v_inferType_3440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 4, v_getLevel_3441_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 5, v_congrInfo_3442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 6, v_defEqI_3443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 7, v_extensions_3444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 8, v_issues_3445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 9, v_canon_3446_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3481_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_3447_,
                    );
                    v___x_3453_ = v_reuseFailAlloc_3481_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3454_ = lean_st_ref_set(v_a_3434_, v___x_3453_);
                v___x_3455_ = lean_st_ref_get(v_a_3434_);
                v_debug_3456_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3455_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_3455_);
                v___x_3457_ =
                    l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(
                        v_e_3432_,
                        v_subst_3433_,
                        v_debug_3456_,
                        v_share_3437_,
                    );
                v_fst_3458_ = crate::leanh::lean_ctor_get(v___x_3457_, 0);
                crate::leanh::lean_inc(v_fst_3458_);
                v_snd_3459_ = crate::leanh::lean_ctor_get(v___x_3457_, 1);
                crate::leanh::lean_inc(v_snd_3459_);
                crate::leanh::lean_dec_ref(v___x_3457_);
                v___x_3460_ = lean_st_ref_take(v_a_3434_);
                v_maxFVar_3461_ = crate::leanh::lean_ctor_get(v___x_3460_, 1);
                v_proofInstInfo_3462_ = crate::leanh::lean_ctor_get(v___x_3460_, 2);
                v_inferType_3463_ = crate::leanh::lean_ctor_get(v___x_3460_, 3);
                v_getLevel_3464_ = crate::leanh::lean_ctor_get(v___x_3460_, 4);
                v_congrInfo_3465_ = crate::leanh::lean_ctor_get(v___x_3460_, 5);
                v_defEqI_3466_ = crate::leanh::lean_ctor_get(v___x_3460_, 6);
                v_extensions_3467_ = crate::leanh::lean_ctor_get(v___x_3460_, 7);
                v_issues_3468_ = crate::leanh::lean_ctor_get(v___x_3460_, 8);
                v_canon_3469_ = crate::leanh::lean_ctor_get(v___x_3460_, 9);
                v_debug_3470_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_3460_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3479_ = (!crate::leanh::lean_is_exclusive(v___x_3460_)) as u8;
                if v_isSharedCheck_3479_ == 0 {
                    v_unused_3480_ = crate::leanh::lean_ctor_get(v___x_3460_, 0);
                    crate::leanh::lean_dec(v_unused_3480_);
                    v___x_3472_ = v___x_3460_;
                    v_isShared_3473_ = v_isSharedCheck_3479_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_3469_);
                    crate::leanh::lean_inc(v_issues_3468_);
                    crate::leanh::lean_inc(v_extensions_3467_);
                    crate::leanh::lean_inc(v_defEqI_3466_);
                    crate::leanh::lean_inc(v_congrInfo_3465_);
                    crate::leanh::lean_inc(v_getLevel_3464_);
                    crate::leanh::lean_inc(v_inferType_3463_);
                    crate::leanh::lean_inc(v_proofInstInfo_3462_);
                    crate::leanh::lean_inc(v_maxFVar_3461_);
                    crate::leanh::lean_dec(v___x_3460_);
                    v___x_3472_ = crate::leanh::lean_box(0);
                    v_isShared_3473_ = v_isSharedCheck_3479_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3473_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3472_, 0, v_snd_3459_);
                    v___x_3475_ = v___x_3472_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3478_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_snd_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_maxFVar_3461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_proofInstInfo_3462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 3, v_inferType_3463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 4, v_getLevel_3464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 5, v_congrInfo_3465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 6, v_defEqI_3466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 7, v_extensions_3467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 8, v_issues_3468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 9, v_canon_3469_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3478_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_3470_,
                    );
                    v___x_3475_ = v_reuseFailAlloc_3478_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3476_ = lean_st_ref_set(v_a_3434_, v___x_3475_);
                v___x_3477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3477_, 0, v_fst_3458_);
                return v___x_3477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_instantiateS___redArg___boxed(
    mut v_e_3483_: *mut crate::leanh::LeanObject,
    mut v_subst_3484_: *mut crate::leanh::LeanObject,
    mut v_a_3485_: *mut crate::leanh::LeanObject,
    mut v_a_3486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3487_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_3483_, v_subst_3484_, v_a_3485_);
    crate::leanh::lean_dec(v_a_3485_);
    crate::leanh::lean_dec_ref(v_subst_3484_);
    return v_res_3487_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateS(
    mut v_e_3488_: *mut crate::leanh::LeanObject,
    mut v_subst_3489_: *mut crate::leanh::LeanObject,
    mut v_a_3490_: *mut crate::leanh::LeanObject,
    mut v_a_3491_: *mut crate::leanh::LeanObject,
    mut v_a_3492_: *mut crate::leanh::LeanObject,
    mut v_a_3493_: *mut crate::leanh::LeanObject,
    mut v_a_3494_: *mut crate::leanh::LeanObject,
    mut v_a_3495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3497_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_3488_, v_subst_3489_, v_a_3491_);
    return v___x_3497_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateS___boxed(
    mut v_e_3498_: *mut crate::leanh::LeanObject,
    mut v_subst_3499_: *mut crate::leanh::LeanObject,
    mut v_a_3500_: *mut crate::leanh::LeanObject,
    mut v_a_3501_: *mut crate::leanh::LeanObject,
    mut v_a_3502_: *mut crate::leanh::LeanObject,
    mut v_a_3503_: *mut crate::leanh::LeanObject,
    mut v_a_3504_: *mut crate::leanh::LeanObject,
    mut v_a_3505_: *mut crate::leanh::LeanObject,
    mut v_a_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3507_ = l_Lean_Meta_Sym_instantiateS(
        v_e_3498_,
        v_subst_3499_,
        v_a_3500_,
        v_a_3501_,
        v_a_3502_,
        v_a_3503_,
        v_a_3504_,
        v_a_3505_,
    );
    crate::leanh::lean_dec(v_a_3505_);
    crate::leanh::lean_dec_ref(v_a_3504_);
    crate::leanh::lean_dec(v_a_3503_);
    crate::leanh::lean_dec_ref(v_a_3502_);
    crate::leanh::lean_dec(v_a_3501_);
    crate::leanh::lean_dec_ref(v_a_3500_);
    crate::leanh::lean_dec_ref(v_subst_3499_);
    return v_res_3507_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(
    mut v_f_3508_: *mut crate::leanh::LeanObject,
    mut v_a_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: u8,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_3510_ == 0 {
                    v___y_3513_ = v___y_3511_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_3508_);
                    v___x_3516_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_f_3508_,
                        v___y_3510_,
                        v___y_3511_,
                    );
                    v_snd_3517_ = crate::leanh::lean_ctor_get(v___x_3516_, 1);
                    crate::leanh::lean_inc(v_snd_3517_);
                    crate::leanh::lean_dec_ref(v___x_3516_);
                    crate::leanh::lean_inc_ref(v_a_3509_);
                    v___x_3518_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_a_3509_,
                        v___y_3510_,
                        v_snd_3517_,
                    );
                    v_snd_3519_ = crate::leanh::lean_ctor_get(v___x_3518_, 1);
                    crate::leanh::lean_inc(v_snd_3519_);
                    crate::leanh::lean_dec_ref(v___x_3518_);
                    v___y_3513_ = v_snd_3519_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3514_ = l_Lean_Expr_app___override(v_f_3508_, v_a_3509_);
                v___x_3515_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3514_, v___y_3513_);
                return v___x_3515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0___boxed(
    mut v_f_3520_: *mut crate::leanh::LeanObject,
    mut v_a_3521_: *mut crate::leanh::LeanObject,
    mut v___y_3522_: *mut crate::leanh::LeanObject,
    mut v___y_3523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1584__boxed_3524_: u8 = 0;
    let mut v_res_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_1584__boxed_3524_ = (crate::leanh::lean_unbox(v___y_3522_) as u8);
    v_res_3525_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_f_3520_, v_a_3521_, v___y_1584__boxed_3524_, v___y_3523_);
    return v_res_3525_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(
    mut v_revArgs_3526_: *mut crate::leanh::LeanObject,
    mut v_start_3527_: *mut crate::leanh::LeanObject,
    mut v_b_3528_: *mut crate::leanh::LeanObject,
    mut v_i_3529_: *mut crate::leanh::LeanObject,
    mut v___y_3530_: u8,
    mut v___y_3531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3532_ = lean_nat_dec_le(v_i_3529_, v_start_3527_);
                if v___x_3532_ == 0 {
                    v___x_3533_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_i_3534_ = lean_nat_sub(v_i_3529_, v___x_3533_);
                    crate::leanh::lean_dec(v_i_3529_);
                    v___x_3535_ = l_Lean_instInhabitedExpr;
                    v___x_3536_ = lean_array_get_borrowed(v___x_3535_, v_revArgs_3526_, v_i_3534_);
                    crate::leanh::lean_inc(v___x_3536_);
                    v___x_3537_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_b_3528_, v___x_3536_, v___y_3530_, v___y_3531_);
                    v_fst_3538_ = crate::leanh::lean_ctor_get(v___x_3537_, 0);
                    crate::leanh::lean_inc(v_fst_3538_);
                    v_snd_3539_ = crate::leanh::lean_ctor_get(v___x_3537_, 1);
                    crate::leanh::lean_inc(v_snd_3539_);
                    crate::leanh::lean_dec_ref(v___x_3537_);
                    v_b_3528_ = v_fst_3538_;
                    v_i_3529_ = v_i_3534_;
                    v___y_3531_ = v_snd_3539_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_i_3529_);
                    v___x_3541_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3541_, 0, v_b_3528_);
                    crate::leanh::lean_ctor_set(v___x_3541_, 1, v___y_3531_);
                    return v___x_3541_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0___boxed(
    mut v_revArgs_3542_: *mut crate::leanh::LeanObject,
    mut v_start_3543_: *mut crate::leanh::LeanObject,
    mut v_b_3544_: *mut crate::leanh::LeanObject,
    mut v_i_3545_: *mut crate::leanh::LeanObject,
    mut v___y_3546_: *mut crate::leanh::LeanObject,
    mut v___y_3547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1608__boxed_3548_: u8 = 0;
    let mut v_res_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_1608__boxed_3548_ = (crate::leanh::lean_unbox(v___y_3546_) as u8);
    v_res_3549_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_3542_, v_start_3543_, v_b_3544_, v_i_3545_, v___y_1608__boxed_3548_, v___y_3547_);
    crate::leanh::lean_dec(v_start_3543_);
    crate::leanh::lean_dec_ref(v_revArgs_3542_);
    return v_res_3549_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(
    mut v_revArgs_3550_: *mut crate::leanh::LeanObject,
    mut v_sz_3551_: *mut crate::leanh::LeanObject,
    mut v_e_3552_: *mut crate::leanh::LeanObject,
    mut v_i_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: u8,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_body_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: u8 = 0;
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_3552_) {
                6 => {
                    v_body_3556_ = crate::leanh::lean_ctor_get(v_e_3552_, 2);
                    crate::leanh::lean_inc_ref(v_body_3556_);
                    crate::leanh::lean_dec_ref_known(v_e_3552_, 3);
                    v___x_3557_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3558_ = lean_nat_add(v_i_3553_, v___x_3557_);
                    crate::leanh::lean_dec(v_i_3553_);
                    v___x_3559_ = lean_nat_dec_lt(v___x_3558_, v_sz_3551_);
                    if v___x_3559_ == 0 {
                        crate::leanh::lean_dec(v___x_3558_);
                        v___x_3560_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(v_body_3556_, v_revArgs_3550_, v_a_3554_, v_a_3555_);
                        return v___x_3560_;
                    } else {
                        v_e_3552_ = v_body_3556_;
                        v_i_3553_ = v___x_3558_;
                        state = 0;
                        continue;
                    }
                }
                10 => {
                    v_expr_3562_ = crate::leanh::lean_ctor_get(v_e_3552_, 1);
                    crate::leanh::lean_inc_ref(v_expr_3562_);
                    crate::leanh::lean_dec_ref_known(v_e_3552_, 2);
                    v_e_3552_ = v_expr_3562_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_n_3564_ = lean_nat_sub(v_sz_3551_, v_i_3553_);
                    crate::leanh::lean_dec(v_i_3553_);
                    v___x_3565_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_3552_, v_n_3564_, v_sz_3551_, v_revArgs_3550_, v_a_3554_, v_a_3555_);
                    v_fst_3566_ = crate::leanh::lean_ctor_get(v___x_3565_, 0);
                    crate::leanh::lean_inc(v_fst_3566_);
                    v_snd_3567_ = crate::leanh::lean_ctor_get(v___x_3565_, 1);
                    crate::leanh::lean_inc(v_snd_3567_);
                    crate::leanh::lean_dec_ref(v___x_3565_);
                    v___x_3568_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3569_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_3550_, v___x_3568_, v_fst_3566_, v_n_3564_, v_a_3554_, v_snd_3567_);
                    return v___x_3569_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go___boxed(
    mut v_revArgs_3570_: *mut crate::leanh::LeanObject,
    mut v_sz_3571_: *mut crate::leanh::LeanObject,
    mut v_e_3572_: *mut crate::leanh::LeanObject,
    mut v_i_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3576_: u8 = 0;
    let mut v_res_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3576_ = (crate::leanh::lean_unbox(v_a_3574_) as u8);
    v_res_3577_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(
        v_revArgs_3570_,
        v_sz_3571_,
        v_e_3572_,
        v_i_3573_,
        v_a_boxed_3576_,
        v_a_3575_,
    );
    crate::leanh::lean_dec(v_sz_3571_);
    crate::leanh::lean_dec_ref(v_revArgs_3570_);
    return v_res_3577_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(
    mut v_f_3578_: *mut crate::leanh::LeanObject,
    mut v_revArgs_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: u8,
    mut v_a_3581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    v_sz_3582_ = lean_array_get_size(v_revArgs_3579_);
    v___x_3583_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3584_ = lean_nat_dec_eq(v_sz_3582_, v___x_3583_);
    if v___x_3584_ == 0 {
        let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3585_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(
            v_revArgs_3579_,
            v_sz_3582_,
            v_f_3578_,
            v___x_3583_,
            v_a_3580_,
            v_a_3581_,
        );
        return v___x_3585_;
    } else {
        let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3586_, 0, v_f_3578_);
        crate::leanh::lean_ctor_set(v___x_3586_, 1, v_a_3581_);
        return v___x_3586_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed(
    mut v_f_3587_: *mut crate::leanh::LeanObject,
    mut v_revArgs_3588_: *mut crate::leanh::LeanObject,
    mut v_a_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3591_: u8 = 0;
    let mut v_res_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3591_ = (crate::leanh::lean_unbox(v_a_3589_) as u8);
    v_res_3592_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(
        v_f_3587_,
        v_revArgs_3588_,
        v_a_boxed_3591_,
        v_a_3590_,
    );
    crate::leanh::lean_dec_ref(v_revArgs_3588_);
    return v_res_3592_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_3593_: *mut crate::leanh::LeanObject,
    mut v_x_3594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3600_: u8 = 0;
    let mut v_fst_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: u64 = 0;
    let mut v___x_3605_: u64 = 0;
    let mut v___x_3606_: u64 = 0;
    let mut v___x_3607_: u64 = 0;
    let mut v___x_3608_: u64 = 0;
    let mut v_fold_3609_: u64 = 0;
    let mut v___x_3610_: u64 = 0;
    let mut v___x_3611_: u64 = 0;
    let mut v___x_3612_: u64 = 0;
    let mut v___x_3613_: usize = 0;
    let mut v___x_3614_: usize = 0;
    let mut v___x_3615_: usize = 0;
    let mut v___x_3616_: usize = 0;
    let mut v___x_3617_: usize = 0;
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3594_) == 0 {
                    return v_x_3593_;
                } else {
                    v_key_3595_ = crate::leanh::lean_ctor_get(v_x_3594_, 0);
                    v_value_3596_ = crate::leanh::lean_ctor_get(v_x_3594_, 1);
                    v_tail_3597_ = crate::leanh::lean_ctor_get(v_x_3594_, 2);
                    v_isSharedCheck_3624_ = (!crate::leanh::lean_is_exclusive(v_x_3594_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v___x_3599_ = v_x_3594_;
                        v_isShared_3600_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3597_);
                        crate::leanh::lean_inc(v_value_3596_);
                        crate::leanh::lean_inc(v_key_3595_);
                        crate::leanh::lean_dec(v_x_3594_);
                        v___x_3599_ = crate::leanh::lean_box(0);
                        v_isShared_3600_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3601_ = crate::leanh::lean_ctor_get(v_key_3595_, 0);
                v_snd_3602_ = crate::leanh::lean_ctor_get(v_key_3595_, 1);
                v___x_3603_ = lean_array_get_size(v_x_3593_);
                v___x_3604_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_3601_);
                v___x_3605_ = lean_uint64_of_nat(v_snd_3602_);
                v___x_3606_ = lean_uint64_mix_hash(v___x_3604_, v___x_3605_);
                v___x_3607_ = 32u64;
                v___x_3608_ = lean_uint64_shift_right(v___x_3606_, v___x_3607_);
                v_fold_3609_ = lean_uint64_xor(v___x_3606_, v___x_3608_);
                v___x_3610_ = 16u64;
                v___x_3611_ = lean_uint64_shift_right(v_fold_3609_, v___x_3610_);
                v___x_3612_ = lean_uint64_xor(v_fold_3609_, v___x_3611_);
                v___x_3613_ = lean_uint64_to_usize(v___x_3612_);
                v___x_3614_ = lean_usize_of_nat(v___x_3603_);
                v___x_3615_ = 1usize;
                v___x_3616_ = lean_usize_sub(v___x_3614_, v___x_3615_);
                v___x_3617_ = lean_usize_land(v___x_3613_, v___x_3616_);
                v___x_3618_ = lean_array_uget_borrowed(v_x_3593_, v___x_3617_);
                crate::leanh::lean_inc(v___x_3618_);
                if v_isShared_3600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3599_, 2, v___x_3618_);
                    v___x_3620_ = v___x_3599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_key_3595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_value_3596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 2, v___x_3618_);
                    v___x_3620_ = v_reuseFailAlloc_3623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3621_ = lean_array_uset(v_x_3593_, v___x_3617_, v___x_3620_);
                v_x_3593_ = v___x_3621_;
                v_x_3594_ = v_tail_3597_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(
    mut v_i_3625_: *mut crate::leanh::LeanObject,
    mut v_source_3626_: *mut crate::leanh::LeanObject,
    mut v_target_3627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v_es_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3628_ = lean_array_get_size(v_source_3626_);
                v___x_3629_ = lean_nat_dec_lt(v_i_3625_, v___x_3628_);
                if v___x_3629_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3626_);
                    crate::leanh::lean_dec(v_i_3625_);
                    return v_target_3627_;
                } else {
                    v_es_3630_ = lean_array_fget(v_source_3626_, v_i_3625_);
                    v___x_3631_ = crate::leanh::lean_box(0);
                    v_source_3632_ = lean_array_fset(v_source_3626_, v_i_3625_, v___x_3631_);
                    v_target_3633_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3627_, v_es_3630_);
                    v___x_3634_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3635_ = lean_nat_add(v_i_3625_, v___x_3634_);
                    crate::leanh::lean_dec(v_i_3625_);
                    v_i_3625_ = v___x_3635_;
                    v_source_3626_ = v_source_3632_;
                    v_target_3627_ = v_target_3633_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(
    mut v_data_3637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3638_ = lean_array_get_size(v_data_3637_);
    v___x_3639_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3640_ = lean_nat_mul(v___x_3638_, v___x_3639_);
    v___x_3641_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3642_ = crate::leanh::lean_box(0);
    v___x_3643_ = lean_mk_array(v_nbuckets_3640_, v___x_3642_);
    v___x_3644_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_3641_, v_data_3637_, v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(
    mut v_a_3645_: *mut crate::leanh::LeanObject,
    mut v_b_3646_: *mut crate::leanh::LeanObject,
    mut v_x_3647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___y_3655_: u8 = 0;
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: u8 = 0;
    let mut v___x_3668_: u8 = 0;
    let mut v_isSharedCheck_3669_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3647_) == 0 {
                    crate::leanh::lean_dec(v_b_3646_);
                    crate::leanh::lean_dec_ref(v_a_3645_);
                    return v_x_3647_;
                } else {
                    v_key_3648_ = crate::leanh::lean_ctor_get(v_x_3647_, 0);
                    v_value_3649_ = crate::leanh::lean_ctor_get(v_x_3647_, 1);
                    v_tail_3650_ = crate::leanh::lean_ctor_get(v_x_3647_, 2);
                    v_isSharedCheck_3669_ = (!crate::leanh::lean_is_exclusive(v_x_3647_)) as u8;
                    if v_isSharedCheck_3669_ == 0 {
                        v___x_3652_ = v_x_3647_;
                        v_isShared_3653_ = v_isSharedCheck_3669_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3650_);
                        crate::leanh::lean_inc(v_value_3649_);
                        crate::leanh::lean_inc(v_key_3648_);
                        crate::leanh::lean_dec(v_x_3647_);
                        v___x_3652_ = crate::leanh::lean_box(0);
                        v_isShared_3653_ = v_isSharedCheck_3669_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3663_ = crate::leanh::lean_ctor_get(v_key_3648_, 0);
                v_snd_3664_ = crate::leanh::lean_ctor_get(v_key_3648_, 1);
                v_fst_3665_ = crate::leanh::lean_ctor_get(v_a_3645_, 0);
                v_snd_3666_ = crate::leanh::lean_ctor_get(v_a_3645_, 1);
                v___x_3667_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_fst_3663_,
                        v_fst_3665_,
                    );
                if v___x_3667_ == 0 {
                    v___y_3655_ = v___x_3667_;
                    state = 2;
                    continue;
                } else {
                    v___x_3668_ = lean_nat_dec_eq(v_snd_3664_, v_snd_3666_);
                    v___y_3655_ = v___x_3668_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_3655_ == 0 {
                    v___x_3656_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_3645_, v_b_3646_, v_tail_3650_);
                    if v_isShared_3653_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3652_, 2, v___x_3656_);
                        v___x_3658_ = v___x_3652_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3659_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_key_3648_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_value_3649_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3659_, 2, v___x_3656_);
                        v___x_3658_ = v_reuseFailAlloc_3659_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3649_);
                    crate::leanh::lean_dec(v_key_3648_);
                    if v_isShared_3653_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3652_, 1, v_b_3646_);
                        crate::leanh::lean_ctor_set(v___x_3652_, 0, v_a_3645_);
                        v___x_3661_ = v___x_3652_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3662_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3645_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_b_3646_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 2, v_tail_3650_);
                        v___x_3661_ = v_reuseFailAlloc_3662_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3658_;
            }
            4 => {
                return v___x_3661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(
    mut v_a_3670_: *mut crate::leanh::LeanObject,
    mut v_x_3671_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3672_: u8 = 0;
    let mut v_key_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3676_: u8 = 0;
    let mut v_fst_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3671_) == 0 {
                    v___x_3672_ = 0;
                    return v___x_3672_;
                } else {
                    v_key_3673_ = crate::leanh::lean_ctor_get(v_x_3671_, 0);
                    v_tail_3674_ = crate::leanh::lean_ctor_get(v_x_3671_, 2);
                    v_fst_3678_ = crate::leanh::lean_ctor_get(v_key_3673_, 0);
                    v_snd_3679_ = crate::leanh::lean_ctor_get(v_key_3673_, 1);
                    v_fst_3680_ = crate::leanh::lean_ctor_get(v_a_3670_, 0);
                    v_snd_3681_ = crate::leanh::lean_ctor_get(v_a_3670_, 1);
                    v___x_3682_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_3678_,
                            v_fst_3680_,
                        );
                    if v___x_3682_ == 0 {
                        v___y_3676_ = v___x_3682_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3683_ = lean_nat_dec_eq(v_snd_3679_, v_snd_3681_);
                        v___y_3676_ = v___x_3683_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3676_ == 0 {
                    v_x_3671_ = v_tail_3674_;
                    state = 0;
                    continue;
                } else {
                    return v___y_3676_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg___boxed(
    mut v_a_3684_: *mut crate::leanh::LeanObject,
    mut v_x_3685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3686_: u8 = 0;
    let mut v_r_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_3684_, v_x_3685_);
    crate::leanh::lean_dec(v_x_3685_);
    crate::leanh::lean_dec_ref(v_a_3684_);
    v_r_3687_ = crate::leanh::lean_box((v_res_3686_) as usize);
    return v_r_3687_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(
    mut v_m_3688_: *mut crate::leanh::LeanObject,
    mut v_a_3689_: *mut crate::leanh::LeanObject,
    mut v_b_3690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v_fst_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: u64 = 0;
    let mut v___x_3700_: u64 = 0;
    let mut v___x_3701_: u64 = 0;
    let mut v___x_3702_: u64 = 0;
    let mut v___x_3703_: u64 = 0;
    let mut v_fold_3704_: u64 = 0;
    let mut v___x_3705_: u64 = 0;
    let mut v___x_3706_: u64 = 0;
    let mut v___x_3707_: u64 = 0;
    let mut v___x_3708_: usize = 0;
    let mut v___x_3709_: usize = 0;
    let mut v___x_3710_: usize = 0;
    let mut v___x_3711_: usize = 0;
    let mut v___x_3712_: usize = 0;
    let mut v_bkt_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: u8 = 0;
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: u8 = 0;
    let mut v_val_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3691_ = crate::leanh::lean_ctor_get(v_m_3688_, 0);
                v_buckets_3692_ = crate::leanh::lean_ctor_get(v_m_3688_, 1);
                v_isSharedCheck_3739_ = (!crate::leanh::lean_is_exclusive(v_m_3688_)) as u8;
                if v_isSharedCheck_3739_ == 0 {
                    v___x_3694_ = v_m_3688_;
                    v_isShared_3695_ = v_isSharedCheck_3739_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3692_);
                    crate::leanh::lean_inc(v_size_3691_);
                    crate::leanh::lean_dec(v_m_3688_);
                    v___x_3694_ = crate::leanh::lean_box(0);
                    v_isShared_3695_ = v_isSharedCheck_3739_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3696_ = crate::leanh::lean_ctor_get(v_a_3689_, 0);
                v_snd_3697_ = crate::leanh::lean_ctor_get(v_a_3689_, 1);
                v___x_3698_ = lean_array_get_size(v_buckets_3692_);
                v___x_3699_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_3696_);
                v___x_3700_ = lean_uint64_of_nat(v_snd_3697_);
                v___x_3701_ = lean_uint64_mix_hash(v___x_3699_, v___x_3700_);
                v___x_3702_ = 32u64;
                v___x_3703_ = lean_uint64_shift_right(v___x_3701_, v___x_3702_);
                v_fold_3704_ = lean_uint64_xor(v___x_3701_, v___x_3703_);
                v___x_3705_ = 16u64;
                v___x_3706_ = lean_uint64_shift_right(v_fold_3704_, v___x_3705_);
                v___x_3707_ = lean_uint64_xor(v_fold_3704_, v___x_3706_);
                v___x_3708_ = lean_uint64_to_usize(v___x_3707_);
                v___x_3709_ = lean_usize_of_nat(v___x_3698_);
                v___x_3710_ = 1usize;
                v___x_3711_ = lean_usize_sub(v___x_3709_, v___x_3710_);
                v___x_3712_ = lean_usize_land(v___x_3708_, v___x_3711_);
                v_bkt_3713_ = lean_array_uget_borrowed(v_buckets_3692_, v___x_3712_);
                v___x_3714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_3689_, v_bkt_3713_);
                if v___x_3714_ == 0 {
                    v___x_3715_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3716_ = lean_nat_add(v_size_3691_, v___x_3715_);
                    crate::leanh::lean_dec(v_size_3691_);
                    crate::leanh::lean_inc(v_bkt_3713_);
                    v___x_3717_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3717_, 0, v_a_3689_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 1, v_b_3690_);
                    crate::leanh::lean_ctor_set(v___x_3717_, 2, v_bkt_3713_);
                    v_buckets_x27_3718_ =
                        lean_array_uset(v_buckets_3692_, v___x_3712_, v___x_3717_);
                    v___x_3719_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3720_ = lean_nat_mul(v_size_x27_3716_, v___x_3719_);
                    v___x_3721_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3722_ = lean_nat_div(v___x_3720_, v___x_3721_);
                    crate::leanh::lean_dec(v___x_3720_);
                    v___x_3723_ = lean_array_get_size(v_buckets_x27_3718_);
                    v___x_3724_ = lean_nat_dec_le(v___x_3722_, v___x_3723_);
                    crate::leanh::lean_dec(v___x_3722_);
                    if v___x_3724_ == 0 {
                        v_val_3725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_3718_);
                        if v_isShared_3695_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3694_, 1, v_val_3725_);
                            crate::leanh::lean_ctor_set(v___x_3694_, 0, v_size_x27_3716_);
                            v___x_3727_ = v___x_3694_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3728_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3728_,
                                0,
                                v_size_x27_3716_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_val_3725_);
                            v___x_3727_ = v_reuseFailAlloc_3728_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3695_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3694_, 1, v_buckets_x27_3718_);
                            crate::leanh::lean_ctor_set(v___x_3694_, 0, v_size_x27_3716_);
                            v___x_3730_ = v___x_3694_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3731_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3731_,
                                0,
                                v_size_x27_3716_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3731_,
                                1,
                                v_buckets_x27_3718_,
                            );
                            v___x_3730_ = v_reuseFailAlloc_3731_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3713_);
                    v___x_3732_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3733_ =
                        lean_array_uset(v_buckets_3692_, v___x_3712_, v___x_3732_);
                    v___x_3734_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_3689_, v_b_3690_, v_bkt_3713_);
                    v___x_3735_ = lean_array_uset(v_buckets_x27_3733_, v___x_3712_, v___x_3734_);
                    if v_isShared_3695_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3694_, 1, v___x_3735_);
                        v___x_3737_ = v___x_3694_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3738_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_size_3691_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 1, v___x_3735_);
                        v___x_3737_ = v_reuseFailAlloc_3738_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3727_;
            }
            3 => {
                return v___x_3730_;
            }
            4 => {
                return v___x_3737_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
    mut v_key_3740_: *mut crate::leanh::LeanObject,
    mut v_r_3741_: *mut crate::leanh::LeanObject,
    mut v_a_3742_: *mut crate::leanh::LeanObject,
    mut v_a_3743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_r_3741_);
    v___x_3744_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_3742_, v_key_3740_, v_r_3741_);
    v___x_3745_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3745_, 0, v_r_3741_);
    crate::leanh::lean_ctor_set(v___x_3745_, 1, v___x_3744_);
    v___x_3746_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3746_, 0, v___x_3745_);
    crate::leanh::lean_ctor_set(v___x_3746_, 1, v_a_3743_);
    return v___x_3746_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(
    mut v_key_3747_: *mut crate::leanh::LeanObject,
    mut v_r_3748_: *mut crate::leanh::LeanObject,
    mut v_a_3749_: *mut crate::leanh::LeanObject,
    mut v_a_3750_: u8,
    mut v_a_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3752_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
        v_key_3747_,
        v_r_3748_,
        v_a_3749_,
        v_a_3751_,
    );
    return v___x_3752_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(
    mut v_key_3753_: *mut crate::leanh::LeanObject,
    mut v_r_3754_: *mut crate::leanh::LeanObject,
    mut v_a_3755_: *mut crate::leanh::LeanObject,
    mut v_a_3756_: *mut crate::leanh::LeanObject,
    mut v_a_3757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3758_: u8 = 0;
    let mut v_res_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3758_ = (crate::leanh::lean_unbox(v_a_3756_) as u8);
    v_res_3759_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(
        v_key_3753_,
        v_r_3754_,
        v_a_3755_,
        v_a_boxed_3758_,
        v_a_3757_,
    );
    return v_res_3759_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0(
    mut v_00_u03b2_3760_: *mut crate::leanh::LeanObject,
    mut v_m_3761_: *mut crate::leanh::LeanObject,
    mut v_a_3762_: *mut crate::leanh::LeanObject,
    mut v_b_3763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3764_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_3761_, v_a_3762_, v_b_3763_);
    return v___x_3764_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(
    mut v_00_u03b2_3765_: *mut crate::leanh::LeanObject,
    mut v_a_3766_: *mut crate::leanh::LeanObject,
    mut v_x_3767_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3768_: u8 = 0;
    v___x_3768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_3766_, v_x_3767_);
    return v___x_3768_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(
    mut v_00_u03b2_3769_: *mut crate::leanh::LeanObject,
    mut v_a_3770_: *mut crate::leanh::LeanObject,
    mut v_x_3771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3772_: u8 = 0;
    let mut v_r_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_3769_, v_a_3770_, v_x_3771_);
    crate::leanh::lean_dec(v_x_3771_);
    crate::leanh::lean_dec_ref(v_a_3770_);
    v_r_3773_ = crate::leanh::lean_box((v_res_3772_) as usize);
    return v_r_3773_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(
    mut v_00_u03b2_3774_: *mut crate::leanh::LeanObject,
    mut v_data_3775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_3775_);
    return v___x_3776_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(
    mut v_00_u03b2_3777_: *mut crate::leanh::LeanObject,
    mut v_a_3778_: *mut crate::leanh::LeanObject,
    mut v_b_3779_: *mut crate::leanh::LeanObject,
    mut v_x_3780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3781_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_3778_, v_b_3779_, v_x_3780_);
    return v___x_3781_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3782_: *mut crate::leanh::LeanObject,
    mut v_i_3783_: *mut crate::leanh::LeanObject,
    mut v_source_3784_: *mut crate::leanh::LeanObject,
    mut v_target_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3786_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_3783_, v_source_3784_, v_target_3785_);
    return v___x_3786_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3787_: *mut crate::leanh::LeanObject,
    mut v_x_3788_: *mut crate::leanh::LeanObject,
    mut v_x_3789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3790_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3788_, v_x_3789_);
    return v___x_3790_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(
    mut v_idx_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3800_: u8 = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3794_ = l_Lean_Expr_bvar___override(v_idx_3791_);
                v___x_3795_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3794_, v___y_3793_);
                v_fst_3796_ = crate::leanh::lean_ctor_get(v___x_3795_, 0);
                v_snd_3797_ = crate::leanh::lean_ctor_get(v___x_3795_, 1);
                v_isSharedCheck_3805_ = (!crate::leanh::lean_is_exclusive(v___x_3795_)) as u8;
                if v_isSharedCheck_3805_ == 0 {
                    v___x_3799_ = v___x_3795_;
                    v_isShared_3800_ = v_isSharedCheck_3805_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3797_);
                    crate::leanh::lean_inc(v_fst_3796_);
                    crate::leanh::lean_dec(v___x_3795_);
                    v___x_3799_ = crate::leanh::lean_box(0);
                    v_isShared_3800_ = v_isSharedCheck_3805_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3800_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3799_, 1, v___y_3792_);
                    v___x_3802_ = v___x_3799_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3804_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_fst_3796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 1, v___y_3792_);
                    v___x_3802_ = v_reuseFailAlloc_3804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3803_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3803_, 0, v___x_3802_);
                crate::leanh::lean_ctor_set(v___x_3803_, 1, v_snd_3797_);
                return v___x_3803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(
    mut v_idx_3806_: *mut crate::leanh::LeanObject,
    mut v___y_3807_: *mut crate::leanh::LeanObject,
    mut v___y_3808_: u8,
    mut v___y_3809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3810_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_3806_, v___y_3807_, v___y_3809_);
    return v___x_3810_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(
    mut v_idx_3811_: *mut crate::leanh::LeanObject,
    mut v___y_3812_: *mut crate::leanh::LeanObject,
    mut v___y_3813_: *mut crate::leanh::LeanObject,
    mut v___y_3814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1291__boxed_3815_: u8 = 0;
    let mut v_res_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_1291__boxed_3815_ = (crate::leanh::lean_unbox(v___y_3813_) as u8);
    v_res_3816_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_3811_, v___y_3812_, v___y_1291__boxed_3815_, v___y_3814_);
    return v_res_3816_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(
    mut v_subst_3817_: *mut crate::leanh::LeanObject,
    mut v_e_3818_: *mut crate::leanh::LeanObject,
    mut v_bidx_3819_: *mut crate::leanh::LeanObject,
    mut v_offset_3820_: *mut crate::leanh::LeanObject,
    mut v_a_3821_: *mut crate::leanh::LeanObject,
    mut v_a_3822_: u8,
    mut v_a_3823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3824_ = lean_nat_dec_le(v_offset_3820_, v_bidx_3819_);
                if v___x_3824_ == 0 {
                    v___x_3825_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3825_, 0, v_e_3818_);
                    crate::leanh::lean_ctor_set(v___x_3825_, 1, v_a_3821_);
                    v___x_3826_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3826_, 0, v___x_3825_);
                    crate::leanh::lean_ctor_set(v___x_3826_, 1, v_a_3823_);
                    return v___x_3826_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_3818_);
                    v_n_3827_ = lean_array_get_size(v_subst_3817_);
                    v___x_3828_ = lean_nat_add(v_offset_3820_, v_n_3827_);
                    v___x_3829_ = lean_nat_dec_lt(v_bidx_3819_, v___x_3828_);
                    crate::leanh::lean_dec(v___x_3828_);
                    if v___x_3829_ == 0 {
                        v___x_3830_ = lean_nat_sub(v_bidx_3819_, v_n_3827_);
                        v___x_3831_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_3830_, v_a_3821_, v_a_3823_);
                        return v___x_3831_;
                    } else {
                        v___x_3832_ = lean_nat_sub(v_bidx_3819_, v_offset_3820_);
                        v___x_3833_ = lean_nat_sub(v_n_3827_, v___x_3832_);
                        crate::leanh::lean_dec(v___x_3832_);
                        v___x_3834_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3835_ = lean_nat_sub(v___x_3833_, v___x_3834_);
                        crate::leanh::lean_dec(v___x_3833_);
                        v_v_3836_ = lean_array_fget_borrowed(v_subst_3817_, v___x_3835_);
                        crate::leanh::lean_dec(v___x_3835_);
                        v___x_3837_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc(v_v_3836_);
                        v___x_3838_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                            v_v_3836_,
                            v___x_3837_,
                            v_offset_3820_,
                            v_a_3822_,
                            v_a_3823_,
                        );
                        v_fst_3839_ = crate::leanh::lean_ctor_get(v___x_3838_, 0);
                        v_snd_3840_ = crate::leanh::lean_ctor_get(v___x_3838_, 1);
                        v_isSharedCheck_3848_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3838_)) as u8;
                        if v_isSharedCheck_3848_ == 0 {
                            v___x_3842_ = v___x_3838_;
                            v_isShared_3843_ = v_isSharedCheck_3848_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3840_);
                            crate::leanh::lean_inc(v_fst_3839_);
                            crate::leanh::lean_dec(v___x_3838_);
                            v___x_3842_ = crate::leanh::lean_box(0);
                            v_isShared_3843_ = v_isSharedCheck_3848_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3842_, 1, v_a_3821_);
                    v___x_3845_ = v___x_3842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3847_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_fst_3839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_a_3821_);
                    v___x_3845_ = v_reuseFailAlloc_3847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3846_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3846_, 0, v___x_3845_);
                crate::leanh::lean_ctor_set(v___x_3846_, 1, v_snd_3840_);
                return v___x_3846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(
    mut v_subst_3849_: *mut crate::leanh::LeanObject,
    mut v_e_3850_: *mut crate::leanh::LeanObject,
    mut v_bidx_3851_: *mut crate::leanh::LeanObject,
    mut v_offset_3852_: *mut crate::leanh::LeanObject,
    mut v_a_3853_: *mut crate::leanh::LeanObject,
    mut v_a_3854_: *mut crate::leanh::LeanObject,
    mut v_a_3855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_3856_: u8 = 0;
    let mut v_res_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3856_ = (crate::leanh::lean_unbox(v_a_3854_) as u8);
    v_res_3857_ =
        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(
            v_subst_3849_,
            v_e_3850_,
            v_bidx_3851_,
            v_offset_3852_,
            v_a_3853_,
            v_a_boxed_3856_,
            v_a_3855_,
        );
    crate::leanh::lean_dec(v_offset_3852_);
    crate::leanh::lean_dec(v_bidx_3851_);
    crate::leanh::lean_dec_ref(v_subst_3849_);
    return v_res_3857_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3861_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2;
    v___x_3862_ = crate::leanh::lean_unsigned_to_nat(25);
    v___x_3863_ = crate::leanh::lean_unsigned_to_nat(148);
    v___x_3864_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1;
    v___x_3865_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0;
    v___x_3866_ = l_mkPanicMessageWithDecl(
        v___x_3865_,
        v___x_3864_,
        v___x_3863_,
        v___x_3862_,
        v___x_3861_,
    );
    return v___x_3866_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3868_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_3869_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_3870_ = crate::leanh::lean_unsigned_to_nat(165);
    v___x_3871_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0;
    v___x_3872_ = l_Lean_Meta_Sym_instantiateRevRangeS___closed__3;
    v___x_3873_ = l_mkPanicMessageWithDecl(
        v___x_3872_,
        v___x_3871_,
        v___x_3870_,
        v___x_3869_,
        v___x_3868_,
    );
    return v___x_3873_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(
    mut v_subst_3874_: *mut crate::leanh::LeanObject,
    mut v_e_3875_: *mut crate::leanh::LeanObject,
    mut v_f_3876_: *mut crate::leanh::LeanObject,
    mut v_argsRev_3877_: *mut crate::leanh::LeanObject,
    mut v_offset_3878_: *mut crate::leanh::LeanObject,
    mut v_modified_3879_: u8,
    mut v_a_3880_: *mut crate::leanh::LeanObject,
    mut v_a_3881_: u8,
    mut v_a_3882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: u8 = 0;
    let mut v___x_3892_: u8 = 0;
    let mut v_deBruijnIndex_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v_fst_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3921_: u8 = 0;
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match crate::leanh::lean_obj_tag(v_f_3876_) {
                    5 => {
                        v_fn_3883_ = crate::leanh::lean_ctor_get(v_f_3876_, 0);
                        crate::leanh::lean_inc_ref(v_fn_3883_);
                        v_arg_3884_ = crate::leanh::lean_ctor_get(v_f_3876_, 1);
                        crate::leanh::lean_inc_ref_n(v_arg_3884_, 2);
                        crate::leanh::lean_dec_ref_known(v_f_3876_, 2);
                        crate::leanh::lean_inc(v_offset_3878_);
                        v___x_3885_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3874_, v_arg_3884_, v_offset_3878_, v_a_3880_, v_a_3881_, v_a_3882_);
                        v_fst_3886_ = crate::leanh::lean_ctor_get(v___x_3885_, 0);
                        crate::leanh::lean_inc(v_fst_3886_);
                        v_snd_3887_ = crate::leanh::lean_ctor_get(v___x_3885_, 1);
                        crate::leanh::lean_inc(v_snd_3887_);
                        crate::leanh::lean_dec_ref(v___x_3885_);
                        v_fst_3888_ = crate::leanh::lean_ctor_get(v_fst_3886_, 0);
                        crate::leanh::lean_inc_n(v_fst_3888_, 2);
                        v_snd_3889_ = crate::leanh::lean_ctor_get(v_fst_3886_, 1);
                        crate::leanh::lean_inc(v_snd_3889_);
                        crate::leanh::lean_dec(v_fst_3886_);
                        v___x_3890_ = lean_array_push(v_argsRev_3877_, v_fst_3888_);
                        if v_modified_3879_ == 0 {
                            v___x_3891_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_3884_, v_fst_3888_);
                            crate::leanh::lean_dec(v_fst_3888_);
                            crate::leanh::lean_dec_ref(v_arg_3884_);
                            if v___x_3891_ == 0 {
                                v___x_3892_ = 1;
                                v_f_3876_ = v_fn_3883_;
                                v_argsRev_3877_ = v___x_3890_;
                                v_modified_3879_ = v___x_3892_;
                                v_a_3880_ = v_snd_3889_;
                                v_a_3882_ = v_snd_3887_;
                                state = 0;
                                continue;
                            } else {
                                v_f_3876_ = v_fn_3883_;
                                v_argsRev_3877_ = v___x_3890_;
                                v_a_3880_ = v_snd_3889_;
                                v_a_3882_ = v_snd_3887_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_3888_);
                            crate::leanh::lean_dec_ref(v_arg_3884_);
                            v_f_3876_ = v_fn_3883_;
                            v_argsRev_3877_ = v___x_3890_;
                            v_a_3880_ = v_snd_3889_;
                            v_a_3882_ = v_snd_3887_;
                            state = 0;
                            continue;
                        }
                    }
                    0 => {
                        v_deBruijnIndex_3896_ = crate::leanh::lean_ctor_get(v_f_3876_, 0);
                        crate::leanh::lean_inc_ref(v_f_3876_);
                        v___x_3897_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_3874_, v_f_3876_, v_deBruijnIndex_3896_, v_offset_3878_, v_a_3880_, v_a_3881_, v_a_3882_);
                        crate::leanh::lean_dec(v_offset_3878_);
                        v_fst_3898_ = crate::leanh::lean_ctor_get(v___x_3897_, 0);
                        v_snd_3899_ = crate::leanh::lean_ctor_get(v___x_3897_, 1);
                        v_isSharedCheck_3928_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3897_)) as u8;
                        if v_isSharedCheck_3928_ == 0 {
                            v___x_3901_ = v___x_3897_;
                            v_isShared_3902_ = v_isSharedCheck_3928_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3899_);
                            crate::leanh::lean_inc(v_fst_3898_);
                            crate::leanh::lean_dec(v___x_3897_);
                            v___x_3901_ = crate::leanh::lean_box(0);
                            v_isShared_3902_ = v_isSharedCheck_3928_;
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_offset_3878_);
                        crate::leanh::lean_dec_ref(v_argsRev_3877_);
                        crate::leanh::lean_dec_ref(v_f_3876_);
                        crate::leanh::lean_dec_ref(v_e_3875_);
                        v___x_3929_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once), _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
                        v___x_3930_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_3929_, v_a_3880_, v_a_3881_, v_a_3882_);
                        return v___x_3930_;
                    }
                }
            }
            1 => {
                v_fst_3903_ = crate::leanh::lean_ctor_get(v_fst_3898_, 0);
                v_snd_3904_ = crate::leanh::lean_ctor_get(v_fst_3898_, 1);
                v_isSharedCheck_3927_ = (!crate::leanh::lean_is_exclusive(v_fst_3898_)) as u8;
                if v_isSharedCheck_3927_ == 0 {
                    v___x_3906_ = v_fst_3898_;
                    v_isShared_3907_ = v_isSharedCheck_3927_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3904_);
                    crate::leanh::lean_inc(v_fst_3903_);
                    crate::leanh::lean_dec(v_fst_3898_);
                    v___x_3906_ = crate::leanh::lean_box(0);
                    v_isShared_3907_ = v_isSharedCheck_3927_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_modified_3879_ == 0 {
                    v___x_3922_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_f_3876_,
                            v_fst_3903_,
                        );
                    crate::leanh::lean_dec_ref_known(v_f_3876_, 1);
                    if v___x_3922_ == 0 {
                        crate::leanh::lean_del_object(v___x_3901_);
                        crate::leanh::lean_dec_ref(v_e_3875_);
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_3906_);
                        crate::leanh::lean_dec(v_fst_3903_);
                        crate::leanh::lean_dec_ref(v_argsRev_3877_);
                        if v_isShared_3902_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3901_, 1, v_snd_3904_);
                            crate::leanh::lean_ctor_set(v___x_3901_, 0, v_e_3875_);
                            v___x_3924_ = v___x_3901_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3926_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_e_3875_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_snd_3904_);
                            v___x_3924_ = v_reuseFailAlloc_3926_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3901_);
                    crate::leanh::lean_dec_ref_known(v_f_3876_, 1);
                    crate::leanh::lean_dec_ref(v_e_3875_);
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3909_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(
                    v_fst_3903_,
                    v_argsRev_3877_,
                    v_a_3881_,
                    v_snd_3899_,
                );
                crate::leanh::lean_dec_ref(v_argsRev_3877_);
                v_fst_3910_ = crate::leanh::lean_ctor_get(v___x_3909_, 0);
                v_snd_3911_ = crate::leanh::lean_ctor_get(v___x_3909_, 1);
                v_isSharedCheck_3921_ = (!crate::leanh::lean_is_exclusive(v___x_3909_)) as u8;
                if v_isSharedCheck_3921_ == 0 {
                    v___x_3913_ = v___x_3909_;
                    v_isShared_3914_ = v_isSharedCheck_3921_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3911_);
                    crate::leanh::lean_inc(v_fst_3910_);
                    crate::leanh::lean_dec(v___x_3909_);
                    v___x_3913_ = crate::leanh::lean_box(0);
                    v_isShared_3914_ = v_isSharedCheck_3921_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3914_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3913_, 1, v_snd_3904_);
                    v___x_3916_ = v___x_3913_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3920_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_fst_3910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_snd_3904_);
                    v___x_3916_ = v_reuseFailAlloc_3920_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3907_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3906_, 1, v_snd_3911_);
                    crate::leanh::lean_ctor_set(v___x_3906_, 0, v___x_3916_);
                    v___x_3918_ = v___x_3906_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_snd_3911_);
                    v___x_3918_ = v_reuseFailAlloc_3919_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3918_;
            }
            7 => {
                v___x_3925_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3925_, 0, v___x_3924_);
                crate::leanh::lean_ctor_set(v___x_3925_, 1, v_snd_3899_);
                return v___x_3925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(
    mut v_subst_3931_: *mut crate::leanh::LeanObject,
    mut v_e_3932_: *mut crate::leanh::LeanObject,
    mut v_f_3933_: *mut crate::leanh::LeanObject,
    mut v_arg_3934_: *mut crate::leanh::LeanObject,
    mut v_offset_3935_: *mut crate::leanh::LeanObject,
    mut v_a_3936_: *mut crate::leanh::LeanObject,
    mut v_a_3937_: u8,
    mut v_a_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v_fst_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___y_3958_: u8 = 0;
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3969_: u8 = 0;
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v_isSharedCheck_3973_: u8 = 0;
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: u8 = 0;
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_offset_3935_);
                crate::leanh::lean_inc_ref(v_arg_3934_);
                v___x_3939_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3931_, v_arg_3934_, v_offset_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
                v_fst_3940_ = crate::leanh::lean_ctor_get(v___x_3939_, 0);
                crate::leanh::lean_inc(v_fst_3940_);
                v_snd_3941_ = crate::leanh::lean_ctor_get(v___x_3939_, 1);
                crate::leanh::lean_inc(v_snd_3941_);
                crate::leanh::lean_dec_ref(v___x_3939_);
                v_fst_3942_ = crate::leanh::lean_ctor_get(v_fst_3940_, 0);
                crate::leanh::lean_inc(v_fst_3942_);
                v_snd_3943_ = crate::leanh::lean_ctor_get(v_fst_3940_, 1);
                crate::leanh::lean_inc(v_snd_3943_);
                crate::leanh::lean_dec(v_fst_3940_);
                v___x_3944_ = l_Lean_Expr_getAppFn(v_f_3933_);
                v___x_3945_ = l_Lean_Expr_isBVar(v___x_3944_);
                crate::leanh::lean_dec_ref(v___x_3944_);
                if v___x_3945_ == 0 {
                    crate::leanh::lean_dec_ref(v_arg_3934_);
                    v___x_3946_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_3931_, v_f_3933_, v_offset_3935_, v_snd_3943_, v_a_3937_, v_snd_3941_);
                    v_fst_3947_ = crate::leanh::lean_ctor_get(v___x_3946_, 0);
                    v_snd_3948_ = crate::leanh::lean_ctor_get(v___x_3946_, 1);
                    v_isSharedCheck_3973_ = (!crate::leanh::lean_is_exclusive(v___x_3946_)) as u8;
                    if v_isSharedCheck_3973_ == 0 {
                        v___x_3950_ = v___x_3946_;
                        v_isShared_3951_ = v_isSharedCheck_3973_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3948_);
                        crate::leanh::lean_inc(v_fst_3947_);
                        crate::leanh::lean_dec(v___x_3946_);
                        v___x_3950_ = crate::leanh::lean_box(0);
                        v_isShared_3951_ = v_isSharedCheck_3973_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3974_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3975_ = lean_mk_empty_array_with_capacity(v___x_3974_);
                    crate::leanh::lean_inc(v_fst_3942_);
                    v___x_3976_ = lean_array_push(v___x_3975_, v_fst_3942_);
                    v___x_3977_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_3934_,
                            v_fst_3942_,
                        );
                    crate::leanh::lean_dec(v_fst_3942_);
                    crate::leanh::lean_dec_ref(v_arg_3934_);
                    if v___x_3977_ == 0 {
                        v___x_3978_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_3931_, v_e_3932_, v_f_3933_, v___x_3976_, v_offset_3935_, v___x_3945_, v_snd_3943_, v_a_3937_, v_snd_3941_);
                        return v___x_3978_;
                    } else {
                        v___x_3979_ = 0;
                        v___x_3980_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_3931_, v_e_3932_, v_f_3933_, v___x_3976_, v_offset_3935_, v___x_3979_, v_snd_3943_, v_a_3937_, v_snd_3941_);
                        return v___x_3980_;
                    }
                }
            }
            1 => {
                v_fst_3952_ = crate::leanh::lean_ctor_get(v_fst_3947_, 0);
                v_snd_3953_ = crate::leanh::lean_ctor_get(v_fst_3947_, 1);
                v_isSharedCheck_3972_ = (!crate::leanh::lean_is_exclusive(v_fst_3947_)) as u8;
                if v_isSharedCheck_3972_ == 0 {
                    v___x_3955_ = v_fst_3947_;
                    v_isShared_3956_ = v_isSharedCheck_3972_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3953_);
                    crate::leanh::lean_inc(v_fst_3952_);
                    crate::leanh::lean_dec(v_fst_3947_);
                    v___x_3955_ = crate::leanh::lean_box(0);
                    v_isShared_3956_ = v_isSharedCheck_3972_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_e_3932_) == 5 {
                    v_fn_3966_ = crate::leanh::lean_ctor_get(v_e_3932_, 0);
                    v_arg_3967_ = crate::leanh::lean_ctor_get(v_e_3932_, 1);
                    v___x_3968_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fn_3966_,
                            v_fst_3952_,
                        );
                    if v___x_3968_ == 0 {
                        v___y_3958_ = v___x_3968_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3969_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_arg_3967_,
                                v_fst_3942_,
                            );
                        v___y_3958_ = v___x_3969_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3955_);
                    crate::leanh::lean_dec(v_fst_3952_);
                    crate::leanh::lean_del_object(v___x_3950_);
                    crate::leanh::lean_dec(v_fst_3942_);
                    crate::leanh::lean_dec_ref(v_e_3932_);
                    v___x_3970_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once), _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3);
                    v___x_3971_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_3970_, v_snd_3953_, v_a_3937_, v_snd_3948_);
                    return v___x_3971_;
                }
            }
            3 => {
                if v___y_3958_ == 0 {
                    crate::leanh::lean_del_object(v___x_3955_);
                    crate::leanh::lean_del_object(v___x_3950_);
                    crate::leanh::lean_dec_ref(v_e_3932_);
                    v___x_3959_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_3952_, v_fst_3942_, v_snd_3953_, v_a_3937_, v_snd_3948_);
                    return v___x_3959_;
                } else {
                    crate::leanh::lean_dec(v_fst_3952_);
                    crate::leanh::lean_dec(v_fst_3942_);
                    if v_isShared_3956_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3955_, 0, v_e_3932_);
                        v___x_3961_ = v___x_3955_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3965_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_e_3932_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3965_, 1, v_snd_3953_);
                        v___x_3961_ = v_reuseFailAlloc_3965_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3951_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3950_, 0, v___x_3961_);
                    v___x_3963_ = v___x_3950_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3961_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_snd_3948_);
                    v___x_3963_ = v_reuseFailAlloc_3964_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3963_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3982_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_3983_ = crate::leanh::lean_unsigned_to_nat(59);
    v___x_3984_ = crate::leanh::lean_unsigned_to_nat(176);
    v___x_3985_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0;
    v___x_3986_ = l_Lean_Meta_Sym_instantiateRevRangeS___closed__3;
    v___x_3987_ = l_mkPanicMessageWithDecl(
        v___x_3986_,
        v___x_3985_,
        v___x_3984_,
        v___x_3983_,
        v___x_3982_,
    );
    return v___x_3987_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(
    mut v_subst_3988_: *mut crate::leanh::LeanObject,
    mut v_e_3989_: *mut crate::leanh::LeanObject,
    mut v_offset_3990_: *mut crate::leanh::LeanObject,
    mut v_a_3991_: *mut crate::leanh::LeanObject,
    mut v_a_3992_: u8,
    mut v_a_3993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_deBruijnIndex_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4002_: u8 = 0;
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4015_: u8 = 0;
    let mut v_fst_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4020_: u8 = 0;
    let mut v___y_4022_: u8 = 0;
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: u8 = 0;
    let mut v___x_4031_: u8 = 0;
    let mut v_isSharedCheck_4032_: u8 = 0;
    let mut v_isSharedCheck_4033_: u8 = 0;
    let mut v_binderName_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4037_: u8 = 0;
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4050_: u8 = 0;
    let mut v_fst_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___y_4057_: u8 = 0;
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: u8 = 0;
    let mut v___x_4066_: u8 = 0;
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut v_declName_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_4073_: u8 = 0;
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v_fst_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4096_: u8 = 0;
    let mut v___y_4098_: u8 = 0;
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: u8 = 0;
    let mut v_isSharedCheck_4110_: u8 = 0;
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut v_data_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4119_: u8 = 0;
    let mut v_fst_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4133_: u8 = 0;
    let mut v_isSharedCheck_4134_: u8 = 0;
    let mut v_typeName_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4143_: u8 = 0;
    let mut v_fst_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4148_: u8 = 0;
    let mut v___x_4149_: u8 = 0;
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4157_: u8 = 0;
    let mut v_isSharedCheck_4158_: u8 = 0;
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_3989_) {
                0 => {
                    v_deBruijnIndex_3994_ = crate::leanh::lean_ctor_get(v_e_3989_, 0);
                    crate::leanh::lean_inc(v_deBruijnIndex_3994_);
                    v___x_3995_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_3988_, v_e_3989_, v_deBruijnIndex_3994_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    crate::leanh::lean_dec(v_offset_3990_);
                    crate::leanh::lean_dec(v_deBruijnIndex_3994_);
                    return v___x_3995_;
                }
                5 => {
                    v_fn_3996_ = crate::leanh::lean_ctor_get(v_e_3989_, 0);
                    crate::leanh::lean_inc_ref(v_fn_3996_);
                    v_arg_3997_ = crate::leanh::lean_ctor_get(v_e_3989_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3997_);
                    v___x_3998_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_3988_, v_e_3989_, v_fn_3996_, v_arg_3997_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    return v___x_3998_;
                }
                6 => {
                    v_binderName_3999_ = crate::leanh::lean_ctor_get(v_e_3989_, 0);
                    v_binderType_4000_ = crate::leanh::lean_ctor_get(v_e_3989_, 1);
                    v_body_4001_ = crate::leanh::lean_ctor_get(v_e_3989_, 2);
                    v_binderInfo_4002_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_3989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc(v_offset_3990_);
                    crate::leanh::lean_inc_ref(v_binderType_4000_);
                    v___x_4003_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_binderType_4000_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    v_fst_4004_ = crate::leanh::lean_ctor_get(v___x_4003_, 0);
                    crate::leanh::lean_inc(v_fst_4004_);
                    v_snd_4005_ = crate::leanh::lean_ctor_get(v___x_4003_, 1);
                    crate::leanh::lean_inc(v_snd_4005_);
                    crate::leanh::lean_dec_ref(v___x_4003_);
                    v_fst_4006_ = crate::leanh::lean_ctor_get(v_fst_4004_, 0);
                    crate::leanh::lean_inc(v_fst_4006_);
                    v_snd_4007_ = crate::leanh::lean_ctor_get(v_fst_4004_, 1);
                    crate::leanh::lean_inc(v_snd_4007_);
                    crate::leanh::lean_dec(v_fst_4004_);
                    v___x_4008_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4009_ = lean_nat_add(v_offset_3990_, v___x_4008_);
                    crate::leanh::lean_dec(v_offset_3990_);
                    crate::leanh::lean_inc_ref(v_body_4001_);
                    v___x_4010_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_body_4001_, v___x_4009_, v_snd_4007_, v_a_3992_, v_snd_4005_);
                    v_fst_4011_ = crate::leanh::lean_ctor_get(v___x_4010_, 0);
                    v_snd_4012_ = crate::leanh::lean_ctor_get(v___x_4010_, 1);
                    v_isSharedCheck_4033_ = (!crate::leanh::lean_is_exclusive(v___x_4010_)) as u8;
                    if v_isSharedCheck_4033_ == 0 {
                        v___x_4014_ = v___x_4010_;
                        v_isShared_4015_ = v_isSharedCheck_4033_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4012_);
                        crate::leanh::lean_inc(v_fst_4011_);
                        crate::leanh::lean_dec(v___x_4010_);
                        v___x_4014_ = crate::leanh::lean_box(0);
                        v_isShared_4015_ = v_isSharedCheck_4033_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_binderName_4034_ = crate::leanh::lean_ctor_get(v_e_3989_, 0);
                    v_binderType_4035_ = crate::leanh::lean_ctor_get(v_e_3989_, 1);
                    v_body_4036_ = crate::leanh::lean_ctor_get(v_e_3989_, 2);
                    v_binderInfo_4037_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_3989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc(v_offset_3990_);
                    crate::leanh::lean_inc_ref(v_binderType_4035_);
                    v___x_4038_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_binderType_4035_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    v_fst_4039_ = crate::leanh::lean_ctor_get(v___x_4038_, 0);
                    crate::leanh::lean_inc(v_fst_4039_);
                    v_snd_4040_ = crate::leanh::lean_ctor_get(v___x_4038_, 1);
                    crate::leanh::lean_inc(v_snd_4040_);
                    crate::leanh::lean_dec_ref(v___x_4038_);
                    v_fst_4041_ = crate::leanh::lean_ctor_get(v_fst_4039_, 0);
                    crate::leanh::lean_inc(v_fst_4041_);
                    v_snd_4042_ = crate::leanh::lean_ctor_get(v_fst_4039_, 1);
                    crate::leanh::lean_inc(v_snd_4042_);
                    crate::leanh::lean_dec(v_fst_4039_);
                    v___x_4043_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4044_ = lean_nat_add(v_offset_3990_, v___x_4043_);
                    crate::leanh::lean_dec(v_offset_3990_);
                    crate::leanh::lean_inc_ref(v_body_4036_);
                    v___x_4045_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_body_4036_, v___x_4044_, v_snd_4042_, v_a_3992_, v_snd_4040_);
                    v_fst_4046_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
                    v_snd_4047_ = crate::leanh::lean_ctor_get(v___x_4045_, 1);
                    v_isSharedCheck_4068_ = (!crate::leanh::lean_is_exclusive(v___x_4045_)) as u8;
                    if v_isSharedCheck_4068_ == 0 {
                        v___x_4049_ = v___x_4045_;
                        v_isShared_4050_ = v_isSharedCheck_4068_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4047_);
                        crate::leanh::lean_inc(v_fst_4046_);
                        crate::leanh::lean_dec(v___x_4045_);
                        v___x_4049_ = crate::leanh::lean_box(0);
                        v_isShared_4050_ = v_isSharedCheck_4068_;
                        state = 6;
                        continue;
                    }
                }
                8 => {
                    v_declName_4069_ = crate::leanh::lean_ctor_get(v_e_3989_, 0);
                    v_type_4070_ = crate::leanh::lean_ctor_get(v_e_3989_, 1);
                    v_value_4071_ = crate::leanh::lean_ctor_get(v_e_3989_, 2);
                    v_body_4072_ = crate::leanh::lean_ctor_get(v_e_3989_, 3);
                    v_nondep_4073_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_3989_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_inc_n(v_offset_3990_, 2);
                    crate::leanh::lean_inc_ref(v_type_4070_);
                    v___x_4074_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_type_4070_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    v_fst_4075_ = crate::leanh::lean_ctor_get(v___x_4074_, 0);
                    crate::leanh::lean_inc(v_fst_4075_);
                    v_snd_4076_ = crate::leanh::lean_ctor_get(v___x_4074_, 1);
                    crate::leanh::lean_inc(v_snd_4076_);
                    crate::leanh::lean_dec_ref(v___x_4074_);
                    v_fst_4077_ = crate::leanh::lean_ctor_get(v_fst_4075_, 0);
                    crate::leanh::lean_inc(v_fst_4077_);
                    v_snd_4078_ = crate::leanh::lean_ctor_get(v_fst_4075_, 1);
                    crate::leanh::lean_inc(v_snd_4078_);
                    crate::leanh::lean_dec(v_fst_4075_);
                    crate::leanh::lean_inc_ref(v_value_4071_);
                    v___x_4079_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_value_4071_, v_offset_3990_, v_snd_4078_, v_a_3992_, v_snd_4076_);
                    v_fst_4080_ = crate::leanh::lean_ctor_get(v___x_4079_, 0);
                    crate::leanh::lean_inc(v_fst_4080_);
                    v_snd_4081_ = crate::leanh::lean_ctor_get(v___x_4079_, 1);
                    crate::leanh::lean_inc(v_snd_4081_);
                    crate::leanh::lean_dec_ref(v___x_4079_);
                    v_fst_4082_ = crate::leanh::lean_ctor_get(v_fst_4080_, 0);
                    crate::leanh::lean_inc(v_fst_4082_);
                    v_snd_4083_ = crate::leanh::lean_ctor_get(v_fst_4080_, 1);
                    crate::leanh::lean_inc(v_snd_4083_);
                    crate::leanh::lean_dec(v_fst_4080_);
                    v___x_4084_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4085_ = lean_nat_add(v_offset_3990_, v___x_4084_);
                    crate::leanh::lean_dec(v_offset_3990_);
                    crate::leanh::lean_inc_ref(v_body_4072_);
                    v___x_4086_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_body_4072_, v___x_4085_, v_snd_4083_, v_a_3992_, v_snd_4081_);
                    v_fst_4087_ = crate::leanh::lean_ctor_get(v___x_4086_, 0);
                    v_snd_4088_ = crate::leanh::lean_ctor_get(v___x_4086_, 1);
                    v_isSharedCheck_4111_ = (!crate::leanh::lean_is_exclusive(v___x_4086_)) as u8;
                    if v_isSharedCheck_4111_ == 0 {
                        v___x_4090_ = v___x_4086_;
                        v_isShared_4091_ = v_isSharedCheck_4111_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4088_);
                        crate::leanh::lean_inc(v_fst_4087_);
                        crate::leanh::lean_dec(v___x_4086_);
                        v___x_4090_ = crate::leanh::lean_box(0);
                        v_isShared_4091_ = v_isSharedCheck_4111_;
                        state = 11;
                        continue;
                    }
                }
                10 => {
                    v_data_4112_ = crate::leanh::lean_ctor_get(v_e_3989_, 0);
                    v_expr_4113_ = crate::leanh::lean_ctor_get(v_e_3989_, 1);
                    crate::leanh::lean_inc_ref(v_expr_4113_);
                    v___x_4114_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_expr_4113_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    v_fst_4115_ = crate::leanh::lean_ctor_get(v___x_4114_, 0);
                    v_snd_4116_ = crate::leanh::lean_ctor_get(v___x_4114_, 1);
                    v_isSharedCheck_4134_ = (!crate::leanh::lean_is_exclusive(v___x_4114_)) as u8;
                    if v_isSharedCheck_4134_ == 0 {
                        v___x_4118_ = v___x_4114_;
                        v_isShared_4119_ = v_isSharedCheck_4134_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4116_);
                        crate::leanh::lean_inc(v_fst_4115_);
                        crate::leanh::lean_dec(v___x_4114_);
                        v___x_4118_ = crate::leanh::lean_box(0);
                        v_isShared_4119_ = v_isSharedCheck_4134_;
                        state = 16;
                        continue;
                    }
                }
                11 => {
                    v_typeName_4135_ = crate::leanh::lean_ctor_get(v_e_3989_, 0);
                    v_idx_4136_ = crate::leanh::lean_ctor_get(v_e_3989_, 1);
                    v_struct_4137_ = crate::leanh::lean_ctor_get(v_e_3989_, 2);
                    crate::leanh::lean_inc_ref(v_struct_4137_);
                    v___x_4138_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_struct_4137_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    v_fst_4139_ = crate::leanh::lean_ctor_get(v___x_4138_, 0);
                    v_snd_4140_ = crate::leanh::lean_ctor_get(v___x_4138_, 1);
                    v_isSharedCheck_4158_ = (!crate::leanh::lean_is_exclusive(v___x_4138_)) as u8;
                    if v_isSharedCheck_4158_ == 0 {
                        v___x_4142_ = v___x_4138_;
                        v_isShared_4143_ = v_isSharedCheck_4158_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4140_);
                        crate::leanh::lean_inc(v_fst_4139_);
                        crate::leanh::lean_dec(v___x_4138_);
                        v___x_4142_ = crate::leanh::lean_box(0);
                        v_isShared_4143_ = v_isSharedCheck_4158_;
                        state = 20;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_offset_3990_);
                    crate::leanh::lean_dec_ref(v_e_3989_);
                    v___x_4159_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once), _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
                    v___x_4160_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_4159_, v_a_3991_, v_a_3992_, v_a_3993_);
                    return v___x_4160_;
                }
            },
            1 => {
                v_fst_4016_ = crate::leanh::lean_ctor_get(v_fst_4011_, 0);
                v_snd_4017_ = crate::leanh::lean_ctor_get(v_fst_4011_, 1);
                v_isSharedCheck_4032_ = (!crate::leanh::lean_is_exclusive(v_fst_4011_)) as u8;
                if v_isSharedCheck_4032_ == 0 {
                    v___x_4019_ = v_fst_4011_;
                    v_isShared_4020_ = v_isSharedCheck_4032_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4017_);
                    crate::leanh::lean_inc(v_fst_4016_);
                    crate::leanh::lean_dec(v_fst_4011_);
                    v___x_4019_ = crate::leanh::lean_box(0);
                    v_isShared_4020_ = v_isSharedCheck_4032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4030_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_4000_,
                        v_fst_4006_,
                    );
                if v___x_4030_ == 0 {
                    v___y_4022_ = v___x_4030_;
                    state = 3;
                    continue;
                } else {
                    v___x_4031_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_4001_,
                            v_fst_4016_,
                        );
                    v___y_4022_ = v___x_4031_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_4022_ == 0 {
                    crate::leanh::lean_inc(v_binderName_3999_);
                    crate::leanh::lean_del_object(v___x_4019_);
                    crate::leanh::lean_del_object(v___x_4014_);
                    crate::leanh::lean_dec_ref_known(v_e_3989_, 3);
                    v___x_4023_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_3999_, v_binderInfo_4002_, v_fst_4006_, v_fst_4016_, v_snd_4017_, v_a_3992_, v_snd_4012_);
                    return v___x_4023_;
                } else {
                    crate::leanh::lean_dec(v_fst_4016_);
                    crate::leanh::lean_dec(v_fst_4006_);
                    if v_isShared_4020_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4019_, 0, v_e_3989_);
                        v___x_4025_ = v___x_4019_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4029_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_e_3989_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4029_, 1, v_snd_4017_);
                        v___x_4025_ = v_reuseFailAlloc_4029_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4015_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4014_, 0, v___x_4025_);
                    v___x_4027_ = v___x_4014_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4028_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4028_, 1, v_snd_4012_);
                    v___x_4027_ = v_reuseFailAlloc_4028_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4027_;
            }
            6 => {
                v_fst_4051_ = crate::leanh::lean_ctor_get(v_fst_4046_, 0);
                v_snd_4052_ = crate::leanh::lean_ctor_get(v_fst_4046_, 1);
                v_isSharedCheck_4067_ = (!crate::leanh::lean_is_exclusive(v_fst_4046_)) as u8;
                if v_isSharedCheck_4067_ == 0 {
                    v___x_4054_ = v_fst_4046_;
                    v_isShared_4055_ = v_isSharedCheck_4067_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4052_);
                    crate::leanh::lean_inc(v_fst_4051_);
                    crate::leanh::lean_dec(v_fst_4046_);
                    v___x_4054_ = crate::leanh::lean_box(0);
                    v_isShared_4055_ = v_isSharedCheck_4067_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4065_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_binderType_4035_,
                        v_fst_4041_,
                    );
                if v___x_4065_ == 0 {
                    v___y_4057_ = v___x_4065_;
                    state = 8;
                    continue;
                } else {
                    v___x_4066_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_4036_,
                            v_fst_4051_,
                        );
                    v___y_4057_ = v___x_4066_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_4057_ == 0 {
                    crate::leanh::lean_inc(v_binderName_4034_);
                    crate::leanh::lean_del_object(v___x_4054_);
                    crate::leanh::lean_del_object(v___x_4049_);
                    crate::leanh::lean_dec_ref_known(v_e_3989_, 3);
                    v___x_4058_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_4034_, v_binderInfo_4037_, v_fst_4041_, v_fst_4051_, v_snd_4052_, v_a_3992_, v_snd_4047_);
                    return v___x_4058_;
                } else {
                    crate::leanh::lean_dec(v_fst_4051_);
                    crate::leanh::lean_dec(v_fst_4041_);
                    if v_isShared_4055_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4054_, 0, v_e_3989_);
                        v___x_4060_ = v___x_4054_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4064_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_e_3989_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_snd_4052_);
                        v___x_4060_ = v_reuseFailAlloc_4064_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4050_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4049_, 0, v___x_4060_);
                    v___x_4062_ = v___x_4049_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_snd_4047_);
                    v___x_4062_ = v_reuseFailAlloc_4063_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4062_;
            }
            11 => {
                v_fst_4092_ = crate::leanh::lean_ctor_get(v_fst_4087_, 0);
                v_snd_4093_ = crate::leanh::lean_ctor_get(v_fst_4087_, 1);
                v_isSharedCheck_4110_ = (!crate::leanh::lean_is_exclusive(v_fst_4087_)) as u8;
                if v_isSharedCheck_4110_ == 0 {
                    v___x_4095_ = v_fst_4087_;
                    v_isShared_4096_ = v_isSharedCheck_4110_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4093_);
                    crate::leanh::lean_inc(v_fst_4092_);
                    crate::leanh::lean_dec(v_fst_4087_);
                    v___x_4095_ = crate::leanh::lean_box(0);
                    v_isShared_4096_ = v_isSharedCheck_4110_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4108_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_type_4070_,
                        v_fst_4077_,
                    );
                if v___x_4108_ == 0 {
                    v___y_4098_ = v___x_4108_;
                    state = 13;
                    continue;
                } else {
                    v___x_4109_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_value_4071_,
                            v_fst_4082_,
                        );
                    v___y_4098_ = v___x_4109_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v___y_4098_ == 0 {
                    crate::leanh::lean_inc(v_declName_4069_);
                    crate::leanh::lean_del_object(v___x_4095_);
                    crate::leanh::lean_del_object(v___x_4090_);
                    crate::leanh::lean_dec_ref_known(v_e_3989_, 4);
                    v___x_4099_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_4069_, v_fst_4077_, v_fst_4082_, v_fst_4092_, v_nondep_4073_, v_snd_4093_, v_a_3992_, v_snd_4088_);
                    return v___x_4099_;
                } else {
                    v___x_4100_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_4072_,
                            v_fst_4092_,
                        );
                    if v___x_4100_ == 0 {
                        crate::leanh::lean_inc(v_declName_4069_);
                        crate::leanh::lean_del_object(v___x_4095_);
                        crate::leanh::lean_del_object(v___x_4090_);
                        crate::leanh::lean_dec_ref_known(v_e_3989_, 4);
                        v___x_4101_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_4069_, v_fst_4077_, v_fst_4082_, v_fst_4092_, v_nondep_4073_, v_snd_4093_, v_a_3992_, v_snd_4088_);
                        return v___x_4101_;
                    } else {
                        crate::leanh::lean_dec(v_fst_4092_);
                        crate::leanh::lean_dec(v_fst_4082_);
                        crate::leanh::lean_dec(v_fst_4077_);
                        if v_isShared_4096_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4095_, 0, v_e_3989_);
                            v___x_4103_ = v___x_4095_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_4107_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_e_3989_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4107_, 1, v_snd_4093_);
                            v___x_4103_ = v_reuseFailAlloc_4107_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            14 => {
                if v_isShared_4091_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4090_, 0, v___x_4103_);
                    v___x_4105_ = v___x_4090_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4106_, 1, v_snd_4088_);
                    v___x_4105_ = v_reuseFailAlloc_4106_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4105_;
            }
            16 => {
                v_fst_4120_ = crate::leanh::lean_ctor_get(v_fst_4115_, 0);
                v_snd_4121_ = crate::leanh::lean_ctor_get(v_fst_4115_, 1);
                v_isSharedCheck_4133_ = (!crate::leanh::lean_is_exclusive(v_fst_4115_)) as u8;
                if v_isSharedCheck_4133_ == 0 {
                    v___x_4123_ = v_fst_4115_;
                    v_isShared_4124_ = v_isSharedCheck_4133_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4121_);
                    crate::leanh::lean_inc(v_fst_4120_);
                    crate::leanh::lean_dec(v_fst_4115_);
                    v___x_4123_ = crate::leanh::lean_box(0);
                    v_isShared_4124_ = v_isSharedCheck_4133_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4125_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_expr_4113_,
                        v_fst_4120_,
                    );
                if v___x_4125_ == 0 {
                    crate::leanh::lean_inc(v_data_4112_);
                    crate::leanh::lean_del_object(v___x_4123_);
                    crate::leanh::lean_del_object(v___x_4118_);
                    crate::leanh::lean_dec_ref_known(v_e_3989_, 2);
                    v___x_4126_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_4112_, v_fst_4120_, v_snd_4121_, v_a_3992_, v_snd_4116_);
                    return v___x_4126_;
                } else {
                    crate::leanh::lean_dec(v_fst_4120_);
                    if v_isShared_4124_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4123_, 0, v_e_3989_);
                        v___x_4128_ = v___x_4123_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_4132_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_e_3989_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_snd_4121_);
                        v___x_4128_ = v_reuseFailAlloc_4132_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4119_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4118_, 0, v___x_4128_);
                    v___x_4130_ = v___x_4118_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4128_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_snd_4116_);
                    v___x_4130_ = v_reuseFailAlloc_4131_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4130_;
            }
            20 => {
                v_fst_4144_ = crate::leanh::lean_ctor_get(v_fst_4139_, 0);
                v_snd_4145_ = crate::leanh::lean_ctor_get(v_fst_4139_, 1);
                v_isSharedCheck_4157_ = (!crate::leanh::lean_is_exclusive(v_fst_4139_)) as u8;
                if v_isSharedCheck_4157_ == 0 {
                    v___x_4147_ = v_fst_4139_;
                    v_isShared_4148_ = v_isSharedCheck_4157_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4145_);
                    crate::leanh::lean_inc(v_fst_4144_);
                    crate::leanh::lean_dec(v_fst_4139_);
                    v___x_4147_ = crate::leanh::lean_box(0);
                    v_isShared_4148_ = v_isSharedCheck_4157_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_4149_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_struct_4137_,
                        v_fst_4144_,
                    );
                if v___x_4149_ == 0 {
                    crate::leanh::lean_inc(v_idx_4136_);
                    crate::leanh::lean_inc(v_typeName_4135_);
                    crate::leanh::lean_del_object(v___x_4147_);
                    crate::leanh::lean_del_object(v___x_4142_);
                    crate::leanh::lean_dec_ref_known(v_e_3989_, 3);
                    v___x_4150_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_4135_, v_idx_4136_, v_fst_4144_, v_snd_4145_, v_a_3992_, v_snd_4140_);
                    return v___x_4150_;
                } else {
                    crate::leanh::lean_dec(v_fst_4144_);
                    if v_isShared_4148_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4147_, 0, v_e_3989_);
                        v___x_4152_ = v___x_4147_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_4156_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_e_3989_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4156_, 1, v_snd_4145_);
                        v___x_4152_ = v_reuseFailAlloc_4156_;
                        state = 22;
                        continue;
                    }
                }
            }
            22 => {
                if v_isShared_4143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4142_, 0, v___x_4152_);
                    v___x_4154_ = v___x_4142_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_snd_4140_);
                    v___x_4154_ = v_reuseFailAlloc_4155_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(
    mut v_subst_4161_: *mut crate::leanh::LeanObject,
    mut v_e_4162_: *mut crate::leanh::LeanObject,
    mut v_offset_4163_: *mut crate::leanh::LeanObject,
    mut v_a_4164_: *mut crate::leanh::LeanObject,
    mut v_a_4165_: u8,
    mut v_a_4166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: u8 = 0;
    v___x_4167_ = l_Lean_Expr_looseBVarRange(v_e_4162_);
    v___x_4168_ = lean_nat_dec_le(v___x_4167_, v_offset_4163_);
    crate::leanh::lean_dec(v___x_4167_);
    if v___x_4168_ == 0 {
        let mut v_key_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_offset_4163_);
        crate::leanh::lean_inc_ref(v_e_4162_);
        v_key_4169_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v_key_4169_, 0, v_e_4162_);
        crate::leanh::lean_ctor_set(v_key_4169_, 1, v_offset_4163_);
        v___x_4170_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_4164_, v_key_4169_);
        if crate::leanh::lean_obj_tag(v___x_4170_) == 1 {
            let mut v_val_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v_key_4169_, 2);
            crate::leanh::lean_dec(v_offset_4163_);
            crate::leanh::lean_dec_ref(v_e_4162_);
            v_val_4171_ = crate::leanh::lean_ctor_get(v___x_4170_, 0);
            crate::leanh::lean_inc(v_val_4171_);
            crate::leanh::lean_dec_ref_known(v___x_4170_, 1);
            v___x_4172_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4172_, 0, v_val_4171_);
            crate::leanh::lean_ctor_set(v___x_4172_, 1, v_a_4164_);
            v___x_4173_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4173_, 0, v___x_4172_);
            crate::leanh::lean_ctor_set(v___x_4173_, 1, v_a_4166_);
            return v___x_4173_;
        } else {
            crate::leanh::lean_dec(v___x_4170_);
            match crate::leanh::lean_obj_tag(v_e_4162_) {
                0 => {
                    let mut v_deBruijnIndex_4174_: *mut crate::leanh::LeanObject =
                        core::ptr::null_mut();
                    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_fst_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_snd_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_fst_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_snd_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v_deBruijnIndex_4174_ = crate::leanh::lean_ctor_get(v_e_4162_, 0);
                    crate::leanh::lean_inc(v_deBruijnIndex_4174_);
                    v___x_4175_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_4161_, v_e_4162_, v_deBruijnIndex_4174_, v_offset_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
                    crate::leanh::lean_dec(v_offset_4163_);
                    crate::leanh::lean_dec(v_deBruijnIndex_4174_);
                    v_fst_4176_ = crate::leanh::lean_ctor_get(v___x_4175_, 0);
                    crate::leanh::lean_inc(v_fst_4176_);
                    v_snd_4177_ = crate::leanh::lean_ctor_get(v___x_4175_, 1);
                    crate::leanh::lean_inc(v_snd_4177_);
                    crate::leanh::lean_dec_ref(v___x_4175_);
                    v_fst_4178_ = crate::leanh::lean_ctor_get(v_fst_4176_, 0);
                    crate::leanh::lean_inc(v_fst_4178_);
                    v_snd_4179_ = crate::leanh::lean_ctor_get(v_fst_4176_, 1);
                    crate::leanh::lean_inc(v_snd_4179_);
                    crate::leanh::lean_dec(v_fst_4176_);
                    v___x_4180_ =
                        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
                            v_key_4169_,
                            v_fst_4178_,
                            v_snd_4179_,
                            v_snd_4177_,
                        );
                    return v___x_4180_;
                }
                9 => {
                    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_offset_4163_);
                    v___x_4181_ =
                        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
                            v_key_4169_,
                            v_e_4162_,
                            v_a_4164_,
                            v_a_4166_,
                        );
                    return v___x_4181_;
                }
                2 => {
                    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_offset_4163_);
                    v___x_4182_ =
                        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
                            v_key_4169_,
                            v_e_4162_,
                            v_a_4164_,
                            v_a_4166_,
                        );
                    return v___x_4182_;
                }
                1 => {
                    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_offset_4163_);
                    v___x_4183_ =
                        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
                            v_key_4169_,
                            v_e_4162_,
                            v_a_4164_,
                            v_a_4166_,
                        );
                    return v___x_4183_;
                }
                4 => {
                    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_offset_4163_);
                    v___x_4184_ =
                        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
                            v_key_4169_,
                            v_e_4162_,
                            v_a_4164_,
                            v_a_4166_,
                        );
                    return v___x_4184_;
                }
                3 => {
                    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_offset_4163_);
                    v___x_4185_ =
                        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
                            v_key_4169_,
                            v_e_4162_,
                            v_a_4164_,
                            v_a_4166_,
                        );
                    return v___x_4185_;
                }
                _ => {
                    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_fst_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_snd_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_fst_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_snd_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_4186_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_4161_, v_e_4162_, v_offset_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
                    v_fst_4187_ = crate::leanh::lean_ctor_get(v___x_4186_, 0);
                    crate::leanh::lean_inc(v_fst_4187_);
                    v_snd_4188_ = crate::leanh::lean_ctor_get(v___x_4186_, 1);
                    crate::leanh::lean_inc(v_snd_4188_);
                    crate::leanh::lean_dec_ref(v___x_4186_);
                    v_fst_4189_ = crate::leanh::lean_ctor_get(v_fst_4187_, 0);
                    crate::leanh::lean_inc(v_fst_4189_);
                    v_snd_4190_ = crate::leanh::lean_ctor_get(v_fst_4187_, 1);
                    crate::leanh::lean_inc(v_snd_4190_);
                    crate::leanh::lean_dec(v_fst_4187_);
                    v___x_4191_ =
                        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
                            v_key_4169_,
                            v_fst_4189_,
                            v_snd_4190_,
                            v_snd_4188_,
                        );
                    return v___x_4191_;
                }
            }
        }
    } else {
        let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_offset_4163_);
        v___x_4192_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4192_, 0, v_e_4162_);
        crate::leanh::lean_ctor_set(v___x_4192_, 1, v_a_4164_);
        v___x_4193_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4193_, 0, v___x_4192_);
        crate::leanh::lean_ctor_set(v___x_4193_, 1, v_a_4166_);
        return v___x_4193_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(
    mut v_subst_4194_: *mut crate::leanh::LeanObject,
    mut v_e_4195_: *mut crate::leanh::LeanObject,
    mut v_offset_4196_: *mut crate::leanh::LeanObject,
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_a_4198_: u8,
    mut v_a_4199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: u8 = 0;
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: u8 = 0;
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_4195_) == 5 {
                    v_fn_4200_ = crate::leanh::lean_ctor_get(v_e_4195_, 0);
                    v_arg_4201_ = crate::leanh::lean_ctor_get(v_e_4195_, 1);
                    crate::leanh::lean_inc(v_offset_4196_);
                    crate::leanh::lean_inc_ref(v_e_4195_);
                    v_key_4202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_key_4202_, 0, v_e_4195_);
                    crate::leanh::lean_ctor_set(v_key_4202_, 1, v_offset_4196_);
                    v___x_4203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_4197_, v_key_4202_);
                    if crate::leanh::lean_obj_tag(v___x_4203_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_key_4202_, 2);
                        crate::leanh::lean_dec_ref_known(v_e_4195_, 2);
                        crate::leanh::lean_dec(v_offset_4196_);
                        v_val_4204_ = crate::leanh::lean_ctor_get(v___x_4203_, 0);
                        crate::leanh::lean_inc(v_val_4204_);
                        crate::leanh::lean_dec_ref_known(v___x_4203_, 1);
                        v___x_4205_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4205_, 0, v_val_4204_);
                        crate::leanh::lean_ctor_set(v___x_4205_, 1, v_a_4197_);
                        v___x_4206_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4206_, 0, v___x_4205_);
                        crate::leanh::lean_ctor_set(v___x_4206_, 1, v_a_4199_);
                        return v___x_4206_;
                    } else {
                        crate::leanh::lean_dec(v___x_4203_);
                        crate::leanh::lean_inc(v_offset_4196_);
                        crate::leanh::lean_inc_ref(v_fn_4200_);
                        v___x_4207_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_4194_, v_fn_4200_, v_offset_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
                        v_fst_4208_ = crate::leanh::lean_ctor_get(v___x_4207_, 0);
                        crate::leanh::lean_inc(v_fst_4208_);
                        v_snd_4209_ = crate::leanh::lean_ctor_get(v___x_4207_, 1);
                        crate::leanh::lean_inc(v_snd_4209_);
                        crate::leanh::lean_dec_ref(v___x_4207_);
                        v_fst_4210_ = crate::leanh::lean_ctor_get(v_fst_4208_, 0);
                        crate::leanh::lean_inc(v_fst_4210_);
                        v_snd_4211_ = crate::leanh::lean_ctor_get(v_fst_4208_, 1);
                        crate::leanh::lean_inc(v_snd_4211_);
                        crate::leanh::lean_dec(v_fst_4208_);
                        crate::leanh::lean_inc_ref(v_arg_4201_);
                        v___x_4212_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_4194_, v_arg_4201_, v_offset_4196_, v_snd_4211_, v_a_4198_, v_snd_4209_);
                        v_fst_4213_ = crate::leanh::lean_ctor_get(v___x_4212_, 0);
                        crate::leanh::lean_inc(v_fst_4213_);
                        v_snd_4214_ = crate::leanh::lean_ctor_get(v___x_4212_, 1);
                        crate::leanh::lean_inc(v_snd_4214_);
                        crate::leanh::lean_dec_ref(v___x_4212_);
                        v_fst_4215_ = crate::leanh::lean_ctor_get(v_fst_4213_, 0);
                        crate::leanh::lean_inc(v_fst_4215_);
                        v_snd_4216_ = crate::leanh::lean_ctor_get(v_fst_4213_, 1);
                        crate::leanh::lean_inc(v_snd_4216_);
                        crate::leanh::lean_dec(v_fst_4213_);
                        v___x_4226_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_fn_4200_,
                                v_fst_4210_,
                            );
                        if v___x_4226_ == 0 {
                            v___y_4218_ = v___x_4226_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4227_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_4201_, v_fst_4215_);
                            v___y_4218_ = v___x_4227_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_4228_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_4194_, v_e_4195_, v_offset_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
                    return v___x_4228_;
                }
            }
            1 => {
                if v___y_4218_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_4195_, 2);
                    v___x_4219_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_4210_, v_fst_4215_, v_snd_4216_, v_a_4198_, v_snd_4214_);
                    v_fst_4220_ = crate::leanh::lean_ctor_get(v___x_4219_, 0);
                    crate::leanh::lean_inc(v_fst_4220_);
                    v_snd_4221_ = crate::leanh::lean_ctor_get(v___x_4219_, 1);
                    crate::leanh::lean_inc(v_snd_4221_);
                    crate::leanh::lean_dec_ref(v___x_4219_);
                    v_fst_4222_ = crate::leanh::lean_ctor_get(v_fst_4220_, 0);
                    crate::leanh::lean_inc(v_fst_4222_);
                    v_snd_4223_ = crate::leanh::lean_ctor_get(v_fst_4220_, 1);
                    crate::leanh::lean_inc(v_snd_4223_);
                    crate::leanh::lean_dec(v_fst_4220_);
                    v___x_4224_ =
                        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
                            v_key_4202_,
                            v_fst_4222_,
                            v_snd_4223_,
                            v_snd_4221_,
                        );
                    return v___x_4224_;
                } else {
                    crate::leanh::lean_dec(v_fst_4215_);
                    crate::leanh::lean_dec(v_fst_4210_);
                    v___x_4225_ =
                        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
                            v_key_4202_,
                            v_e_4195_,
                            v_snd_4216_,
                            v_snd_4214_,
                        );
                    return v___x_4225_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault___boxed(
    mut v_subst_4229_: *mut crate::leanh::LeanObject,
    mut v_e_4230_: *mut crate::leanh::LeanObject,
    mut v_offset_4231_: *mut crate::leanh::LeanObject,
    mut v_a_4232_: *mut crate::leanh::LeanObject,
    mut v_a_4233_: *mut crate::leanh::LeanObject,
    mut v_a_4234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4235_: u8 = 0;
    let mut v_res_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4235_ = (crate::leanh::lean_unbox(v_a_4233_) as u8);
    v_res_4236_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_4229_, v_e_4230_, v_offset_4231_, v_a_4232_, v_a_boxed_4235_, v_a_4234_);
    crate::leanh::lean_dec_ref(v_subst_4229_);
    return v_res_4236_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(
    mut v_subst_4237_: *mut crate::leanh::LeanObject,
    mut v_e_4238_: *mut crate::leanh::LeanObject,
    mut v_offset_4239_: *mut crate::leanh::LeanObject,
    mut v_a_4240_: *mut crate::leanh::LeanObject,
    mut v_a_4241_: *mut crate::leanh::LeanObject,
    mut v_a_4242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4243_: u8 = 0;
    let mut v_res_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4243_ = (crate::leanh::lean_unbox(v_a_4241_) as u8);
    v_res_4244_ =
        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(
            v_subst_4237_,
            v_e_4238_,
            v_offset_4239_,
            v_a_4240_,
            v_a_boxed_4243_,
            v_a_4242_,
        );
    crate::leanh::lean_dec_ref(v_subst_4237_);
    return v_res_4244_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(
    mut v_subst_4245_: *mut crate::leanh::LeanObject,
    mut v_e_4246_: *mut crate::leanh::LeanObject,
    mut v_f_4247_: *mut crate::leanh::LeanObject,
    mut v_arg_4248_: *mut crate::leanh::LeanObject,
    mut v_offset_4249_: *mut crate::leanh::LeanObject,
    mut v_a_4250_: *mut crate::leanh::LeanObject,
    mut v_a_4251_: *mut crate::leanh::LeanObject,
    mut v_a_4252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4253_: u8 = 0;
    let mut v_res_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4253_ = (crate::leanh::lean_unbox(v_a_4251_) as u8);
    v_res_4254_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_4245_, v_e_4246_, v_f_4247_, v_arg_4248_, v_offset_4249_, v_a_4250_, v_a_boxed_4253_, v_a_4252_);
    crate::leanh::lean_dec_ref(v_subst_4245_);
    return v_res_4254_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(
    mut v_subst_4255_: *mut crate::leanh::LeanObject,
    mut v_e_4256_: *mut crate::leanh::LeanObject,
    mut v_f_4257_: *mut crate::leanh::LeanObject,
    mut v_argsRev_4258_: *mut crate::leanh::LeanObject,
    mut v_offset_4259_: *mut crate::leanh::LeanObject,
    mut v_modified_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modified_boxed_4264_: u8 = 0;
    let mut v_a_boxed_4265_: u8 = 0;
    let mut v_res_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modified_boxed_4264_ = (crate::leanh::lean_unbox(v_modified_4260_) as u8);
    v_a_boxed_4265_ = (crate::leanh::lean_unbox(v_a_4262_) as u8);
    v_res_4266_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_4255_, v_e_4256_, v_f_4257_, v_argsRev_4258_, v_offset_4259_, v_modified_boxed_4264_, v_a_4261_, v_a_boxed_4265_, v_a_4263_);
    crate::leanh::lean_dec_ref(v_subst_4255_);
    return v_res_4266_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(
    mut v_subst_4267_: *mut crate::leanh::LeanObject,
    mut v_e_4268_: *mut crate::leanh::LeanObject,
    mut v_offset_4269_: *mut crate::leanh::LeanObject,
    mut v_a_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
    mut v_a_4272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4273_: u8 = 0;
    let mut v_res_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4273_ = (crate::leanh::lean_unbox(v_a_4271_) as u8);
    v_res_4274_ =
        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(
            v_subst_4267_,
            v_e_4268_,
            v_offset_4269_,
            v_a_4270_,
            v_a_boxed_4273_,
            v_a_4272_,
        );
    crate::leanh::lean_dec_ref(v_subst_4267_);
    return v_res_4274_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(
    mut v_subst_4275_: *mut crate::leanh::LeanObject,
    mut v_e_4276_: *mut crate::leanh::LeanObject,
    mut v_f_4277_: *mut crate::leanh::LeanObject,
    mut v_arg_4278_: *mut crate::leanh::LeanObject,
    mut v_offset_4279_: *mut crate::leanh::LeanObject,
    mut v_x_4280_: *mut crate::leanh::LeanObject,
    mut v_a_4281_: *mut crate::leanh::LeanObject,
    mut v_a_4282_: u8,
    mut v_a_4283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_4275_, v_e_4276_, v_f_4277_, v_arg_4278_, v_offset_4279_, v_a_4281_, v_a_4282_, v_a_4283_);
    return v___x_4284_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(
    mut v_subst_4285_: *mut crate::leanh::LeanObject,
    mut v_e_4286_: *mut crate::leanh::LeanObject,
    mut v_f_4287_: *mut crate::leanh::LeanObject,
    mut v_arg_4288_: *mut crate::leanh::LeanObject,
    mut v_offset_4289_: *mut crate::leanh::LeanObject,
    mut v_x_4290_: *mut crate::leanh::LeanObject,
    mut v_a_4291_: *mut crate::leanh::LeanObject,
    mut v_a_4292_: *mut crate::leanh::LeanObject,
    mut v_a_4293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4294_: u8 = 0;
    let mut v_res_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4294_ = (crate::leanh::lean_unbox(v_a_4292_) as u8);
    v_res_4295_ =
        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(
            v_subst_4285_,
            v_e_4286_,
            v_f_4287_,
            v_arg_4288_,
            v_offset_4289_,
            v_x_4290_,
            v_a_4291_,
            v_a_boxed_4294_,
            v_a_4293_,
        );
    crate::leanh::lean_dec_ref(v_subst_4285_);
    return v_res_4295_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(
    mut v_e_4296_: *mut crate::leanh::LeanObject,
    mut v_subst_4297_: *mut crate::leanh::LeanObject,
    mut v_a_4298_: u8,
    mut v_a_4299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4301_: u8 = 0;
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4310_: u8 = 0;
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut v_unused_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: u8 = 0;
    let mut v___x_4320_: u8 = 0;
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4317_ = lean_array_get_size(v_subst_4297_);
                v___x_4318_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4319_ = lean_nat_dec_eq(v___x_4317_, v___x_4318_);
                if v___x_4319_ == 0 {
                    v___x_4320_ = l_Lean_Expr_hasLooseBVars(v_e_4296_);
                    if v___x_4320_ == 0 {
                        v___x_4321_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4321_, 0, v_e_4296_);
                        crate::leanh::lean_ctor_set(v___x_4321_, 1, v_a_4299_);
                        return v___x_4321_;
                    } else {
                        v___y_4301_ = v___x_4319_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_4301_ = v___x_4319_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4301_ == 0 {
                    v___x_4302_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4303_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once
                        ),
                        _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2,
                    );
                    v___x_4304_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_4297_, v_e_4296_, v___x_4302_, v___x_4303_, v_a_4298_, v_a_4299_);
                    v_fst_4305_ = crate::leanh::lean_ctor_get(v___x_4304_, 0);
                    crate::leanh::lean_inc(v_fst_4305_);
                    v_snd_4306_ = crate::leanh::lean_ctor_get(v___x_4304_, 1);
                    crate::leanh::lean_inc(v_snd_4306_);
                    crate::leanh::lean_dec_ref(v___x_4304_);
                    v_fst_4307_ = crate::leanh::lean_ctor_get(v_fst_4305_, 0);
                    v_isSharedCheck_4314_ = (!crate::leanh::lean_is_exclusive(v_fst_4305_)) as u8;
                    if v_isSharedCheck_4314_ == 0 {
                        v_unused_4315_ = crate::leanh::lean_ctor_get(v_fst_4305_, 1);
                        crate::leanh::lean_dec(v_unused_4315_);
                        v___x_4309_ = v_fst_4305_;
                        v_isShared_4310_ = v_isSharedCheck_4314_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4307_);
                        crate::leanh::lean_dec(v_fst_4305_);
                        v___x_4309_ = crate::leanh::lean_box(0);
                        v_isShared_4310_ = v_isSharedCheck_4314_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4316_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4316_, 0, v_e_4296_);
                    crate::leanh::lean_ctor_set(v___x_4316_, 1, v_a_4299_);
                    return v___x_4316_;
                }
            }
            2 => {
                if v_isShared_4310_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4309_, 1, v_snd_4306_);
                    v___x_4312_ = v___x_4309_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4313_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_fst_4307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4313_, 1, v_snd_4306_);
                    v___x_4312_ = v_reuseFailAlloc_4313_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27___boxed(
    mut v_e_4322_: *mut crate::leanh::LeanObject,
    mut v_subst_4323_: *mut crate::leanh::LeanObject,
    mut v_a_4324_: *mut crate::leanh::LeanObject,
    mut v_a_4325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_4326_: u8 = 0;
    let mut v_res_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_4326_ = (crate::leanh::lean_unbox(v_a_4324_) as u8);
    v_res_4327_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(
        v_e_4322_,
        v_subst_4323_,
        v_a_boxed_4326_,
        v_a_4325_,
    );
    crate::leanh::lean_dec_ref(v_subst_4323_);
    return v_res_4327_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
    mut v_e_4328_: *mut crate::leanh::LeanObject,
    mut v_subst_4329_: *mut crate::leanh::LeanObject,
    mut v_a_4330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4332_: u8 = 0;
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: u8 = 0;
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4348_: u8 = 0;
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4351_: u8 = 0;
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4357_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4371_: u8 = 0;
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4380_: u8 = 0;
    let mut v_unused_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4332_ = l_Lean_Expr_hasLooseBVars(v_e_4328_);
                if v___x_4332_ == 0 {
                    v___x_4333_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4333_, 0, v_e_4328_);
                    return v___x_4333_;
                } else {
                    v___x_4334_ = lean_array_get_size(v_subst_4329_);
                    v___x_4335_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4336_ = lean_nat_dec_eq(v___x_4334_, v___x_4335_);
                    if v___x_4336_ == 0 {
                        v___x_4337_ = lean_st_ref_take(v_a_4330_);
                        v_share_4338_ = crate::leanh::lean_ctor_get(v___x_4337_, 0);
                        v_maxFVar_4339_ = crate::leanh::lean_ctor_get(v___x_4337_, 1);
                        v_proofInstInfo_4340_ = crate::leanh::lean_ctor_get(v___x_4337_, 2);
                        v_inferType_4341_ = crate::leanh::lean_ctor_get(v___x_4337_, 3);
                        v_getLevel_4342_ = crate::leanh::lean_ctor_get(v___x_4337_, 4);
                        v_congrInfo_4343_ = crate::leanh::lean_ctor_get(v___x_4337_, 5);
                        v_defEqI_4344_ = crate::leanh::lean_ctor_get(v___x_4337_, 6);
                        v_extensions_4345_ = crate::leanh::lean_ctor_get(v___x_4337_, 7);
                        v_issues_4346_ = crate::leanh::lean_ctor_get(v___x_4337_, 8);
                        v_canon_4347_ = crate::leanh::lean_ctor_get(v___x_4337_, 9);
                        v_debug_4348_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_4337_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        );
                        v_isSharedCheck_4383_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4337_)) as u8;
                        if v_isSharedCheck_4383_ == 0 {
                            v___x_4350_ = v___x_4337_;
                            v_isShared_4351_ = v_isSharedCheck_4383_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_canon_4347_);
                            crate::leanh::lean_inc(v_issues_4346_);
                            crate::leanh::lean_inc(v_extensions_4345_);
                            crate::leanh::lean_inc(v_defEqI_4344_);
                            crate::leanh::lean_inc(v_congrInfo_4343_);
                            crate::leanh::lean_inc(v_getLevel_4342_);
                            crate::leanh::lean_inc(v_inferType_4341_);
                            crate::leanh::lean_inc(v_proofInstInfo_4340_);
                            crate::leanh::lean_inc(v_maxFVar_4339_);
                            crate::leanh::lean_inc(v_share_4338_);
                            crate::leanh::lean_dec(v___x_4337_);
                            v___x_4350_ = crate::leanh::lean_box(0);
                            v_isShared_4351_ = v_isSharedCheck_4383_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4384_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4384_, 0, v_e_4328_);
                        return v___x_4384_;
                    }
                }
            }
            1 => {
                v___x_4352_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once),
                    _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0,
                );
                if v_isShared_4351_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4350_, 0, v___x_4352_);
                    v___x_4354_ = v___x_4350_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_maxFVar_4339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 2, v_proofInstInfo_4340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 3, v_inferType_4341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 4, v_getLevel_4342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 5, v_congrInfo_4343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 6, v_defEqI_4344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 7, v_extensions_4345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 8, v_issues_4346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 9, v_canon_4347_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4382_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_4348_,
                    );
                    v___x_4354_ = v_reuseFailAlloc_4382_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4355_ = lean_st_ref_set(v_a_4330_, v___x_4354_);
                v___x_4356_ = lean_st_ref_get(v_a_4330_);
                v_debug_4357_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4356_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_4356_);
                v___x_4358_ =
                    l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(
                        v_e_4328_,
                        v_subst_4329_,
                        v_debug_4357_,
                        v_share_4338_,
                    );
                v_fst_4359_ = crate::leanh::lean_ctor_get(v___x_4358_, 0);
                crate::leanh::lean_inc(v_fst_4359_);
                v_snd_4360_ = crate::leanh::lean_ctor_get(v___x_4358_, 1);
                crate::leanh::lean_inc(v_snd_4360_);
                crate::leanh::lean_dec_ref(v___x_4358_);
                v___x_4361_ = lean_st_ref_take(v_a_4330_);
                v_maxFVar_4362_ = crate::leanh::lean_ctor_get(v___x_4361_, 1);
                v_proofInstInfo_4363_ = crate::leanh::lean_ctor_get(v___x_4361_, 2);
                v_inferType_4364_ = crate::leanh::lean_ctor_get(v___x_4361_, 3);
                v_getLevel_4365_ = crate::leanh::lean_ctor_get(v___x_4361_, 4);
                v_congrInfo_4366_ = crate::leanh::lean_ctor_get(v___x_4361_, 5);
                v_defEqI_4367_ = crate::leanh::lean_ctor_get(v___x_4361_, 6);
                v_extensions_4368_ = crate::leanh::lean_ctor_get(v___x_4361_, 7);
                v_issues_4369_ = crate::leanh::lean_ctor_get(v___x_4361_, 8);
                v_canon_4370_ = crate::leanh::lean_ctor_get(v___x_4361_, 9);
                v_debug_4371_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4361_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4380_ = (!crate::leanh::lean_is_exclusive(v___x_4361_)) as u8;
                if v_isSharedCheck_4380_ == 0 {
                    v_unused_4381_ = crate::leanh::lean_ctor_get(v___x_4361_, 0);
                    crate::leanh::lean_dec(v_unused_4381_);
                    v___x_4373_ = v___x_4361_;
                    v_isShared_4374_ = v_isSharedCheck_4380_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_4370_);
                    crate::leanh::lean_inc(v_issues_4369_);
                    crate::leanh::lean_inc(v_extensions_4368_);
                    crate::leanh::lean_inc(v_defEqI_4367_);
                    crate::leanh::lean_inc(v_congrInfo_4366_);
                    crate::leanh::lean_inc(v_getLevel_4365_);
                    crate::leanh::lean_inc(v_inferType_4364_);
                    crate::leanh::lean_inc(v_proofInstInfo_4363_);
                    crate::leanh::lean_inc(v_maxFVar_4362_);
                    crate::leanh::lean_dec(v___x_4361_);
                    v___x_4373_ = crate::leanh::lean_box(0);
                    v_isShared_4374_ = v_isSharedCheck_4380_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4374_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4373_, 0, v_snd_4360_);
                    v___x_4376_ = v___x_4373_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4379_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_snd_4360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4379_, 1, v_maxFVar_4362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4379_, 2, v_proofInstInfo_4363_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4379_, 3, v_inferType_4364_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4379_, 4, v_getLevel_4365_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4379_, 5, v_congrInfo_4366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4379_, 6, v_defEqI_4367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4379_, 7, v_extensions_4368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4379_, 8, v_issues_4369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4379_, 9, v_canon_4370_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4379_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_4371_,
                    );
                    v___x_4376_ = v_reuseFailAlloc_4379_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4377_ = lean_st_ref_set(v_a_4330_, v___x_4376_);
                v___x_4378_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4378_, 0, v_fst_4359_);
                return v___x_4378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(
    mut v_e_4385_: *mut crate::leanh::LeanObject,
    mut v_subst_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4389_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_4385_, v_subst_4386_, v_a_4387_);
    crate::leanh::lean_dec(v_a_4387_);
    crate::leanh::lean_dec_ref(v_subst_4386_);
    return v_res_4389_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevBetaS(
    mut v_e_4390_: *mut crate::leanh::LeanObject,
    mut v_subst_4391_: *mut crate::leanh::LeanObject,
    mut v_a_4392_: *mut crate::leanh::LeanObject,
    mut v_a_4393_: *mut crate::leanh::LeanObject,
    mut v_a_4394_: *mut crate::leanh::LeanObject,
    mut v_a_4395_: *mut crate::leanh::LeanObject,
    mut v_a_4396_: *mut crate::leanh::LeanObject,
    mut v_a_4397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4399_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_4390_, v_subst_4391_, v_a_4393_);
    return v___x_4399_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevBetaS___boxed(
    mut v_e_4400_: *mut crate::leanh::LeanObject,
    mut v_subst_4401_: *mut crate::leanh::LeanObject,
    mut v_a_4402_: *mut crate::leanh::LeanObject,
    mut v_a_4403_: *mut crate::leanh::LeanObject,
    mut v_a_4404_: *mut crate::leanh::LeanObject,
    mut v_a_4405_: *mut crate::leanh::LeanObject,
    mut v_a_4406_: *mut crate::leanh::LeanObject,
    mut v_a_4407_: *mut crate::leanh::LeanObject,
    mut v_a_4408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4409_ = l_Lean_Meta_Sym_instantiateRevBetaS(
        v_e_4400_,
        v_subst_4401_,
        v_a_4402_,
        v_a_4403_,
        v_a_4404_,
        v_a_4405_,
        v_a_4406_,
        v_a_4407_,
    );
    crate::leanh::lean_dec(v_a_4407_);
    crate::leanh::lean_dec_ref(v_a_4406_);
    crate::leanh::lean_dec(v_a_4405_);
    crate::leanh::lean_dec_ref(v_a_4404_);
    crate::leanh::lean_dec(v_a_4403_);
    crate::leanh::lean_dec_ref(v_a_4402_);
    crate::leanh::lean_dec_ref(v_subst_4401_);
    return v_res_4409_;
}
pub unsafe fn l_Lean_Meta_Sym_betaRevS___redArg(
    mut v_f_4410_: *mut crate::leanh::LeanObject,
    mut v_revArgs_4411_: *mut crate::leanh::LeanObject,
    mut v_a_4412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4425_: u8 = 0;
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4428_: u8 = 0;
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4434_: u8 = 0;
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4448_: u8 = 0;
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut v_unused_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4414_ = lean_st_ref_take(v_a_4412_);
                v_share_4415_ = crate::leanh::lean_ctor_get(v___x_4414_, 0);
                v_maxFVar_4416_ = crate::leanh::lean_ctor_get(v___x_4414_, 1);
                v_proofInstInfo_4417_ = crate::leanh::lean_ctor_get(v___x_4414_, 2);
                v_inferType_4418_ = crate::leanh::lean_ctor_get(v___x_4414_, 3);
                v_getLevel_4419_ = crate::leanh::lean_ctor_get(v___x_4414_, 4);
                v_congrInfo_4420_ = crate::leanh::lean_ctor_get(v___x_4414_, 5);
                v_defEqI_4421_ = crate::leanh::lean_ctor_get(v___x_4414_, 6);
                v_extensions_4422_ = crate::leanh::lean_ctor_get(v___x_4414_, 7);
                v_issues_4423_ = crate::leanh::lean_ctor_get(v___x_4414_, 8);
                v_canon_4424_ = crate::leanh::lean_ctor_get(v___x_4414_, 9);
                v_debug_4425_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4414_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4460_ = (!crate::leanh::lean_is_exclusive(v___x_4414_)) as u8;
                if v_isSharedCheck_4460_ == 0 {
                    v___x_4427_ = v___x_4414_;
                    v_isShared_4428_ = v_isSharedCheck_4460_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_4424_);
                    crate::leanh::lean_inc(v_issues_4423_);
                    crate::leanh::lean_inc(v_extensions_4422_);
                    crate::leanh::lean_inc(v_defEqI_4421_);
                    crate::leanh::lean_inc(v_congrInfo_4420_);
                    crate::leanh::lean_inc(v_getLevel_4419_);
                    crate::leanh::lean_inc(v_inferType_4418_);
                    crate::leanh::lean_inc(v_proofInstInfo_4417_);
                    crate::leanh::lean_inc(v_maxFVar_4416_);
                    crate::leanh::lean_inc(v_share_4415_);
                    crate::leanh::lean_dec(v___x_4414_);
                    v___x_4427_ = crate::leanh::lean_box(0);
                    v_isShared_4428_ = v_isSharedCheck_4460_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4429_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once),
                    _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0,
                );
                if v_isShared_4428_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4427_, 0, v___x_4429_);
                    v___x_4431_ = v___x_4427_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4459_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 1, v_maxFVar_4416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 2, v_proofInstInfo_4417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 3, v_inferType_4418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 4, v_getLevel_4419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 5, v_congrInfo_4420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 6, v_defEqI_4421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 7, v_extensions_4422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 8, v_issues_4423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 9, v_canon_4424_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4459_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_4425_,
                    );
                    v___x_4431_ = v_reuseFailAlloc_4459_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4432_ = lean_st_ref_set(v_a_4412_, v___x_4431_);
                v___x_4433_ = lean_st_ref_get(v_a_4412_);
                v_debug_4434_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4433_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_4433_);
                v___x_4435_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(
                    v_f_4410_,
                    v_revArgs_4411_,
                    v_debug_4434_,
                    v_share_4415_,
                );
                v_fst_4436_ = crate::leanh::lean_ctor_get(v___x_4435_, 0);
                crate::leanh::lean_inc(v_fst_4436_);
                v_snd_4437_ = crate::leanh::lean_ctor_get(v___x_4435_, 1);
                crate::leanh::lean_inc(v_snd_4437_);
                crate::leanh::lean_dec_ref(v___x_4435_);
                v___x_4438_ = lean_st_ref_take(v_a_4412_);
                v_maxFVar_4439_ = crate::leanh::lean_ctor_get(v___x_4438_, 1);
                v_proofInstInfo_4440_ = crate::leanh::lean_ctor_get(v___x_4438_, 2);
                v_inferType_4441_ = crate::leanh::lean_ctor_get(v___x_4438_, 3);
                v_getLevel_4442_ = crate::leanh::lean_ctor_get(v___x_4438_, 4);
                v_congrInfo_4443_ = crate::leanh::lean_ctor_get(v___x_4438_, 5);
                v_defEqI_4444_ = crate::leanh::lean_ctor_get(v___x_4438_, 6);
                v_extensions_4445_ = crate::leanh::lean_ctor_get(v___x_4438_, 7);
                v_issues_4446_ = crate::leanh::lean_ctor_get(v___x_4438_, 8);
                v_canon_4447_ = crate::leanh::lean_ctor_get(v___x_4438_, 9);
                v_debug_4448_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_4438_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4457_ = (!crate::leanh::lean_is_exclusive(v___x_4438_)) as u8;
                if v_isSharedCheck_4457_ == 0 {
                    v_unused_4458_ = crate::leanh::lean_ctor_get(v___x_4438_, 0);
                    crate::leanh::lean_dec(v_unused_4458_);
                    v___x_4450_ = v___x_4438_;
                    v_isShared_4451_ = v_isSharedCheck_4457_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_4447_);
                    crate::leanh::lean_inc(v_issues_4446_);
                    crate::leanh::lean_inc(v_extensions_4445_);
                    crate::leanh::lean_inc(v_defEqI_4444_);
                    crate::leanh::lean_inc(v_congrInfo_4443_);
                    crate::leanh::lean_inc(v_getLevel_4442_);
                    crate::leanh::lean_inc(v_inferType_4441_);
                    crate::leanh::lean_inc(v_proofInstInfo_4440_);
                    crate::leanh::lean_inc(v_maxFVar_4439_);
                    crate::leanh::lean_dec(v___x_4438_);
                    v___x_4450_ = crate::leanh::lean_box(0);
                    v_isShared_4451_ = v_isSharedCheck_4457_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4450_, 0, v_snd_4437_);
                    v___x_4453_ = v___x_4450_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4456_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_snd_4437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 1, v_maxFVar_4439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 2, v_proofInstInfo_4440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 3, v_inferType_4441_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 4, v_getLevel_4442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 5, v_congrInfo_4443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 6, v_defEqI_4444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 7, v_extensions_4445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 8, v_issues_4446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4456_, 9, v_canon_4447_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4456_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_4448_,
                    );
                    v___x_4453_ = v_reuseFailAlloc_4456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4454_ = lean_st_ref_set(v_a_4412_, v___x_4453_);
                v___x_4455_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4455_, 0, v_fst_4436_);
                return v___x_4455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_betaRevS___redArg___boxed(
    mut v_f_4461_: *mut crate::leanh::LeanObject,
    mut v_revArgs_4462_: *mut crate::leanh::LeanObject,
    mut v_a_4463_: *mut crate::leanh::LeanObject,
    mut v_a_4464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4465_ = l_Lean_Meta_Sym_betaRevS___redArg(v_f_4461_, v_revArgs_4462_, v_a_4463_);
    crate::leanh::lean_dec(v_a_4463_);
    crate::leanh::lean_dec_ref(v_revArgs_4462_);
    return v_res_4465_;
}
pub unsafe fn l_Lean_Meta_Sym_betaRevS(
    mut v_f_4466_: *mut crate::leanh::LeanObject,
    mut v_revArgs_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
    mut v_a_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
    mut v_a_4472_: *mut crate::leanh::LeanObject,
    mut v_a_4473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4475_ = l_Lean_Meta_Sym_betaRevS___redArg(v_f_4466_, v_revArgs_4467_, v_a_4469_);
    return v___x_4475_;
}
pub unsafe fn l_Lean_Meta_Sym_betaRevS___boxed(
    mut v_f_4476_: *mut crate::leanh::LeanObject,
    mut v_revArgs_4477_: *mut crate::leanh::LeanObject,
    mut v_a_4478_: *mut crate::leanh::LeanObject,
    mut v_a_4479_: *mut crate::leanh::LeanObject,
    mut v_a_4480_: *mut crate::leanh::LeanObject,
    mut v_a_4481_: *mut crate::leanh::LeanObject,
    mut v_a_4482_: *mut crate::leanh::LeanObject,
    mut v_a_4483_: *mut crate::leanh::LeanObject,
    mut v_a_4484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4485_ = l_Lean_Meta_Sym_betaRevS(
        v_f_4476_,
        v_revArgs_4477_,
        v_a_4478_,
        v_a_4479_,
        v_a_4480_,
        v_a_4481_,
        v_a_4482_,
        v_a_4483_,
    );
    crate::leanh::lean_dec(v_a_4483_);
    crate::leanh::lean_dec_ref(v_a_4482_);
    crate::leanh::lean_dec(v_a_4481_);
    crate::leanh::lean_dec_ref(v_a_4480_);
    crate::leanh::lean_dec(v_a_4479_);
    crate::leanh::lean_dec_ref(v_a_4478_);
    crate::leanh::lean_dec_ref(v_revArgs_4477_);
    return v_res_4485_;
}
pub unsafe fn l_Lean_Meta_Sym_betaS___redArg(
    mut v_f_4486_: *mut crate::leanh::LeanObject,
    mut v_args_4487_: *mut crate::leanh::LeanObject,
    mut v_a_4488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4490_ = l_Array_reverse___redArg(v_args_4487_);
    v___x_4491_ = l_Lean_Meta_Sym_betaRevS___redArg(v_f_4486_, v___x_4490_, v_a_4488_);
    crate::leanh::lean_dec_ref(v___x_4490_);
    return v___x_4491_;
}
pub unsafe fn l_Lean_Meta_Sym_betaS___redArg___boxed(
    mut v_f_4492_: *mut crate::leanh::LeanObject,
    mut v_args_4493_: *mut crate::leanh::LeanObject,
    mut v_a_4494_: *mut crate::leanh::LeanObject,
    mut v_a_4495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4496_ = l_Lean_Meta_Sym_betaS___redArg(v_f_4492_, v_args_4493_, v_a_4494_);
    crate::leanh::lean_dec(v_a_4494_);
    return v_res_4496_;
}
pub unsafe fn l_Lean_Meta_Sym_betaS(
    mut v_f_4497_: *mut crate::leanh::LeanObject,
    mut v_args_4498_: *mut crate::leanh::LeanObject,
    mut v_a_4499_: *mut crate::leanh::LeanObject,
    mut v_a_4500_: *mut crate::leanh::LeanObject,
    mut v_a_4501_: *mut crate::leanh::LeanObject,
    mut v_a_4502_: *mut crate::leanh::LeanObject,
    mut v_a_4503_: *mut crate::leanh::LeanObject,
    mut v_a_4504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4506_ = l_Lean_Meta_Sym_betaS___redArg(v_f_4497_, v_args_4498_, v_a_4500_);
    return v___x_4506_;
}
pub unsafe fn l_Lean_Meta_Sym_betaS___boxed(
    mut v_f_4507_: *mut crate::leanh::LeanObject,
    mut v_args_4508_: *mut crate::leanh::LeanObject,
    mut v_a_4509_: *mut crate::leanh::LeanObject,
    mut v_a_4510_: *mut crate::leanh::LeanObject,
    mut v_a_4511_: *mut crate::leanh::LeanObject,
    mut v_a_4512_: *mut crate::leanh::LeanObject,
    mut v_a_4513_: *mut crate::leanh::LeanObject,
    mut v_a_4514_: *mut crate::leanh::LeanObject,
    mut v_a_4515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4516_ = l_Lean_Meta_Sym_betaS(
        v_f_4507_,
        v_args_4508_,
        v_a_4509_,
        v_a_4510_,
        v_a_4511_,
        v_a_4512_,
        v_a_4513_,
        v_a_4514_,
    );
    crate::leanh::lean_dec(v_a_4514_);
    crate::leanh::lean_dec_ref(v_a_4513_);
    crate::leanh::lean_dec(v_a_4512_);
    crate::leanh::lean_dec_ref(v_a_4511_);
    crate::leanh::lean_dec(v_a_4510_);
    crate::leanh::lean_dec_ref(v_a_4509_);
    return v_res_4516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_InstantiateS(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_InstantiateS(
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
pub unsafe fn initialize_Lean_Meta_Sym_InstantiateS(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_InstantiateS(builtin);
}
