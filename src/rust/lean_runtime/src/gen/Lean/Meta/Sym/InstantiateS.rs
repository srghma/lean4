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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 82, 101, 112, 108, 97, 99, 101, 83, 0]};
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_instantiateRevRangeS___closed__3_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 73, 110, 115, 116, 97,
            110, 116, 105, 97, 116, 101, 83, 0,
        ],
    };
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_instantiateRevRangeS___closed__4_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 105, 110, 115, 116, 97,
            110, 116, 105, 97, 116, 101, 82, 101, 118, 82, 97, 110, 103, 101, 83, 0,
        ],
    };
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_instantiateRevRangeS___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value: LeanStringObject<71> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 73, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 82, 97, 110, 103, 101, 83, 39, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 65, 112, 112, 83, 33, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 65, 108, 112, 104, 97, 83, 104, 97, 114, 101, 66, 117, 105, 108, 100, 101, 114, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value: LeanStringObject<86> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 86, m_capacity: 86, m_length: 85, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 73, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 82, 101, 118, 66, 101, 116, 97, 83, 39, 46, 118, 105, 115, 105, 116, 65, 112, 112, 66, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 73, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 83, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 82, 101, 118, 66, 101, 116, 97, 83, 39, 46, 118, 105, 115, 105, 116, 0]};
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    v___x_2259_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2259_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    v___x_2260_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__0);
    v___x_2261_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2261_, 0, v___x_2260_);
    return v___x_2261_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(
    mut v_00_u03b2_2262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    v___x_2263_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0___closed__1);
    return v___x_2263_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(
    mut v_idx_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    v___x_2266_ = l_Lean_Expr_bvar___override(v_idx_2264_);
    v___x_2267_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_2266_, v___y_2265_);
    return v___x_2267_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(
    mut v_idx_2268_: *mut LeanObject,
    mut v___y_2269_: u8,
    mut v___y_2270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    v___x_2271_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v_idx_2268_, v___y_2270_);
    return v___x_2271_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___boxed(
    mut v_idx_2272_: *mut LeanObject,
    mut v___y_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_22951__boxed_2275_: u8 = 0;
    let mut v_res_2276_: *mut LeanObject = core::ptr::null_mut();
    v___y_22951__boxed_2275_ = (lean_unbox(v___y_2273_) as u8);
    v_res_2276_ =
        l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1(
            v_idx_2272_,
            v___y_22951__boxed_2275_,
            v___y_2274_,
        );
    return v_res_2276_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    v___x_2277_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
    return v___x_2277_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(
    mut v_msg_2278_: *mut LeanObject,
    mut v___y_2279_: *mut LeanObject,
    mut v___y_2280_: *mut LeanObject,
    mut v___y_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
    mut v___y_2283_: *mut LeanObject,
    mut v___y_2284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191__overap_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    v___x_2286_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0_once
        ),
        _init_l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___closed__0,
    );
    v___x_3191__overap_2287_ = lean_panic_fn_borrowed(v___x_2286_, v_msg_2278_);
    lean_inc(v___y_2284_);
    lean_inc_ref(v___y_2283_);
    lean_inc(v___y_2282_);
    lean_inc_ref(v___y_2281_);
    lean_inc(v___y_2280_);
    lean_inc_ref(v___y_2279_);
    v___x_2288_ = lean_apply_7(
        v___x_3191__overap_2287_,
        v___y_2279_,
        v___y_2280_,
        v___y_2281_,
        v___y_2282_,
        v___y_2283_,
        v___y_2284_,
        lean_box(0),
    );
    return v___x_2288_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3___boxed(
    mut v_msg_2289_: *mut LeanObject,
    mut v___y_2290_: *mut LeanObject,
    mut v___y_2291_: *mut LeanObject,
    mut v___y_2292_: *mut LeanObject,
    mut v___y_2293_: *mut LeanObject,
    mut v___y_2294_: *mut LeanObject,
    mut v___y_2295_: *mut LeanObject,
    mut v___y_2296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2297_: *mut LeanObject = core::ptr::null_mut();
    v_res_2297_ = l_panic___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__3(
        v_msg_2289_,
        v___y_2290_,
        v___y_2291_,
        v___y_2292_,
        v___y_2293_,
        v___y_2294_,
        v___y_2295_,
    );
    lean_dec(v___y_2295_);
    lean_dec_ref(v___y_2294_);
    lean_dec(v___y_2293_);
    lean_dec_ref(v___y_2292_);
    lean_dec(v___y_2291_);
    lean_dec_ref(v___y_2290_);
    return v_res_2297_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(
    mut v_x_2298_: *mut LeanObject,
    mut v_bi_2299_: u8,
    mut v_t_2300_: *mut LeanObject,
    mut v_b_2301_: *mut LeanObject,
    mut v___y_2302_: *mut LeanObject,
    mut v___y_2303_: u8,
    mut v___y_2304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2323_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_t_2300_);
                    v___x_2320_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_2300_,
                        v___y_2303_,
                        v___y_2304_,
                    );
                    v_snd_2321_ = lean_ctor_get(v___x_2320_, 1);
                    lean_inc(v_snd_2321_);
                    lean_dec_ref(v___x_2320_);
                    lean_inc_ref(v_b_2301_);
                    v___x_2322_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_2301_,
                        v___y_2303_,
                        v_snd_2321_,
                    );
                    v_snd_2323_ = lean_ctor_get(v___x_2322_, 1);
                    lean_inc(v_snd_2323_);
                    lean_dec_ref(v___x_2322_);
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
                v_fst_2310_ = lean_ctor_get(v___x_2309_, 0);
                v_snd_2311_ = lean_ctor_get(v___x_2309_, 1);
                v_isSharedCheck_2319_ = (!lean_is_exclusive(v___x_2309_)) as u8;
                if v_isSharedCheck_2319_ == 0 {
                    v___x_2313_ = v___x_2309_;
                    v_isShared_2314_ = v_isSharedCheck_2319_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2311_);
                    lean_inc(v_fst_2310_);
                    lean_dec(v___x_2309_);
                    v___x_2313_ = lean_box(0);
                    v_isShared_2314_ = v_isSharedCheck_2319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2314_ == 0 {
                    lean_ctor_set(v___x_2313_, 1, v___y_2306_);
                    v___x_2316_ = v___x_2313_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_fst_2310_);
                    lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___y_2306_);
                    v___x_2316_ = v_reuseFailAlloc_2318_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2317_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2317_, 0, v___x_2316_);
                lean_ctor_set(v___x_2317_, 1, v_snd_2311_);
                return v___x_2317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5___boxed(
    mut v_x_2324_: *mut LeanObject,
    mut v_bi_2325_: *mut LeanObject,
    mut v_t_2326_: *mut LeanObject,
    mut v_b_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
    mut v___y_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_2331_: u8 = 0;
    let mut v___y_22988__boxed_2332_: u8 = 0;
    let mut v_res_2333_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_2331_ = (lean_unbox(v_bi_2325_) as u8);
    v___y_22988__boxed_2332_ = (lean_unbox(v___y_2329_) as u8);
    v_res_2333_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_x_2324_, v_bi_boxed_2331_, v_t_2326_, v_b_2327_, v___y_2328_, v___y_22988__boxed_2332_, v___y_2330_);
    return v_res_2333_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(
    mut v_msg_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: u8,
    mut v___y_2344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_22617__overap_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    v___f_2345_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0;
    v___f_2346_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1;
    v___f_2347_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2;
    v___f_2348_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3;
    v___f_2349_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4;
    v___f_2350_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5;
    v___f_2351_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6;
    v___x_2352_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2352_, 0, v___f_2345_);
    lean_ctor_set(v___x_2352_, 1, v___f_2346_);
    v___x_2353_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2353_, 0, v___x_2352_);
    lean_ctor_set(v___x_2353_, 1, v___f_2347_);
    lean_ctor_set(v___x_2353_, 2, v___f_2348_);
    lean_ctor_set(v___x_2353_, 3, v___f_2349_);
    lean_ctor_set(v___x_2353_, 4, v___f_2350_);
    v___x_2354_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2354_, 0, v___x_2353_);
    lean_ctor_set(v___x_2354_, 1, v___f_2351_);
    lean_inc_ref_n(v___x_2354_, 6);
    v___f_2355_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2355_, 0, v___x_2354_);
    v___f_2356_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2356_, 0, v___x_2354_);
    v___f_2357_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2357_, 0, v___x_2354_);
    v___f_2358_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2358_, 0, v___x_2354_);
    v___x_2359_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2359_, 0, lean_box(0));
    lean_closure_set(v___x_2359_, 1, lean_box(0));
    lean_closure_set(v___x_2359_, 2, v___x_2354_);
    v___x_2360_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2360_, 0, v___x_2359_);
    lean_ctor_set(v___x_2360_, 1, v___f_2355_);
    v___x_2361_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_2361_, 0, lean_box(0));
    lean_closure_set(v___x_2361_, 1, lean_box(0));
    lean_closure_set(v___x_2361_, 2, v___x_2354_);
    v___x_2362_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2362_, 0, v___x_2360_);
    lean_ctor_set(v___x_2362_, 1, v___x_2361_);
    lean_ctor_set(v___x_2362_, 2, v___f_2356_);
    lean_ctor_set(v___x_2362_, 3, v___f_2357_);
    lean_ctor_set(v___x_2362_, 4, v___f_2358_);
    v___x_2363_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2363_, 0, lean_box(0));
    lean_closure_set(v___x_2363_, 1, lean_box(0));
    lean_closure_set(v___x_2363_, 2, v___x_2354_);
    v___x_2364_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2364_, 0, v___x_2362_);
    lean_ctor_set(v___x_2364_, 1, v___x_2363_);
    v___x_2365_ = l_ReaderT_instMonad___redArg(v___x_2364_);
    lean_inc_ref_n(v___x_2365_, 6);
    v___f_2366_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2366_, 0, v___x_2365_);
    v___f_2367_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2367_, 0, v___x_2365_);
    v___f_2368_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2368_, 0, v___x_2365_);
    v___f_2369_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2369_, 0, v___x_2365_);
    v___x_2370_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2370_, 0, lean_box(0));
    lean_closure_set(v___x_2370_, 1, lean_box(0));
    lean_closure_set(v___x_2370_, 2, v___x_2365_);
    v___x_2371_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2371_, 0, v___x_2370_);
    lean_ctor_set(v___x_2371_, 1, v___f_2366_);
    v___x_2372_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_2372_, 0, lean_box(0));
    lean_closure_set(v___x_2372_, 1, lean_box(0));
    lean_closure_set(v___x_2372_, 2, v___x_2365_);
    v___x_2373_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2373_, 0, v___x_2371_);
    lean_ctor_set(v___x_2373_, 1, v___x_2372_);
    lean_ctor_set(v___x_2373_, 2, v___f_2367_);
    lean_ctor_set(v___x_2373_, 3, v___f_2368_);
    lean_ctor_set(v___x_2373_, 4, v___f_2369_);
    v___x_2374_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2374_, 0, lean_box(0));
    lean_closure_set(v___x_2374_, 1, lean_box(0));
    lean_closure_set(v___x_2374_, 2, v___x_2365_);
    v___x_2375_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2375_, 0, v___x_2373_);
    lean_ctor_set(v___x_2375_, 1, v___x_2374_);
    v___x_2376_ = l_Lean_instInhabitedExpr;
    v___x_2377_ = l_instInhabitedOfMonad___redArg(v___x_2375_, v___x_2376_);
    v___x_22617__overap_2378_ = lean_panic_fn_borrowed(v___x_2377_, v_msg_2341_);
    lean_dec(v___x_2377_);
    v___x_2379_ = lean_box((v___y_2343_) as usize);
    v___x_2380_ = lean_apply_3(
        v___x_22617__overap_2378_,
        v___y_2342_,
        v___x_2379_,
        v___y_2344_,
    );
    return v___x_2380_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___boxed(
    mut v_msg_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_23051__boxed_2385_: u8 = 0;
    let mut v_res_2386_: *mut LeanObject = core::ptr::null_mut();
    v___y_23051__boxed_2385_ = (lean_unbox(v___y_2383_) as u8);
    v_res_2386_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v_msg_2381_, v___y_2382_, v___y_23051__boxed_2385_, v___y_2384_);
    return v_res_2386_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(
    mut v_structName_2387_: *mut LeanObject,
    mut v_idx_2388_: *mut LeanObject,
    mut v_struct_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
    mut v___y_2391_: u8,
    mut v___y_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2407_: u8 = 0;
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2409_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_struct_2389_);
                    v___x_2408_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_struct_2389_,
                        v___y_2391_,
                        v___y_2392_,
                    );
                    v_snd_2409_ = lean_ctor_get(v___x_2408_, 1);
                    lean_inc(v_snd_2409_);
                    lean_dec_ref(v___x_2408_);
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
                v_fst_2398_ = lean_ctor_get(v___x_2397_, 0);
                v_snd_2399_ = lean_ctor_get(v___x_2397_, 1);
                v_isSharedCheck_2407_ = (!lean_is_exclusive(v___x_2397_)) as u8;
                if v_isSharedCheck_2407_ == 0 {
                    v___x_2401_ = v___x_2397_;
                    v_isShared_2402_ = v_isSharedCheck_2407_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2399_);
                    lean_inc(v_fst_2398_);
                    lean_dec(v___x_2397_);
                    v___x_2401_ = lean_box(0);
                    v_isShared_2402_ = v_isSharedCheck_2407_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2402_ == 0 {
                    lean_ctor_set(v___x_2401_, 1, v___y_2394_);
                    v___x_2404_ = v___x_2401_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_fst_2398_);
                    lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___y_2394_);
                    v___x_2404_ = v_reuseFailAlloc_2406_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2405_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2405_, 0, v___x_2404_);
                lean_ctor_set(v___x_2405_, 1, v_snd_2399_);
                return v___x_2405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8___boxed(
    mut v_structName_2410_: *mut LeanObject,
    mut v_idx_2411_: *mut LeanObject,
    mut v_struct_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_23137__boxed_2416_: u8 = 0;
    let mut v_res_2417_: *mut LeanObject = core::ptr::null_mut();
    v___y_23137__boxed_2416_ = (lean_unbox(v___y_2414_) as u8);
    v_res_2417_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_structName_2410_, v_idx_2411_, v_struct_2412_, v___y_2413_, v___y_23137__boxed_2416_, v___y_2415_);
    return v_res_2417_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(
    mut v_x_2418_: *mut LeanObject,
    mut v_bi_2419_: u8,
    mut v_t_2420_: *mut LeanObject,
    mut v_b_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: u8,
    mut v___y_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2434_: u8 = 0;
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2439_: u8 = 0;
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2443_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_t_2420_);
                    v___x_2440_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_2420_,
                        v___y_2423_,
                        v___y_2424_,
                    );
                    v_snd_2441_ = lean_ctor_get(v___x_2440_, 1);
                    lean_inc(v_snd_2441_);
                    lean_dec_ref(v___x_2440_);
                    lean_inc_ref(v_b_2421_);
                    v___x_2442_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_2421_,
                        v___y_2423_,
                        v_snd_2441_,
                    );
                    v_snd_2443_ = lean_ctor_get(v___x_2442_, 1);
                    lean_inc(v_snd_2443_);
                    lean_dec_ref(v___x_2442_);
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
                v_fst_2430_ = lean_ctor_get(v___x_2429_, 0);
                v_snd_2431_ = lean_ctor_get(v___x_2429_, 1);
                v_isSharedCheck_2439_ = (!lean_is_exclusive(v___x_2429_)) as u8;
                if v_isSharedCheck_2439_ == 0 {
                    v___x_2433_ = v___x_2429_;
                    v_isShared_2434_ = v_isSharedCheck_2439_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2431_);
                    lean_inc(v_fst_2430_);
                    lean_dec(v___x_2429_);
                    v___x_2433_ = lean_box(0);
                    v_isShared_2434_ = v_isSharedCheck_2439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2434_ == 0 {
                    lean_ctor_set(v___x_2433_, 1, v___y_2426_);
                    v___x_2436_ = v___x_2433_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_fst_2430_);
                    lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___y_2426_);
                    v___x_2436_ = v_reuseFailAlloc_2438_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2437_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2437_, 0, v___x_2436_);
                lean_ctor_set(v___x_2437_, 1, v_snd_2431_);
                return v___x_2437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4___boxed(
    mut v_x_2444_: *mut LeanObject,
    mut v_bi_2445_: *mut LeanObject,
    mut v_t_2446_: *mut LeanObject,
    mut v_b_2447_: *mut LeanObject,
    mut v___y_2448_: *mut LeanObject,
    mut v___y_2449_: *mut LeanObject,
    mut v___y_2450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_2451_: u8 = 0;
    let mut v___y_23181__boxed_2452_: u8 = 0;
    let mut v_res_2453_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_2451_ = (lean_unbox(v_bi_2445_) as u8);
    v___y_23181__boxed_2452_ = (lean_unbox(v___y_2449_) as u8);
    v_res_2453_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_x_2444_, v_bi_boxed_2451_, v_t_2446_, v_b_2447_, v___y_2448_, v___y_23181__boxed_2452_, v___y_2450_);
    return v_res_2453_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(
    mut v_d_2454_: *mut LeanObject,
    mut v_e_2455_: *mut LeanObject,
    mut v___y_2456_: *mut LeanObject,
    mut v___y_2457_: u8,
    mut v___y_2458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2468_: u8 = 0;
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2475_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_e_2455_);
                    v___x_2474_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_e_2455_,
                        v___y_2457_,
                        v___y_2458_,
                    );
                    v_snd_2475_ = lean_ctor_get(v___x_2474_, 1);
                    lean_inc(v_snd_2475_);
                    lean_dec_ref(v___x_2474_);
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
                v_fst_2464_ = lean_ctor_get(v___x_2463_, 0);
                v_snd_2465_ = lean_ctor_get(v___x_2463_, 1);
                v_isSharedCheck_2473_ = (!lean_is_exclusive(v___x_2463_)) as u8;
                if v_isSharedCheck_2473_ == 0 {
                    v___x_2467_ = v___x_2463_;
                    v_isShared_2468_ = v_isSharedCheck_2473_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2465_);
                    lean_inc(v_fst_2464_);
                    lean_dec(v___x_2463_);
                    v___x_2467_ = lean_box(0);
                    v_isShared_2468_ = v_isSharedCheck_2473_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2468_ == 0 {
                    lean_ctor_set(v___x_2467_, 1, v___y_2460_);
                    v___x_2470_ = v___x_2467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_fst_2464_);
                    lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___y_2460_);
                    v___x_2470_ = v_reuseFailAlloc_2472_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2471_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2471_, 0, v___x_2470_);
                lean_ctor_set(v___x_2471_, 1, v_snd_2465_);
                return v___x_2471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7___boxed(
    mut v_d_2476_: *mut LeanObject,
    mut v_e_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_23230__boxed_2481_: u8 = 0;
    let mut v_res_2482_: *mut LeanObject = core::ptr::null_mut();
    v___y_23230__boxed_2481_ = (lean_unbox(v___y_2479_) as u8);
    v_res_2482_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_d_2476_, v_e_2477_, v___y_2478_, v___y_23230__boxed_2481_, v___y_2480_);
    return v_res_2482_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(
    mut v_a_2483_: *mut LeanObject,
    mut v_x_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2490_: u8 = 0;
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: u8 = 0;
    let mut v___x_2498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2484_) == 0 {
                    v___x_2485_ = lean_box(0);
                    return v___x_2485_;
                } else {
                    v_key_2486_ = lean_ctor_get(v_x_2484_, 0);
                    v_value_2487_ = lean_ctor_get(v_x_2484_, 1);
                    v_tail_2488_ = lean_ctor_get(v_x_2484_, 2);
                    v_fst_2493_ = lean_ctor_get(v_key_2486_, 0);
                    v_snd_2494_ = lean_ctor_get(v_key_2486_, 1);
                    v_fst_2495_ = lean_ctor_get(v_a_2483_, 0);
                    v_snd_2496_ = lean_ctor_get(v_a_2483_, 1);
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
                    lean_inc(v_value_2487_);
                    v___x_2492_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2492_, 0, v_value_2487_);
                    return v___x_2492_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg___boxed(
    mut v_a_2499_: *mut LeanObject,
    mut v_x_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2501_: *mut LeanObject = core::ptr::null_mut();
    v_res_2501_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_2499_, v_x_2500_);
    lean_dec(v_x_2500_);
    lean_dec_ref(v_a_2499_);
    return v_res_2501_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(
    mut v_m_2502_: *mut LeanObject,
    mut v_a_2503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2504_ = lean_ctor_get(v_m_2502_, 1);
    v_fst_2505_ = lean_ctor_get(v_a_2503_, 0);
    v_snd_2506_ = lean_ctor_get(v_a_2503_, 1);
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
    mut v_m_2524_: *mut LeanObject,
    mut v_a_2525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2526_: *mut LeanObject = core::ptr::null_mut();
    v_res_2526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_2524_, v_a_2525_);
    lean_dec_ref(v_a_2525_);
    lean_dec_ref(v_m_2524_);
    return v_res_2526_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(
    mut v_f_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
    mut v___y_2530_: u8,
    mut v___y_2531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2550_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_f_2527_);
                    v___x_2547_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_f_2527_,
                        v___y_2530_,
                        v___y_2531_,
                    );
                    v_snd_2548_ = lean_ctor_get(v___x_2547_, 1);
                    lean_inc(v_snd_2548_);
                    lean_dec_ref(v___x_2547_);
                    lean_inc_ref(v_a_2528_);
                    v___x_2549_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_a_2528_,
                        v___y_2530_,
                        v_snd_2548_,
                    );
                    v_snd_2550_ = lean_ctor_get(v___x_2549_, 1);
                    lean_inc(v_snd_2550_);
                    lean_dec_ref(v___x_2549_);
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
                v_fst_2537_ = lean_ctor_get(v___x_2536_, 0);
                v_snd_2538_ = lean_ctor_get(v___x_2536_, 1);
                v_isSharedCheck_2546_ = (!lean_is_exclusive(v___x_2536_)) as u8;
                if v_isSharedCheck_2546_ == 0 {
                    v___x_2540_ = v___x_2536_;
                    v_isShared_2541_ = v_isSharedCheck_2546_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2538_);
                    lean_inc(v_fst_2537_);
                    lean_dec(v___x_2536_);
                    v___x_2540_ = lean_box(0);
                    v_isShared_2541_ = v_isSharedCheck_2546_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2541_ == 0 {
                    lean_ctor_set(v___x_2540_, 1, v___y_2533_);
                    v___x_2543_ = v___x_2540_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_fst_2537_);
                    lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___y_2533_);
                    v___x_2543_ = v_reuseFailAlloc_2545_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2544_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2544_, 0, v___x_2543_);
                lean_ctor_set(v___x_2544_, 1, v_snd_2538_);
                return v___x_2544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3___boxed(
    mut v_f_2551_: *mut LeanObject,
    mut v_a_2552_: *mut LeanObject,
    mut v___y_2553_: *mut LeanObject,
    mut v___y_2554_: *mut LeanObject,
    mut v___y_2555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_23343__boxed_2556_: u8 = 0;
    let mut v_res_2557_: *mut LeanObject = core::ptr::null_mut();
    v___y_23343__boxed_2556_ = (lean_unbox(v___y_2554_) as u8);
    v_res_2557_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_f_2551_, v_a_2552_, v___y_2553_, v___y_23343__boxed_2556_, v___y_2555_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(
    mut v_x_2558_: *mut LeanObject,
    mut v_t_2559_: *mut LeanObject,
    mut v_v_2560_: *mut LeanObject,
    mut v_b_2561_: *mut LeanObject,
    mut v_nondep_2562_: u8,
    mut v___y_2563_: *mut LeanObject,
    mut v___y_2564_: u8,
    mut v___y_2565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2580_: u8 = 0;
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2586_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_t_2559_);
                    v___x_2581_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_t_2559_,
                        v___y_2564_,
                        v___y_2565_,
                    );
                    v_snd_2582_ = lean_ctor_get(v___x_2581_, 1);
                    lean_inc(v_snd_2582_);
                    lean_dec_ref(v___x_2581_);
                    lean_inc_ref(v_v_2560_);
                    v___x_2583_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_v_2560_,
                        v___y_2564_,
                        v_snd_2582_,
                    );
                    v_snd_2584_ = lean_ctor_get(v___x_2583_, 1);
                    lean_inc(v_snd_2584_);
                    lean_dec_ref(v___x_2583_);
                    lean_inc_ref(v_b_2561_);
                    v___x_2585_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_b_2561_,
                        v___y_2564_,
                        v_snd_2584_,
                    );
                    v_snd_2586_ = lean_ctor_get(v___x_2585_, 1);
                    lean_inc(v_snd_2586_);
                    lean_dec_ref(v___x_2585_);
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
                v_fst_2571_ = lean_ctor_get(v___x_2570_, 0);
                v_snd_2572_ = lean_ctor_get(v___x_2570_, 1);
                v_isSharedCheck_2580_ = (!lean_is_exclusive(v___x_2570_)) as u8;
                if v_isSharedCheck_2580_ == 0 {
                    v___x_2574_ = v___x_2570_;
                    v_isShared_2575_ = v_isSharedCheck_2580_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2572_);
                    lean_inc(v_fst_2571_);
                    lean_dec(v___x_2570_);
                    v___x_2574_ = lean_box(0);
                    v_isShared_2575_ = v_isSharedCheck_2580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2575_ == 0 {
                    lean_ctor_set(v___x_2574_, 1, v___y_2567_);
                    v___x_2577_ = v___x_2574_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_fst_2571_);
                    lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___y_2567_);
                    v___x_2577_ = v_reuseFailAlloc_2579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2578_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2578_, 0, v___x_2577_);
                lean_ctor_set(v___x_2578_, 1, v_snd_2572_);
                return v___x_2578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6___boxed(
    mut v_x_2587_: *mut LeanObject,
    mut v_t_2588_: *mut LeanObject,
    mut v_v_2589_: *mut LeanObject,
    mut v_b_2590_: *mut LeanObject,
    mut v_nondep_2591_: *mut LeanObject,
    mut v___y_2592_: *mut LeanObject,
    mut v___y_2593_: *mut LeanObject,
    mut v___y_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_2595_: u8 = 0;
    let mut v___y_23392__boxed_2596_: u8 = 0;
    let mut v_res_2597_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_2595_ = (lean_unbox(v_nondep_2591_) as u8);
    v___y_23392__boxed_2596_ = (lean_unbox(v___y_2593_) as u8);
    v_res_2597_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_x_2587_, v_t_2588_, v_v_2589_, v_b_2590_, v_nondep_boxed_2595_, v___y_2592_, v___y_23392__boxed_2596_, v___y_2594_);
    return v_res_2597_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    v___x_2601_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_2602_ = lean_unsigned_to_nat(67);
    v___x_2603_ = lean_unsigned_to_nat(35);
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
    mut v_beginIdx_2607_: *mut LeanObject,
    mut v_n_2608_: *mut LeanObject,
    mut v_subst_2609_: *mut LeanObject,
    mut v_e_2610_: *mut LeanObject,
    mut v_offset_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: u8,
    mut v_a_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2627_: u8 = 0;
    let mut v_fst_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2632_: u8 = 0;
    let mut v___y_2634_: u8 = 0;
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: u8 = 0;
    let mut v___x_2643_: u8 = 0;
    let mut v_isSharedCheck_2644_: u8 = 0;
    let mut v_isSharedCheck_2645_: u8 = 0;
    let mut v_binderName_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2649_: u8 = 0;
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v_fst_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2667_: u8 = 0;
    let mut v___y_2669_: u8 = 0;
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: u8 = 0;
    let mut v___x_2678_: u8 = 0;
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v_isSharedCheck_2680_: u8 = 0;
    let mut v_binderName_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2684_: u8 = 0;
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v_fst_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2702_: u8 = 0;
    let mut v___y_2704_: u8 = 0;
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    let mut v___x_2713_: u8 = 0;
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_isSharedCheck_2715_: u8 = 0;
    let mut v_declName_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_2720_: u8 = 0;
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2738_: u8 = 0;
    let mut v_fst_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2743_: u8 = 0;
    let mut v___y_2745_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: u8 = 0;
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___x_2756_: u8 = 0;
    let mut v_isSharedCheck_2757_: u8 = 0;
    let mut v_isSharedCheck_2758_: u8 = 0;
    let mut v_data_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v_fst_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2780_: u8 = 0;
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v_typeName_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2790_: u8 = 0;
    let mut v_fst_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_2610_) {
                5 => {
                    v_fn_2615_ = lean_ctor_get(v_e_2610_, 0);
                    v_arg_2616_ = lean_ctor_get(v_e_2610_, 1);
                    lean_inc(v_offset_2611_);
                    lean_inc_ref(v_fn_2615_);
                    v___x_2617_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_fn_2615_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2618_ = lean_ctor_get(v___x_2617_, 0);
                    lean_inc(v_fst_2618_);
                    v_snd_2619_ = lean_ctor_get(v___x_2617_, 1);
                    lean_inc(v_snd_2619_);
                    lean_dec_ref(v___x_2617_);
                    v_fst_2620_ = lean_ctor_get(v_fst_2618_, 0);
                    lean_inc(v_fst_2620_);
                    v_snd_2621_ = lean_ctor_get(v_fst_2618_, 1);
                    lean_inc(v_snd_2621_);
                    lean_dec(v_fst_2618_);
                    lean_inc_ref(v_arg_2616_);
                    v___x_2622_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_arg_2616_, v_offset_2611_, v_snd_2621_, v_a_2613_, v_snd_2619_);
                    v_fst_2623_ = lean_ctor_get(v___x_2622_, 0);
                    v_snd_2624_ = lean_ctor_get(v___x_2622_, 1);
                    v_isSharedCheck_2645_ = (!lean_is_exclusive(v___x_2622_)) as u8;
                    if v_isSharedCheck_2645_ == 0 {
                        v___x_2626_ = v___x_2622_;
                        v_isShared_2627_ = v_isSharedCheck_2645_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2624_);
                        lean_inc(v_fst_2623_);
                        lean_dec(v___x_2622_);
                        v___x_2626_ = lean_box(0);
                        v_isShared_2627_ = v_isSharedCheck_2645_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_2646_ = lean_ctor_get(v_e_2610_, 0);
                    v_binderType_2647_ = lean_ctor_get(v_e_2610_, 1);
                    v_body_2648_ = lean_ctor_get(v_e_2610_, 2);
                    v_binderInfo_2649_ = lean_ctor_get_uint8(
                        v_e_2610_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_2611_);
                    lean_inc_ref(v_binderType_2647_);
                    v___x_2650_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_binderType_2647_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2651_ = lean_ctor_get(v___x_2650_, 0);
                    lean_inc(v_fst_2651_);
                    v_snd_2652_ = lean_ctor_get(v___x_2650_, 1);
                    lean_inc(v_snd_2652_);
                    lean_dec_ref(v___x_2650_);
                    v_fst_2653_ = lean_ctor_get(v_fst_2651_, 0);
                    lean_inc(v_fst_2653_);
                    v_snd_2654_ = lean_ctor_get(v_fst_2651_, 1);
                    lean_inc(v_snd_2654_);
                    lean_dec(v_fst_2651_);
                    v___x_2655_ = lean_unsigned_to_nat(1);
                    v___x_2656_ = lean_nat_add(v_offset_2611_, v___x_2655_);
                    lean_dec(v_offset_2611_);
                    lean_inc_ref(v_body_2648_);
                    v___x_2657_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_body_2648_, v___x_2656_, v_snd_2654_, v_a_2613_, v_snd_2652_);
                    v_fst_2658_ = lean_ctor_get(v___x_2657_, 0);
                    v_snd_2659_ = lean_ctor_get(v___x_2657_, 1);
                    v_isSharedCheck_2680_ = (!lean_is_exclusive(v___x_2657_)) as u8;
                    if v_isSharedCheck_2680_ == 0 {
                        v___x_2661_ = v___x_2657_;
                        v_isShared_2662_ = v_isSharedCheck_2680_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_2659_);
                        lean_inc(v_fst_2658_);
                        lean_dec(v___x_2657_);
                        v___x_2661_ = lean_box(0);
                        v_isShared_2662_ = v_isSharedCheck_2680_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_2681_ = lean_ctor_get(v_e_2610_, 0);
                    v_binderType_2682_ = lean_ctor_get(v_e_2610_, 1);
                    v_body_2683_ = lean_ctor_get(v_e_2610_, 2);
                    v_binderInfo_2684_ = lean_ctor_get_uint8(
                        v_e_2610_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_2611_);
                    lean_inc_ref(v_binderType_2682_);
                    v___x_2685_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_binderType_2682_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2686_ = lean_ctor_get(v___x_2685_, 0);
                    lean_inc(v_fst_2686_);
                    v_snd_2687_ = lean_ctor_get(v___x_2685_, 1);
                    lean_inc(v_snd_2687_);
                    lean_dec_ref(v___x_2685_);
                    v_fst_2688_ = lean_ctor_get(v_fst_2686_, 0);
                    lean_inc(v_fst_2688_);
                    v_snd_2689_ = lean_ctor_get(v_fst_2686_, 1);
                    lean_inc(v_snd_2689_);
                    lean_dec(v_fst_2686_);
                    v___x_2690_ = lean_unsigned_to_nat(1);
                    v___x_2691_ = lean_nat_add(v_offset_2611_, v___x_2690_);
                    lean_dec(v_offset_2611_);
                    lean_inc_ref(v_body_2683_);
                    v___x_2692_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_body_2683_, v___x_2691_, v_snd_2689_, v_a_2613_, v_snd_2687_);
                    v_fst_2693_ = lean_ctor_get(v___x_2692_, 0);
                    v_snd_2694_ = lean_ctor_get(v___x_2692_, 1);
                    v_isSharedCheck_2715_ = (!lean_is_exclusive(v___x_2692_)) as u8;
                    if v_isSharedCheck_2715_ == 0 {
                        v___x_2696_ = v___x_2692_;
                        v_isShared_2697_ = v_isSharedCheck_2715_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_snd_2694_);
                        lean_inc(v_fst_2693_);
                        lean_dec(v___x_2692_);
                        v___x_2696_ = lean_box(0);
                        v_isShared_2697_ = v_isSharedCheck_2715_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_2716_ = lean_ctor_get(v_e_2610_, 0);
                    v_type_2717_ = lean_ctor_get(v_e_2610_, 1);
                    v_value_2718_ = lean_ctor_get(v_e_2610_, 2);
                    v_body_2719_ = lean_ctor_get(v_e_2610_, 3);
                    v_nondep_2720_ = lean_ctor_get_uint8(
                        v_e_2610_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_inc_n(v_offset_2611_, 2);
                    lean_inc_ref(v_type_2717_);
                    v___x_2721_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_type_2717_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2722_ = lean_ctor_get(v___x_2721_, 0);
                    lean_inc(v_fst_2722_);
                    v_snd_2723_ = lean_ctor_get(v___x_2721_, 1);
                    lean_inc(v_snd_2723_);
                    lean_dec_ref(v___x_2721_);
                    v_fst_2724_ = lean_ctor_get(v_fst_2722_, 0);
                    lean_inc(v_fst_2724_);
                    v_snd_2725_ = lean_ctor_get(v_fst_2722_, 1);
                    lean_inc(v_snd_2725_);
                    lean_dec(v_fst_2722_);
                    lean_inc_ref(v_value_2718_);
                    v___x_2726_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_value_2718_, v_offset_2611_, v_snd_2725_, v_a_2613_, v_snd_2723_);
                    v_fst_2727_ = lean_ctor_get(v___x_2726_, 0);
                    lean_inc(v_fst_2727_);
                    v_snd_2728_ = lean_ctor_get(v___x_2726_, 1);
                    lean_inc(v_snd_2728_);
                    lean_dec_ref(v___x_2726_);
                    v_fst_2729_ = lean_ctor_get(v_fst_2727_, 0);
                    lean_inc(v_fst_2729_);
                    v_snd_2730_ = lean_ctor_get(v_fst_2727_, 1);
                    lean_inc(v_snd_2730_);
                    lean_dec(v_fst_2727_);
                    v___x_2731_ = lean_unsigned_to_nat(1);
                    v___x_2732_ = lean_nat_add(v_offset_2611_, v___x_2731_);
                    lean_dec(v_offset_2611_);
                    lean_inc_ref(v_body_2719_);
                    v___x_2733_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_body_2719_, v___x_2732_, v_snd_2730_, v_a_2613_, v_snd_2728_);
                    v_fst_2734_ = lean_ctor_get(v___x_2733_, 0);
                    v_snd_2735_ = lean_ctor_get(v___x_2733_, 1);
                    v_isSharedCheck_2758_ = (!lean_is_exclusive(v___x_2733_)) as u8;
                    if v_isSharedCheck_2758_ == 0 {
                        v___x_2737_ = v___x_2733_;
                        v_isShared_2738_ = v_isSharedCheck_2758_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_snd_2735_);
                        lean_inc(v_fst_2734_);
                        lean_dec(v___x_2733_);
                        v___x_2737_ = lean_box(0);
                        v_isShared_2738_ = v_isSharedCheck_2758_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_2759_ = lean_ctor_get(v_e_2610_, 0);
                    v_expr_2760_ = lean_ctor_get(v_e_2610_, 1);
                    lean_inc_ref(v_expr_2760_);
                    v___x_2761_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_expr_2760_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2762_ = lean_ctor_get(v___x_2761_, 0);
                    v_snd_2763_ = lean_ctor_get(v___x_2761_, 1);
                    v_isSharedCheck_2781_ = (!lean_is_exclusive(v___x_2761_)) as u8;
                    if v_isSharedCheck_2781_ == 0 {
                        v___x_2765_ = v___x_2761_;
                        v_isShared_2766_ = v_isSharedCheck_2781_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_snd_2763_);
                        lean_inc(v_fst_2762_);
                        lean_dec(v___x_2761_);
                        v___x_2765_ = lean_box(0);
                        v_isShared_2766_ = v_isSharedCheck_2781_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_2782_ = lean_ctor_get(v_e_2610_, 0);
                    v_idx_2783_ = lean_ctor_get(v_e_2610_, 1);
                    v_struct_2784_ = lean_ctor_get(v_e_2610_, 2);
                    lean_inc_ref(v_struct_2784_);
                    v___x_2785_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2607_, v_n_2608_, v_subst_2609_, v_struct_2784_, v_offset_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
                    v_fst_2786_ = lean_ctor_get(v___x_2785_, 0);
                    v_snd_2787_ = lean_ctor_get(v___x_2785_, 1);
                    v_isSharedCheck_2805_ = (!lean_is_exclusive(v___x_2785_)) as u8;
                    if v_isSharedCheck_2805_ == 0 {
                        v___x_2789_ = v___x_2785_;
                        v_isShared_2790_ = v_isSharedCheck_2805_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_snd_2787_);
                        lean_inc(v_fst_2786_);
                        lean_dec(v___x_2785_);
                        v___x_2789_ = lean_box(0);
                        v_isShared_2790_ = v_isSharedCheck_2805_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_offset_2611_);
                    lean_dec_ref(v_e_2610_);
                    v___x_2806_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
                    v___x_2807_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_2806_, v_a_2612_, v_a_2613_, v_a_2614_);
                    return v___x_2807_;
                }
            },
            1 => {
                v_fst_2628_ = lean_ctor_get(v_fst_2623_, 0);
                v_snd_2629_ = lean_ctor_get(v_fst_2623_, 1);
                v_isSharedCheck_2644_ = (!lean_is_exclusive(v_fst_2623_)) as u8;
                if v_isSharedCheck_2644_ == 0 {
                    v___x_2631_ = v_fst_2623_;
                    v_isShared_2632_ = v_isSharedCheck_2644_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2629_);
                    lean_inc(v_fst_2628_);
                    lean_dec(v_fst_2623_);
                    v___x_2631_ = lean_box(0);
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
                    lean_del_object(v___x_2631_);
                    lean_del_object(v___x_2626_);
                    lean_dec_ref_known(v_e_2610_, 2);
                    v___x_2635_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_2620_, v_fst_2628_, v_snd_2629_, v_a_2613_, v_snd_2624_);
                    return v___x_2635_;
                } else {
                    lean_dec(v_fst_2628_);
                    lean_dec(v_fst_2620_);
                    if v_isShared_2632_ == 0 {
                        lean_ctor_set(v___x_2631_, 0, v_e_2610_);
                        v___x_2637_ = v___x_2631_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_e_2610_);
                        lean_ctor_set(v_reuseFailAlloc_2641_, 1, v_snd_2629_);
                        v___x_2637_ = v_reuseFailAlloc_2641_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2627_ == 0 {
                    lean_ctor_set(v___x_2626_, 0, v___x_2637_);
                    v___x_2639_ = v___x_2626_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2637_);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_snd_2624_);
                    v___x_2639_ = v_reuseFailAlloc_2640_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2639_;
            }
            6 => {
                v_fst_2663_ = lean_ctor_get(v_fst_2658_, 0);
                v_snd_2664_ = lean_ctor_get(v_fst_2658_, 1);
                v_isSharedCheck_2679_ = (!lean_is_exclusive(v_fst_2658_)) as u8;
                if v_isSharedCheck_2679_ == 0 {
                    v___x_2666_ = v_fst_2658_;
                    v_isShared_2667_ = v_isSharedCheck_2679_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_2664_);
                    lean_inc(v_fst_2663_);
                    lean_dec(v_fst_2658_);
                    v___x_2666_ = lean_box(0);
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
                    lean_inc(v_binderName_2646_);
                    lean_del_object(v___x_2666_);
                    lean_del_object(v___x_2661_);
                    lean_dec_ref_known(v_e_2610_, 3);
                    v___x_2670_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_2646_, v_binderInfo_2649_, v_fst_2653_, v_fst_2663_, v_snd_2664_, v_a_2613_, v_snd_2659_);
                    return v___x_2670_;
                } else {
                    lean_dec(v_fst_2663_);
                    lean_dec(v_fst_2653_);
                    if v_isShared_2667_ == 0 {
                        lean_ctor_set(v___x_2666_, 0, v_e_2610_);
                        v___x_2672_ = v___x_2666_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_e_2610_);
                        lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_snd_2664_);
                        v___x_2672_ = v_reuseFailAlloc_2676_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2662_ == 0 {
                    lean_ctor_set(v___x_2661_, 0, v___x_2672_);
                    v___x_2674_ = v___x_2661_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
                    lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_snd_2659_);
                    v___x_2674_ = v_reuseFailAlloc_2675_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2674_;
            }
            11 => {
                v_fst_2698_ = lean_ctor_get(v_fst_2693_, 0);
                v_snd_2699_ = lean_ctor_get(v_fst_2693_, 1);
                v_isSharedCheck_2714_ = (!lean_is_exclusive(v_fst_2693_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v___x_2701_ = v_fst_2693_;
                    v_isShared_2702_ = v_isSharedCheck_2714_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_snd_2699_);
                    lean_inc(v_fst_2698_);
                    lean_dec(v_fst_2693_);
                    v___x_2701_ = lean_box(0);
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
                    lean_inc(v_binderName_2681_);
                    lean_del_object(v___x_2701_);
                    lean_del_object(v___x_2696_);
                    lean_dec_ref_known(v_e_2610_, 3);
                    v___x_2705_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_2681_, v_binderInfo_2684_, v_fst_2688_, v_fst_2698_, v_snd_2699_, v_a_2613_, v_snd_2694_);
                    return v___x_2705_;
                } else {
                    lean_dec(v_fst_2698_);
                    lean_dec(v_fst_2688_);
                    if v_isShared_2702_ == 0 {
                        lean_ctor_set(v___x_2701_, 0, v_e_2610_);
                        v___x_2707_ = v___x_2701_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_e_2610_);
                        lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_snd_2699_);
                        v___x_2707_ = v_reuseFailAlloc_2711_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2697_ == 0 {
                    lean_ctor_set(v___x_2696_, 0, v___x_2707_);
                    v___x_2709_ = v___x_2696_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
                    lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_snd_2694_);
                    v___x_2709_ = v_reuseFailAlloc_2710_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2709_;
            }
            16 => {
                v_fst_2739_ = lean_ctor_get(v_fst_2734_, 0);
                v_snd_2740_ = lean_ctor_get(v_fst_2734_, 1);
                v_isSharedCheck_2757_ = (!lean_is_exclusive(v_fst_2734_)) as u8;
                if v_isSharedCheck_2757_ == 0 {
                    v___x_2742_ = v_fst_2734_;
                    v_isShared_2743_ = v_isSharedCheck_2757_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_snd_2740_);
                    lean_inc(v_fst_2739_);
                    lean_dec(v_fst_2734_);
                    v___x_2742_ = lean_box(0);
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
                    lean_inc(v_declName_2716_);
                    lean_del_object(v___x_2742_);
                    lean_del_object(v___x_2737_);
                    lean_dec_ref_known(v_e_2610_, 4);
                    v___x_2746_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_2716_, v_fst_2724_, v_fst_2729_, v_fst_2739_, v_nondep_2720_, v_snd_2740_, v_a_2613_, v_snd_2735_);
                    return v___x_2746_;
                } else {
                    v___x_2747_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_2719_,
                            v_fst_2739_,
                        );
                    if v___x_2747_ == 0 {
                        lean_inc(v_declName_2716_);
                        lean_del_object(v___x_2742_);
                        lean_del_object(v___x_2737_);
                        lean_dec_ref_known(v_e_2610_, 4);
                        v___x_2748_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_2716_, v_fst_2724_, v_fst_2729_, v_fst_2739_, v_nondep_2720_, v_snd_2740_, v_a_2613_, v_snd_2735_);
                        return v___x_2748_;
                    } else {
                        lean_dec(v_fst_2739_);
                        lean_dec(v_fst_2729_);
                        lean_dec(v_fst_2724_);
                        if v_isShared_2743_ == 0 {
                            lean_ctor_set(v___x_2742_, 0, v_e_2610_);
                            v___x_2750_ = v___x_2742_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2754_, 0, v_e_2610_);
                            lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_snd_2740_);
                            v___x_2750_ = v_reuseFailAlloc_2754_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_2738_ == 0 {
                    lean_ctor_set(v___x_2737_, 0, v___x_2750_);
                    v___x_2752_ = v___x_2737_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2750_);
                    lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_snd_2735_);
                    v___x_2752_ = v_reuseFailAlloc_2753_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2752_;
            }
            21 => {
                v_fst_2767_ = lean_ctor_get(v_fst_2762_, 0);
                v_snd_2768_ = lean_ctor_get(v_fst_2762_, 1);
                v_isSharedCheck_2780_ = (!lean_is_exclusive(v_fst_2762_)) as u8;
                if v_isSharedCheck_2780_ == 0 {
                    v___x_2770_ = v_fst_2762_;
                    v_isShared_2771_ = v_isSharedCheck_2780_;
                    state = 22;
                    continue;
                } else {
                    lean_inc(v_snd_2768_);
                    lean_inc(v_fst_2767_);
                    lean_dec(v_fst_2762_);
                    v___x_2770_ = lean_box(0);
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
                    lean_inc(v_data_2759_);
                    lean_del_object(v___x_2770_);
                    lean_del_object(v___x_2765_);
                    lean_dec_ref_known(v_e_2610_, 2);
                    v___x_2773_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_2759_, v_fst_2767_, v_snd_2768_, v_a_2613_, v_snd_2763_);
                    return v___x_2773_;
                } else {
                    lean_dec(v_fst_2767_);
                    if v_isShared_2771_ == 0 {
                        lean_ctor_set(v___x_2770_, 0, v_e_2610_);
                        v___x_2775_ = v___x_2770_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_e_2610_);
                        lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_snd_2768_);
                        v___x_2775_ = v_reuseFailAlloc_2779_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_2766_ == 0 {
                    lean_ctor_set(v___x_2765_, 0, v___x_2775_);
                    v___x_2777_ = v___x_2765_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_snd_2763_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2777_;
            }
            25 => {
                v_fst_2791_ = lean_ctor_get(v_fst_2786_, 0);
                v_snd_2792_ = lean_ctor_get(v_fst_2786_, 1);
                v_isSharedCheck_2804_ = (!lean_is_exclusive(v_fst_2786_)) as u8;
                if v_isSharedCheck_2804_ == 0 {
                    v___x_2794_ = v_fst_2786_;
                    v_isShared_2795_ = v_isSharedCheck_2804_;
                    state = 26;
                    continue;
                } else {
                    lean_inc(v_snd_2792_);
                    lean_inc(v_fst_2791_);
                    lean_dec(v_fst_2786_);
                    v___x_2794_ = lean_box(0);
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
                    lean_inc(v_idx_2783_);
                    lean_inc(v_typeName_2782_);
                    lean_del_object(v___x_2794_);
                    lean_del_object(v___x_2789_);
                    lean_dec_ref_known(v_e_2610_, 3);
                    v___x_2797_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_2782_, v_idx_2783_, v_fst_2791_, v_snd_2792_, v_a_2613_, v_snd_2787_);
                    return v___x_2797_;
                } else {
                    lean_dec(v_fst_2791_);
                    if v_isShared_2795_ == 0 {
                        lean_ctor_set(v___x_2794_, 0, v_e_2610_);
                        v___x_2799_ = v___x_2794_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_e_2610_);
                        lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_snd_2792_);
                        v___x_2799_ = v_reuseFailAlloc_2803_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2790_ == 0 {
                    lean_ctor_set(v___x_2789_, 0, v___x_2799_);
                    v___x_2801_ = v___x_2789_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
                    lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_snd_2787_);
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
    mut v_beginIdx_2808_: *mut LeanObject,
    mut v_n_2809_: *mut LeanObject,
    mut v_subst_2810_: *mut LeanObject,
    mut v_e_2811_: *mut LeanObject,
    mut v_offset_2812_: *mut LeanObject,
    mut v_a_2813_: *mut LeanObject,
    mut v_a_2814_: u8,
    mut v_a_2815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_offset_2812_);
    lean_inc_ref(v_e_2811_);
    v_key_2816_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_key_2816_, 0, v_e_2811_);
    lean_ctor_set(v_key_2816_, 1, v_offset_2812_);
    v___x_2817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_2813_, v_key_2816_);
    if lean_obj_tag(v___x_2817_) == 1 {
        let mut v_val_2818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_key_2816_, 2);
        lean_dec(v_offset_2812_);
        lean_dec_ref(v_e_2811_);
        v_val_2818_ = lean_ctor_get(v___x_2817_, 0);
        lean_inc(v_val_2818_);
        lean_dec_ref_known(v___x_2817_, 1);
        v___x_2819_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2819_, 0, v_val_2818_);
        lean_ctor_set(v___x_2819_, 1, v_a_2813_);
        v___x_2820_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2820_, 0, v___x_2819_);
        lean_ctor_set(v___x_2820_, 1, v_a_2815_);
        return v___x_2820_;
    } else {
        let mut v_s_u2081_2821_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2817_);
        v_s_u2081_2821_ = lean_nat_add(v_beginIdx_2808_, v_offset_2812_);
        match lean_obj_tag(v_e_2811_) {
            0 => {
                let mut v_deBruijnIndex_2822_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2823_: u8 = 0;
                v_deBruijnIndex_2822_ = lean_ctor_get(v_e_2811_, 0);
                v___x_2823_ = lean_nat_dec_le(v_s_u2081_2821_, v_deBruijnIndex_2822_);
                lean_dec(v_s_u2081_2821_);
                if v___x_2823_ == 0 {
                    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_offset_2812_);
                    v___x_2824_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_2816_,
                        v_e_2811_,
                        v_a_2813_,
                        v_a_2814_,
                        v_a_2815_,
                    );
                    return v___x_2824_;
                } else {
                    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2826_: u8 = 0;
                    lean_inc(v_deBruijnIndex_2822_);
                    lean_dec_ref_known(v_e_2811_, 1);
                    v___x_2825_ = lean_nat_add(v_offset_2812_, v_n_2809_);
                    v___x_2826_ = lean_nat_dec_lt(v_deBruijnIndex_2822_, v___x_2825_);
                    lean_dec(v___x_2825_);
                    if v___x_2826_ == 0 {
                        let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_fst_2829_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_snd_2830_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v_offset_2812_);
                        v___x_2827_ = lean_nat_sub(v_deBruijnIndex_2822_, v_n_2809_);
                        lean_dec(v_deBruijnIndex_2822_);
                        v___x_2828_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_2827_, v_a_2815_);
                        v_fst_2829_ = lean_ctor_get(v___x_2828_, 0);
                        lean_inc(v_fst_2829_);
                        v_snd_2830_ = lean_ctor_get(v___x_2828_, 1);
                        lean_inc(v_snd_2830_);
                        lean_dec_ref(v___x_2828_);
                        v___x_2831_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                            v_key_2816_,
                            v_fst_2829_,
                            v_a_2813_,
                            v_a_2814_,
                            v_snd_2830_,
                        );
                        return v___x_2831_;
                    } else {
                        let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_v_2836_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_fst_2839_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_snd_2840_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2832_ = lean_nat_sub(v_deBruijnIndex_2822_, v_offset_2812_);
                        lean_dec(v_deBruijnIndex_2822_);
                        v___x_2833_ = lean_nat_sub(v_n_2809_, v___x_2832_);
                        lean_dec(v___x_2832_);
                        v___x_2834_ = lean_unsigned_to_nat(1);
                        v___x_2835_ = lean_nat_sub(v___x_2833_, v___x_2834_);
                        lean_dec(v___x_2833_);
                        v_v_2836_ = lean_array_fget_borrowed(v_subst_2810_, v___x_2835_);
                        lean_dec(v___x_2835_);
                        v___x_2837_ = lean_unsigned_to_nat(0);
                        lean_inc(v_v_2836_);
                        v___x_2838_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                            v_v_2836_,
                            v___x_2837_,
                            v_offset_2812_,
                            v_a_2814_,
                            v_a_2815_,
                        );
                        lean_dec(v_offset_2812_);
                        v_fst_2839_ = lean_ctor_get(v___x_2838_, 0);
                        lean_inc(v_fst_2839_);
                        v_snd_2840_ = lean_ctor_get(v___x_2838_, 1);
                        lean_inc(v_snd_2840_);
                        lean_dec_ref(v___x_2838_);
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
                let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_s_u2081_2821_);
                lean_dec(v_offset_2812_);
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
                let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_s_u2081_2821_);
                lean_dec(v_offset_2812_);
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
                let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_s_u2081_2821_);
                lean_dec(v_offset_2812_);
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
                let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_s_u2081_2821_);
                lean_dec(v_offset_2812_);
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
                let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_s_u2081_2821_);
                lean_dec(v_offset_2812_);
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
                let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2848_: u8 = 0;
                v___x_2847_ = l_Lean_Expr_looseBVarRange(v_e_2811_);
                v___x_2848_ = lean_nat_dec_le(v___x_2847_, v_s_u2081_2821_);
                lean_dec(v_s_u2081_2821_);
                lean_dec(v___x_2847_);
                if v___x_2848_ == 0 {
                    match lean_obj_tag(v_e_2811_) {
                        9 => {
                            let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_2812_);
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
                            let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_2812_);
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
                            let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_2812_);
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
                            let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_2812_);
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
                            let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_2812_);
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
                            let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_2812_);
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
                            let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_fst_2856_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_snd_2857_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_fst_2858_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_snd_2859_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
                            v___x_2855_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_2808_, v_n_2809_, v_subst_2810_, v_e_2811_, v_offset_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
                            v_fst_2856_ = lean_ctor_get(v___x_2855_, 0);
                            lean_inc(v_fst_2856_);
                            v_snd_2857_ = lean_ctor_get(v___x_2855_, 1);
                            lean_inc(v_snd_2857_);
                            lean_dec_ref(v___x_2855_);
                            v_fst_2858_ = lean_ctor_get(v_fst_2856_, 0);
                            lean_inc(v_fst_2858_);
                            v_snd_2859_ = lean_ctor_get(v_fst_2856_, 1);
                            lean_inc(v_snd_2859_);
                            lean_dec(v_fst_2856_);
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
                    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_offset_2812_);
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
    mut v_beginIdx_2862_: *mut LeanObject,
    mut v_n_2863_: *mut LeanObject,
    mut v_subst_2864_: *mut LeanObject,
    mut v_e_2865_: *mut LeanObject,
    mut v_offset_2866_: *mut LeanObject,
    mut v_a_2867_: *mut LeanObject,
    mut v_a_2868_: *mut LeanObject,
    mut v_a_2869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2870_: u8 = 0;
    let mut v_res_2871_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2870_ = (lean_unbox(v_a_2868_) as u8);
    v_res_2871_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2(v_beginIdx_2862_, v_n_2863_, v_subst_2864_, v_e_2865_, v_offset_2866_, v_a_2867_, v_a_boxed_2870_, v_a_2869_);
    lean_dec_ref(v_subst_2864_);
    lean_dec(v_n_2863_);
    lean_dec(v_beginIdx_2862_);
    return v_res_2871_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___boxed(
    mut v_beginIdx_2872_: *mut LeanObject,
    mut v_n_2873_: *mut LeanObject,
    mut v_subst_2874_: *mut LeanObject,
    mut v_e_2875_: *mut LeanObject,
    mut v_offset_2876_: *mut LeanObject,
    mut v_a_2877_: *mut LeanObject,
    mut v_a_2878_: *mut LeanObject,
    mut v_a_2879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2880_: u8 = 0;
    let mut v_res_2881_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2880_ = (lean_unbox(v_a_2878_) as u8);
    v_res_2881_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_2872_, v_n_2873_, v_subst_2874_, v_e_2875_, v_offset_2876_, v_a_2877_, v_a_boxed_2880_, v_a_2879_);
    lean_dec_ref(v_subst_2874_);
    lean_dec(v_n_2873_);
    lean_dec(v_beginIdx_2872_);
    return v_res_2881_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0() -> *mut LeanObject {
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    v___x_2882_ =
        l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__0(
            lean_box(0),
        );
    return v___x_2882_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1() -> *mut LeanObject {
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    v___x_2883_ = lean_box(0);
    v___x_2884_ = lean_unsigned_to_nat(16);
    v___x_2885_ = lean_mk_array(v___x_2884_, v___x_2883_);
    return v___x_2885_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2() -> *mut LeanObject {
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    v___x_2886_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__1_once),
        _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__1,
    );
    v___x_2887_ = lean_unsigned_to_nat(0);
    v___x_2888_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2888_, 0, v___x_2887_);
    lean_ctor_set(v___x_2888_, 1, v___x_2886_);
    return v___x_2888_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__5() -> *mut LeanObject {
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    v___x_2891_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_2892_ = lean_unsigned_to_nat(34);
    v___x_2893_ = lean_unsigned_to_nat(20);
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
pub unsafe fn _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__6() -> *mut LeanObject {
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    v___x_2897_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_2898_ = lean_unsigned_to_nat(32);
    v___x_2899_ = lean_unsigned_to_nat(19);
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
    mut v_e_2903_: *mut LeanObject,
    mut v_beginIdx_2904_: *mut LeanObject,
    mut v_endIdx_2905_: *mut LeanObject,
    mut v_subst_2906_: *mut LeanObject,
    mut v_a_2907_: *mut LeanObject,
    mut v_a_2908_: *mut LeanObject,
    mut v_a_2909_: *mut LeanObject,
    mut v_a_2910_: *mut LeanObject,
    mut v_a_2911_: *mut LeanObject,
    mut v_a_2912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2914_: u8 = 0;
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: u8 = 0;
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2928_: u8 = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2950_: u8 = 0;
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2953_: u8 = 0;
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2959_: u8 = 0;
    let mut v_unused_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2961_: u8 = 0;
    let mut v_n_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: u8 = 0;
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2986_: u8 = 0;
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
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
                        v_share_2918_ = lean_ctor_get(v___x_2917_, 0);
                        v_maxFVar_2919_ = lean_ctor_get(v___x_2917_, 1);
                        v_proofInstInfo_2920_ = lean_ctor_get(v___x_2917_, 2);
                        v_inferType_2921_ = lean_ctor_get(v___x_2917_, 3);
                        v_getLevel_2922_ = lean_ctor_get(v___x_2917_, 4);
                        v_congrInfo_2923_ = lean_ctor_get(v___x_2917_, 5);
                        v_defEqI_2924_ = lean_ctor_get(v___x_2917_, 6);
                        v_extensions_2925_ = lean_ctor_get(v___x_2917_, 7);
                        v_issues_2926_ = lean_ctor_get(v___x_2917_, 8);
                        v_canon_2927_ = lean_ctor_get(v___x_2917_, 9);
                        v_debug_2928_ = lean_ctor_get_uint8(
                            v___x_2917_,
                            (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        );
                        v_isSharedCheck_2986_ = (!lean_is_exclusive(v___x_2917_)) as u8;
                        if v_isSharedCheck_2986_ == 0 {
                            v___x_2930_ = v___x_2917_;
                            v_isShared_2931_ = v_isSharedCheck_2986_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_canon_2927_);
                            lean_inc(v_issues_2926_);
                            lean_inc(v_extensions_2925_);
                            lean_inc(v_defEqI_2924_);
                            lean_inc(v_congrInfo_2923_);
                            lean_inc(v_getLevel_2922_);
                            lean_inc(v_inferType_2921_);
                            lean_inc(v_proofInstInfo_2920_);
                            lean_inc(v_maxFVar_2919_);
                            lean_inc(v_share_2918_);
                            lean_dec(v___x_2917_);
                            v___x_2930_ = lean_box(0);
                            v_isShared_2931_ = v_isSharedCheck_2986_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_2903_);
                        v___x_2987_ = lean_obj_once(
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
                    lean_dec_ref(v_e_2903_);
                    v___x_2989_ = lean_obj_once(
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
                v___x_2932_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once),
                    _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0,
                );
                if v_isShared_2931_ == 0 {
                    lean_ctor_set(v___x_2930_, 0, v___x_2932_);
                    v___x_2934_ = v___x_2930_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2932_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_maxFVar_2919_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 2, v_proofInstInfo_2920_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 3, v_inferType_2921_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 4, v_getLevel_2922_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 5, v_congrInfo_2923_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 6, v_defEqI_2924_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 7, v_extensions_2925_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 8, v_issues_2926_);
                    lean_ctor_set(v_reuseFailAlloc_2985_, 9, v_canon_2927_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2985_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
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
                v_debug_2961_ = lean_ctor_get_uint8(
                    v___x_2936_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_2936_);
                v_n_2962_ = lean_nat_sub(v_endIdx_2905_, v_beginIdx_2904_);
                v___x_2963_ = lean_unsigned_to_nat(0);
                match lean_obj_tag(v_e_2903_) {
                    0 => {
                        v_deBruijnIndex_2964_ = lean_ctor_get(v_e_2903_, 0);
                        v___x_2965_ = lean_nat_dec_le(v_beginIdx_2904_, v_deBruijnIndex_2964_);
                        if v___x_2965_ == 0 {
                            lean_dec(v_n_2962_);
                            v_fst_2938_ = v_e_2903_;
                            v_snd_2939_ = v_share_2918_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_deBruijnIndex_2964_);
                            lean_dec_ref_known(v_e_2903_, 1);
                            v___x_2966_ = lean_nat_dec_lt(v_deBruijnIndex_2964_, v_n_2962_);
                            if v___x_2966_ == 0 {
                                v___x_2967_ = lean_nat_sub(v_deBruijnIndex_2964_, v_n_2962_);
                                lean_dec(v_n_2962_);
                                lean_dec(v_deBruijnIndex_2964_);
                                v___x_2968_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_2967_, v_share_2918_);
                                v_fst_2969_ = lean_ctor_get(v___x_2968_, 0);
                                lean_inc(v_fst_2969_);
                                v_snd_2970_ = lean_ctor_get(v___x_2968_, 1);
                                lean_inc(v_snd_2970_);
                                lean_dec_ref(v___x_2968_);
                                v_fst_2938_ = v_fst_2969_;
                                v_snd_2939_ = v_snd_2970_;
                                state = 3;
                                continue;
                            } else {
                                v___x_2971_ = lean_nat_sub(v_n_2962_, v_deBruijnIndex_2964_);
                                lean_dec(v_deBruijnIndex_2964_);
                                lean_dec(v_n_2962_);
                                v___x_2972_ = lean_unsigned_to_nat(1);
                                v___x_2973_ = lean_nat_sub(v___x_2971_, v___x_2972_);
                                lean_dec(v___x_2971_);
                                v_v_2974_ = lean_array_fget_borrowed(v_subst_2906_, v___x_2973_);
                                lean_dec(v___x_2973_);
                                lean_inc(v_v_2974_);
                                v___x_2975_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                                    v_v_2974_,
                                    v___x_2963_,
                                    v___x_2963_,
                                    v_debug_2961_,
                                    v_share_2918_,
                                );
                                v_fst_2976_ = lean_ctor_get(v___x_2975_, 0);
                                lean_inc(v_fst_2976_);
                                v_snd_2977_ = lean_ctor_get(v___x_2975_, 1);
                                lean_inc(v_snd_2977_);
                                lean_dec_ref(v___x_2975_);
                                v_fst_2938_ = v_fst_2976_;
                                v_snd_2939_ = v_snd_2977_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                    9 => {
                        lean_dec(v_n_2962_);
                        v_fst_2938_ = v_e_2903_;
                        v_snd_2939_ = v_share_2918_;
                        state = 3;
                        continue;
                    }
                    2 => {
                        lean_dec(v_n_2962_);
                        v_fst_2938_ = v_e_2903_;
                        v_snd_2939_ = v_share_2918_;
                        state = 3;
                        continue;
                    }
                    1 => {
                        lean_dec(v_n_2962_);
                        v_fst_2938_ = v_e_2903_;
                        v_snd_2939_ = v_share_2918_;
                        state = 3;
                        continue;
                    }
                    4 => {
                        lean_dec(v_n_2962_);
                        v_fst_2938_ = v_e_2903_;
                        v_snd_2939_ = v_share_2918_;
                        state = 3;
                        continue;
                    }
                    3 => {
                        lean_dec(v_n_2962_);
                        v_fst_2938_ = v_e_2903_;
                        v_snd_2939_ = v_share_2918_;
                        state = 3;
                        continue;
                    }
                    _ => {
                        v___x_2978_ = l_Lean_Expr_looseBVarRange(v_e_2903_);
                        v___x_2979_ = lean_nat_dec_le(v___x_2978_, v_beginIdx_2904_);
                        lean_dec(v___x_2978_);
                        if v___x_2979_ == 0 {
                            match lean_obj_tag(v_e_2903_) {
                                9 => {
                                    lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                2 => {
                                    lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                0 => {
                                    lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                1 => {
                                    lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                4 => {
                                    lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                3 => {
                                    lean_dec(v_n_2962_);
                                    v_fst_2938_ = v_e_2903_;
                                    v_snd_2939_ = v_share_2918_;
                                    state = 3;
                                    continue;
                                }
                                _ => {
                                    v___x_2980_ = lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_instantiateRevRangeS___closed__2
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once
                                        ),
                                        _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2,
                                    );
                                    v___x_2981_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2(v_beginIdx_2904_, v_n_2962_, v_subst_2906_, v_e_2903_, v___x_2963_, v___x_2980_, v_debug_2961_, v_share_2918_);
                                    lean_dec(v_n_2962_);
                                    v_fst_2982_ = lean_ctor_get(v___x_2981_, 0);
                                    lean_inc(v_fst_2982_);
                                    v_snd_2983_ = lean_ctor_get(v___x_2981_, 1);
                                    lean_inc(v_snd_2983_);
                                    lean_dec_ref(v___x_2981_);
                                    v_fst_2984_ = lean_ctor_get(v_fst_2982_, 0);
                                    lean_inc(v_fst_2984_);
                                    lean_dec(v_fst_2982_);
                                    v_fst_2938_ = v_fst_2984_;
                                    v_snd_2939_ = v_snd_2983_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_n_2962_);
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
                v_maxFVar_2941_ = lean_ctor_get(v___x_2940_, 1);
                v_proofInstInfo_2942_ = lean_ctor_get(v___x_2940_, 2);
                v_inferType_2943_ = lean_ctor_get(v___x_2940_, 3);
                v_getLevel_2944_ = lean_ctor_get(v___x_2940_, 4);
                v_congrInfo_2945_ = lean_ctor_get(v___x_2940_, 5);
                v_defEqI_2946_ = lean_ctor_get(v___x_2940_, 6);
                v_extensions_2947_ = lean_ctor_get(v___x_2940_, 7);
                v_issues_2948_ = lean_ctor_get(v___x_2940_, 8);
                v_canon_2949_ = lean_ctor_get(v___x_2940_, 9);
                v_debug_2950_ = lean_ctor_get_uint8(
                    v___x_2940_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2959_ = (!lean_is_exclusive(v___x_2940_)) as u8;
                if v_isSharedCheck_2959_ == 0 {
                    v_unused_2960_ = lean_ctor_get(v___x_2940_, 0);
                    lean_dec(v_unused_2960_);
                    v___x_2952_ = v___x_2940_;
                    v_isShared_2953_ = v_isSharedCheck_2959_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_canon_2949_);
                    lean_inc(v_issues_2948_);
                    lean_inc(v_extensions_2947_);
                    lean_inc(v_defEqI_2946_);
                    lean_inc(v_congrInfo_2945_);
                    lean_inc(v_getLevel_2944_);
                    lean_inc(v_inferType_2943_);
                    lean_inc(v_proofInstInfo_2942_);
                    lean_inc(v_maxFVar_2941_);
                    lean_dec(v___x_2940_);
                    v___x_2952_ = lean_box(0);
                    v_isShared_2953_ = v_isSharedCheck_2959_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2953_ == 0 {
                    lean_ctor_set(v___x_2952_, 0, v_snd_2939_);
                    v___x_2955_ = v___x_2952_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_snd_2939_);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_maxFVar_2941_);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 2, v_proofInstInfo_2942_);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 3, v_inferType_2943_);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 4, v_getLevel_2944_);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 5, v_congrInfo_2945_);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 6, v_defEqI_2946_);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 7, v_extensions_2947_);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 8, v_issues_2948_);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 9, v_canon_2949_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2958_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_2950_,
                    );
                    v___x_2955_ = v_reuseFailAlloc_2958_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2956_ = lean_st_ref_set(v_a_2908_, v___x_2955_);
                v___x_2957_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2957_, 0, v_fst_2938_);
                return v___x_2957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevRangeS___boxed(
    mut v_e_2991_: *mut LeanObject,
    mut v_beginIdx_2992_: *mut LeanObject,
    mut v_endIdx_2993_: *mut LeanObject,
    mut v_subst_2994_: *mut LeanObject,
    mut v_a_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
    mut v_a_2997_: *mut LeanObject,
    mut v_a_2998_: *mut LeanObject,
    mut v_a_2999_: *mut LeanObject,
    mut v_a_3000_: *mut LeanObject,
    mut v_a_3001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3002_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3000_);
    lean_dec_ref(v_a_2999_);
    lean_dec(v_a_2998_);
    lean_dec_ref(v_a_2997_);
    lean_dec(v_a_2996_);
    lean_dec_ref(v_a_2995_);
    lean_dec_ref(v_subst_2994_);
    lean_dec(v_endIdx_2993_);
    lean_dec(v_beginIdx_2992_);
    return v_res_3002_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(
    mut v_00_u03b2_3003_: *mut LeanObject,
    mut v_m_3004_: *mut LeanObject,
    mut v_a_3005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    v___x_3006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_m_3004_, v_a_3005_);
    return v___x_3006_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_3007_: *mut LeanObject,
    mut v_m_3008_: *mut LeanObject,
    mut v_a_3009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3010_: *mut LeanObject = core::ptr::null_mut();
    v_res_3010_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4(v_00_u03b2_3007_, v_m_3008_, v_a_3009_);
    lean_dec_ref(v_a_3009_);
    lean_dec_ref(v_m_3008_);
    return v_res_3010_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(
    mut v_00_u03b2_3011_: *mut LeanObject,
    mut v_a_3012_: *mut LeanObject,
    mut v_x_3013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    v___x_3014_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___redArg(v_a_3012_, v_x_3013_);
    return v___x_3014_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12___boxed(
    mut v_00_u03b2_3015_: *mut LeanObject,
    mut v_a_3016_: *mut LeanObject,
    mut v_x_3017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3018_: *mut LeanObject = core::ptr::null_mut();
    v_res_3018_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4_spec__12(v_00_u03b2_3015_, v_a_3016_, v_x_3017_);
    lean_dec(v_x_3017_);
    lean_dec_ref(v_a_3016_);
    return v_res_3018_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevS(
    mut v_e_3019_: *mut LeanObject,
    mut v_subst_3020_: *mut LeanObject,
    mut v_a_3021_: *mut LeanObject,
    mut v_a_3022_: *mut LeanObject,
    mut v_a_3023_: *mut LeanObject,
    mut v_a_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
    mut v_a_3026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    v___x_3028_ = lean_unsigned_to_nat(0);
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
    mut v_e_3031_: *mut LeanObject,
    mut v_subst_3032_: *mut LeanObject,
    mut v_a_3033_: *mut LeanObject,
    mut v_a_3034_: *mut LeanObject,
    mut v_a_3035_: *mut LeanObject,
    mut v_a_3036_: *mut LeanObject,
    mut v_a_3037_: *mut LeanObject,
    mut v_a_3038_: *mut LeanObject,
    mut v_a_3039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3040_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3038_);
    lean_dec_ref(v_a_3037_);
    lean_dec(v_a_3036_);
    lean_dec_ref(v_a_3035_);
    lean_dec(v_a_3034_);
    lean_dec_ref(v_a_3033_);
    lean_dec_ref(v_subst_3032_);
    return v_res_3040_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(
    mut v_msg_3041_: *mut LeanObject,
    mut v___y_3042_: u8,
    mut v___y_3043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111__overap_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    v___f_3044_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__0;
    v___f_3045_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__1;
    v___f_3046_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__2;
    v___f_3047_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__3;
    v___f_3048_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__4;
    v___f_3049_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__5;
    v___f_3050_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9___closed__6;
    v___x_3051_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3051_, 0, v___f_3044_);
    lean_ctor_set(v___x_3051_, 1, v___f_3045_);
    v___x_3052_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3052_, 0, v___x_3051_);
    lean_ctor_set(v___x_3052_, 1, v___f_3046_);
    lean_ctor_set(v___x_3052_, 2, v___f_3047_);
    lean_ctor_set(v___x_3052_, 3, v___f_3048_);
    lean_ctor_set(v___x_3052_, 4, v___f_3049_);
    v___x_3053_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3053_, 0, v___x_3052_);
    lean_ctor_set(v___x_3053_, 1, v___f_3050_);
    lean_inc_ref_n(v___x_3053_, 6);
    v___f_3054_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_3054_, 0, v___x_3053_);
    v___f_3055_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_3055_, 0, v___x_3053_);
    v___f_3056_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_3056_, 0, v___x_3053_);
    v___f_3057_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_3057_, 0, v___x_3053_);
    v___x_3058_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_3058_, 0, lean_box(0));
    lean_closure_set(v___x_3058_, 1, lean_box(0));
    lean_closure_set(v___x_3058_, 2, v___x_3053_);
    v___x_3059_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3059_, 0, v___x_3058_);
    lean_ctor_set(v___x_3059_, 1, v___f_3054_);
    v___x_3060_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_3060_, 0, lean_box(0));
    lean_closure_set(v___x_3060_, 1, lean_box(0));
    lean_closure_set(v___x_3060_, 2, v___x_3053_);
    v___x_3061_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3061_, 0, v___x_3059_);
    lean_ctor_set(v___x_3061_, 1, v___x_3060_);
    lean_ctor_set(v___x_3061_, 2, v___f_3055_);
    lean_ctor_set(v___x_3061_, 3, v___f_3056_);
    lean_ctor_set(v___x_3061_, 4, v___f_3057_);
    v___x_3062_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_3062_, 0, lean_box(0));
    lean_closure_set(v___x_3062_, 1, lean_box(0));
    lean_closure_set(v___x_3062_, 2, v___x_3053_);
    v___x_3063_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3063_, 0, v___x_3061_);
    lean_ctor_set(v___x_3063_, 1, v___x_3062_);
    v___x_3064_ = l_Lean_instInhabitedExpr;
    v___x_3065_ = l_instInhabitedOfMonad___redArg(v___x_3063_, v___x_3064_);
    v___f_3066_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3066_, 0, v___x_3065_);
    v___x_3111__overap_3067_ = lean_panic_fn_borrowed(v___f_3066_, v_msg_3041_);
    lean_dec_ref(v___f_3066_);
    v___x_3068_ = lean_box((v___y_3042_) as usize);
    v___x_3069_ = lean_apply_2(v___x_3111__overap_3067_, v___x_3068_, v___y_3043_);
    return v___x_3069_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1___boxed(
    mut v_msg_3070_: *mut LeanObject,
    mut v___y_3071_: *mut LeanObject,
    mut v___y_3072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3548__boxed_3073_: u8 = 0;
    let mut v_res_3074_: *mut LeanObject = core::ptr::null_mut();
    v___y_3548__boxed_3073_ = (lean_unbox(v___y_3071_) as u8);
    v_res_3074_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v_msg_3070_, v___y_3548__boxed_3073_, v___y_3072_);
    return v_res_3074_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(
    mut v_n_3075_: *mut LeanObject,
    mut v_beginIdx_3076_: *mut LeanObject,
    mut v_subst_3077_: *mut LeanObject,
    mut v_e_3078_: *mut LeanObject,
    mut v_offset_3079_: *mut LeanObject,
    mut v_a_3080_: *mut LeanObject,
    mut v_a_3081_: u8,
    mut v_a_3082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3095_: u8 = 0;
    let mut v_fst_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3100_: u8 = 0;
    let mut v___y_3102_: u8 = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: u8 = 0;
    let mut v___x_3111_: u8 = 0;
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_binderName_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3117_: u8 = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v_fst_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3135_: u8 = 0;
    let mut v___y_3137_: u8 = 0;
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3146_: u8 = 0;
    let mut v_isSharedCheck_3147_: u8 = 0;
    let mut v_isSharedCheck_3148_: u8 = 0;
    let mut v_binderName_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3152_: u8 = 0;
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3165_: u8 = 0;
    let mut v_fst_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3170_: u8 = 0;
    let mut v___y_3172_: u8 = 0;
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: u8 = 0;
    let mut v___x_3181_: u8 = 0;
    let mut v_isSharedCheck_3182_: u8 = 0;
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_declName_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_3188_: u8 = 0;
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3206_: u8 = 0;
    let mut v_fst_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3211_: u8 = 0;
    let mut v___y_3213_: u8 = 0;
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: u8 = 0;
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut v_isSharedCheck_3226_: u8 = 0;
    let mut v_data_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3234_: u8 = 0;
    let mut v_fst_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3239_: u8 = 0;
    let mut v___x_3240_: u8 = 0;
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut v_isSharedCheck_3249_: u8 = 0;
    let mut v_typeName_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v_fst_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3263_: u8 = 0;
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_3078_) {
                5 => {
                    v_fn_3083_ = lean_ctor_get(v_e_3078_, 0);
                    v_arg_3084_ = lean_ctor_get(v_e_3078_, 1);
                    lean_inc(v_offset_3079_);
                    lean_inc_ref(v_fn_3083_);
                    v___x_3085_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_fn_3083_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3086_ = lean_ctor_get(v___x_3085_, 0);
                    lean_inc(v_fst_3086_);
                    v_snd_3087_ = lean_ctor_get(v___x_3085_, 1);
                    lean_inc(v_snd_3087_);
                    lean_dec_ref(v___x_3085_);
                    v_fst_3088_ = lean_ctor_get(v_fst_3086_, 0);
                    lean_inc(v_fst_3088_);
                    v_snd_3089_ = lean_ctor_get(v_fst_3086_, 1);
                    lean_inc(v_snd_3089_);
                    lean_dec(v_fst_3086_);
                    lean_inc_ref(v_arg_3084_);
                    v___x_3090_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_arg_3084_, v_offset_3079_, v_snd_3089_, v_a_3081_, v_snd_3087_);
                    v_fst_3091_ = lean_ctor_get(v___x_3090_, 0);
                    v_snd_3092_ = lean_ctor_get(v___x_3090_, 1);
                    v_isSharedCheck_3113_ = (!lean_is_exclusive(v___x_3090_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v___x_3094_ = v___x_3090_;
                        v_isShared_3095_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3092_);
                        lean_inc(v_fst_3091_);
                        lean_dec(v___x_3090_);
                        v___x_3094_ = lean_box(0);
                        v_isShared_3095_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    }
                }
                6 => {
                    v_binderName_3114_ = lean_ctor_get(v_e_3078_, 0);
                    v_binderType_3115_ = lean_ctor_get(v_e_3078_, 1);
                    v_body_3116_ = lean_ctor_get(v_e_3078_, 2);
                    v_binderInfo_3117_ = lean_ctor_get_uint8(
                        v_e_3078_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_3079_);
                    lean_inc_ref(v_binderType_3115_);
                    v___x_3118_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_binderType_3115_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3119_ = lean_ctor_get(v___x_3118_, 0);
                    lean_inc(v_fst_3119_);
                    v_snd_3120_ = lean_ctor_get(v___x_3118_, 1);
                    lean_inc(v_snd_3120_);
                    lean_dec_ref(v___x_3118_);
                    v_fst_3121_ = lean_ctor_get(v_fst_3119_, 0);
                    lean_inc(v_fst_3121_);
                    v_snd_3122_ = lean_ctor_get(v_fst_3119_, 1);
                    lean_inc(v_snd_3122_);
                    lean_dec(v_fst_3119_);
                    v___x_3123_ = lean_unsigned_to_nat(1);
                    v___x_3124_ = lean_nat_add(v_offset_3079_, v___x_3123_);
                    lean_dec(v_offset_3079_);
                    lean_inc_ref(v_body_3116_);
                    v___x_3125_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_body_3116_, v___x_3124_, v_snd_3122_, v_a_3081_, v_snd_3120_);
                    v_fst_3126_ = lean_ctor_get(v___x_3125_, 0);
                    v_snd_3127_ = lean_ctor_get(v___x_3125_, 1);
                    v_isSharedCheck_3148_ = (!lean_is_exclusive(v___x_3125_)) as u8;
                    if v_isSharedCheck_3148_ == 0 {
                        v___x_3129_ = v___x_3125_;
                        v_isShared_3130_ = v_isSharedCheck_3148_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_3127_);
                        lean_inc(v_fst_3126_);
                        lean_dec(v___x_3125_);
                        v___x_3129_ = lean_box(0);
                        v_isShared_3130_ = v_isSharedCheck_3148_;
                        state = 6;
                        continue;
                    }
                }
                7 => {
                    v_binderName_3149_ = lean_ctor_get(v_e_3078_, 0);
                    v_binderType_3150_ = lean_ctor_get(v_e_3078_, 1);
                    v_body_3151_ = lean_ctor_get(v_e_3078_, 2);
                    v_binderInfo_3152_ = lean_ctor_get_uint8(
                        v_e_3078_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_3079_);
                    lean_inc_ref(v_binderType_3150_);
                    v___x_3153_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_binderType_3150_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3154_ = lean_ctor_get(v___x_3153_, 0);
                    lean_inc(v_fst_3154_);
                    v_snd_3155_ = lean_ctor_get(v___x_3153_, 1);
                    lean_inc(v_snd_3155_);
                    lean_dec_ref(v___x_3153_);
                    v_fst_3156_ = lean_ctor_get(v_fst_3154_, 0);
                    lean_inc(v_fst_3156_);
                    v_snd_3157_ = lean_ctor_get(v_fst_3154_, 1);
                    lean_inc(v_snd_3157_);
                    lean_dec(v_fst_3154_);
                    v___x_3158_ = lean_unsigned_to_nat(1);
                    v___x_3159_ = lean_nat_add(v_offset_3079_, v___x_3158_);
                    lean_dec(v_offset_3079_);
                    lean_inc_ref(v_body_3151_);
                    v___x_3160_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_body_3151_, v___x_3159_, v_snd_3157_, v_a_3081_, v_snd_3155_);
                    v_fst_3161_ = lean_ctor_get(v___x_3160_, 0);
                    v_snd_3162_ = lean_ctor_get(v___x_3160_, 1);
                    v_isSharedCheck_3183_ = (!lean_is_exclusive(v___x_3160_)) as u8;
                    if v_isSharedCheck_3183_ == 0 {
                        v___x_3164_ = v___x_3160_;
                        v_isShared_3165_ = v_isSharedCheck_3183_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_snd_3162_);
                        lean_inc(v_fst_3161_);
                        lean_dec(v___x_3160_);
                        v___x_3164_ = lean_box(0);
                        v_isShared_3165_ = v_isSharedCheck_3183_;
                        state = 11;
                        continue;
                    }
                }
                8 => {
                    v_declName_3184_ = lean_ctor_get(v_e_3078_, 0);
                    v_type_3185_ = lean_ctor_get(v_e_3078_, 1);
                    v_value_3186_ = lean_ctor_get(v_e_3078_, 2);
                    v_body_3187_ = lean_ctor_get(v_e_3078_, 3);
                    v_nondep_3188_ = lean_ctor_get_uint8(
                        v_e_3078_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_inc_n(v_offset_3079_, 2);
                    lean_inc_ref(v_type_3185_);
                    v___x_3189_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_type_3185_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3190_ = lean_ctor_get(v___x_3189_, 0);
                    lean_inc(v_fst_3190_);
                    v_snd_3191_ = lean_ctor_get(v___x_3189_, 1);
                    lean_inc(v_snd_3191_);
                    lean_dec_ref(v___x_3189_);
                    v_fst_3192_ = lean_ctor_get(v_fst_3190_, 0);
                    lean_inc(v_fst_3192_);
                    v_snd_3193_ = lean_ctor_get(v_fst_3190_, 1);
                    lean_inc(v_snd_3193_);
                    lean_dec(v_fst_3190_);
                    lean_inc_ref(v_value_3186_);
                    v___x_3194_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_value_3186_, v_offset_3079_, v_snd_3193_, v_a_3081_, v_snd_3191_);
                    v_fst_3195_ = lean_ctor_get(v___x_3194_, 0);
                    lean_inc(v_fst_3195_);
                    v_snd_3196_ = lean_ctor_get(v___x_3194_, 1);
                    lean_inc(v_snd_3196_);
                    lean_dec_ref(v___x_3194_);
                    v_fst_3197_ = lean_ctor_get(v_fst_3195_, 0);
                    lean_inc(v_fst_3197_);
                    v_snd_3198_ = lean_ctor_get(v_fst_3195_, 1);
                    lean_inc(v_snd_3198_);
                    lean_dec(v_fst_3195_);
                    v___x_3199_ = lean_unsigned_to_nat(1);
                    v___x_3200_ = lean_nat_add(v_offset_3079_, v___x_3199_);
                    lean_dec(v_offset_3079_);
                    lean_inc_ref(v_body_3187_);
                    v___x_3201_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_body_3187_, v___x_3200_, v_snd_3198_, v_a_3081_, v_snd_3196_);
                    v_fst_3202_ = lean_ctor_get(v___x_3201_, 0);
                    v_snd_3203_ = lean_ctor_get(v___x_3201_, 1);
                    v_isSharedCheck_3226_ = (!lean_is_exclusive(v___x_3201_)) as u8;
                    if v_isSharedCheck_3226_ == 0 {
                        v___x_3205_ = v___x_3201_;
                        v_isShared_3206_ = v_isSharedCheck_3226_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_snd_3203_);
                        lean_inc(v_fst_3202_);
                        lean_dec(v___x_3201_);
                        v___x_3205_ = lean_box(0);
                        v_isShared_3206_ = v_isSharedCheck_3226_;
                        state = 16;
                        continue;
                    }
                }
                10 => {
                    v_data_3227_ = lean_ctor_get(v_e_3078_, 0);
                    v_expr_3228_ = lean_ctor_get(v_e_3078_, 1);
                    lean_inc_ref(v_expr_3228_);
                    v___x_3229_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_expr_3228_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3230_ = lean_ctor_get(v___x_3229_, 0);
                    v_snd_3231_ = lean_ctor_get(v___x_3229_, 1);
                    v_isSharedCheck_3249_ = (!lean_is_exclusive(v___x_3229_)) as u8;
                    if v_isSharedCheck_3249_ == 0 {
                        v___x_3233_ = v___x_3229_;
                        v_isShared_3234_ = v_isSharedCheck_3249_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_snd_3231_);
                        lean_inc(v_fst_3230_);
                        lean_dec(v___x_3229_);
                        v___x_3233_ = lean_box(0);
                        v_isShared_3234_ = v_isSharedCheck_3249_;
                        state = 21;
                        continue;
                    }
                }
                11 => {
                    v_typeName_3250_ = lean_ctor_get(v_e_3078_, 0);
                    v_idx_3251_ = lean_ctor_get(v_e_3078_, 1);
                    v_struct_3252_ = lean_ctor_get(v_e_3078_, 2);
                    lean_inc_ref(v_struct_3252_);
                    v___x_3253_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3075_, v_beginIdx_3076_, v_subst_3077_, v_struct_3252_, v_offset_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
                    v_fst_3254_ = lean_ctor_get(v___x_3253_, 0);
                    v_snd_3255_ = lean_ctor_get(v___x_3253_, 1);
                    v_isSharedCheck_3273_ = (!lean_is_exclusive(v___x_3253_)) as u8;
                    if v_isSharedCheck_3273_ == 0 {
                        v___x_3257_ = v___x_3253_;
                        v_isShared_3258_ = v_isSharedCheck_3273_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_snd_3255_);
                        lean_inc(v_fst_3254_);
                        lean_dec(v___x_3253_);
                        v___x_3257_ = lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3273_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_offset_3079_);
                    lean_dec_ref(v_e_3078_);
                    v___x_3274_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3_once), _init_l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__3);
                    v___x_3275_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_3274_, v_a_3080_, v_a_3081_, v_a_3082_);
                    return v___x_3275_;
                }
            },
            1 => {
                v_fst_3096_ = lean_ctor_get(v_fst_3091_, 0);
                v_snd_3097_ = lean_ctor_get(v_fst_3091_, 1);
                v_isSharedCheck_3112_ = (!lean_is_exclusive(v_fst_3091_)) as u8;
                if v_isSharedCheck_3112_ == 0 {
                    v___x_3099_ = v_fst_3091_;
                    v_isShared_3100_ = v_isSharedCheck_3112_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3097_);
                    lean_inc(v_fst_3096_);
                    lean_dec(v_fst_3091_);
                    v___x_3099_ = lean_box(0);
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
                    lean_del_object(v___x_3099_);
                    lean_del_object(v___x_3094_);
                    lean_dec_ref_known(v_e_3078_, 2);
                    v___x_3103_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_3088_, v_fst_3096_, v_snd_3097_, v_a_3081_, v_snd_3092_);
                    return v___x_3103_;
                } else {
                    lean_dec(v_fst_3096_);
                    lean_dec(v_fst_3088_);
                    if v_isShared_3100_ == 0 {
                        lean_ctor_set(v___x_3099_, 0, v_e_3078_);
                        v___x_3105_ = v___x_3099_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_e_3078_);
                        lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_snd_3097_);
                        v___x_3105_ = v_reuseFailAlloc_3109_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3095_ == 0 {
                    lean_ctor_set(v___x_3094_, 0, v___x_3105_);
                    v___x_3107_ = v___x_3094_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
                    lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_snd_3092_);
                    v___x_3107_ = v_reuseFailAlloc_3108_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3107_;
            }
            6 => {
                v_fst_3131_ = lean_ctor_get(v_fst_3126_, 0);
                v_snd_3132_ = lean_ctor_get(v_fst_3126_, 1);
                v_isSharedCheck_3147_ = (!lean_is_exclusive(v_fst_3126_)) as u8;
                if v_isSharedCheck_3147_ == 0 {
                    v___x_3134_ = v_fst_3126_;
                    v_isShared_3135_ = v_isSharedCheck_3147_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_3132_);
                    lean_inc(v_fst_3131_);
                    lean_dec(v_fst_3126_);
                    v___x_3134_ = lean_box(0);
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
                    lean_inc(v_binderName_3114_);
                    lean_del_object(v___x_3134_);
                    lean_del_object(v___x_3129_);
                    lean_dec_ref_known(v_e_3078_, 3);
                    v___x_3138_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_3114_, v_binderInfo_3117_, v_fst_3121_, v_fst_3131_, v_snd_3132_, v_a_3081_, v_snd_3127_);
                    return v___x_3138_;
                } else {
                    lean_dec(v_fst_3131_);
                    lean_dec(v_fst_3121_);
                    if v_isShared_3135_ == 0 {
                        lean_ctor_set(v___x_3134_, 0, v_e_3078_);
                        v___x_3140_ = v___x_3134_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_e_3078_);
                        lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_snd_3132_);
                        v___x_3140_ = v_reuseFailAlloc_3144_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3130_ == 0 {
                    lean_ctor_set(v___x_3129_, 0, v___x_3140_);
                    v___x_3142_ = v___x_3129_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_snd_3127_);
                    v___x_3142_ = v_reuseFailAlloc_3143_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3142_;
            }
            11 => {
                v_fst_3166_ = lean_ctor_get(v_fst_3161_, 0);
                v_snd_3167_ = lean_ctor_get(v_fst_3161_, 1);
                v_isSharedCheck_3182_ = (!lean_is_exclusive(v_fst_3161_)) as u8;
                if v_isSharedCheck_3182_ == 0 {
                    v___x_3169_ = v_fst_3161_;
                    v_isShared_3170_ = v_isSharedCheck_3182_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_snd_3167_);
                    lean_inc(v_fst_3166_);
                    lean_dec(v_fst_3161_);
                    v___x_3169_ = lean_box(0);
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
                    lean_inc(v_binderName_3149_);
                    lean_del_object(v___x_3169_);
                    lean_del_object(v___x_3164_);
                    lean_dec_ref_known(v_e_3078_, 3);
                    v___x_3173_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_3149_, v_binderInfo_3152_, v_fst_3156_, v_fst_3166_, v_snd_3167_, v_a_3081_, v_snd_3162_);
                    return v___x_3173_;
                } else {
                    lean_dec(v_fst_3166_);
                    lean_dec(v_fst_3156_);
                    if v_isShared_3170_ == 0 {
                        lean_ctor_set(v___x_3169_, 0, v_e_3078_);
                        v___x_3175_ = v___x_3169_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_e_3078_);
                        lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_snd_3167_);
                        v___x_3175_ = v_reuseFailAlloc_3179_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_3165_ == 0 {
                    lean_ctor_set(v___x_3164_, 0, v___x_3175_);
                    v___x_3177_ = v___x_3164_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_snd_3162_);
                    v___x_3177_ = v_reuseFailAlloc_3178_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3177_;
            }
            16 => {
                v_fst_3207_ = lean_ctor_get(v_fst_3202_, 0);
                v_snd_3208_ = lean_ctor_get(v_fst_3202_, 1);
                v_isSharedCheck_3225_ = (!lean_is_exclusive(v_fst_3202_)) as u8;
                if v_isSharedCheck_3225_ == 0 {
                    v___x_3210_ = v_fst_3202_;
                    v_isShared_3211_ = v_isSharedCheck_3225_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_snd_3208_);
                    lean_inc(v_fst_3207_);
                    lean_dec(v_fst_3202_);
                    v___x_3210_ = lean_box(0);
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
                    lean_inc(v_declName_3184_);
                    lean_del_object(v___x_3210_);
                    lean_del_object(v___x_3205_);
                    lean_dec_ref_known(v_e_3078_, 4);
                    v___x_3214_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_3184_, v_fst_3192_, v_fst_3197_, v_fst_3207_, v_nondep_3188_, v_snd_3208_, v_a_3081_, v_snd_3203_);
                    return v___x_3214_;
                } else {
                    v___x_3215_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_3187_,
                            v_fst_3207_,
                        );
                    if v___x_3215_ == 0 {
                        lean_inc(v_declName_3184_);
                        lean_del_object(v___x_3210_);
                        lean_del_object(v___x_3205_);
                        lean_dec_ref_known(v_e_3078_, 4);
                        v___x_3216_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_3184_, v_fst_3192_, v_fst_3197_, v_fst_3207_, v_nondep_3188_, v_snd_3208_, v_a_3081_, v_snd_3203_);
                        return v___x_3216_;
                    } else {
                        lean_dec(v_fst_3207_);
                        lean_dec(v_fst_3197_);
                        lean_dec(v_fst_3192_);
                        if v_isShared_3211_ == 0 {
                            lean_ctor_set(v___x_3210_, 0, v_e_3078_);
                            v___x_3218_ = v___x_3210_;
                            state = 19;
                            continue;
                        } else {
                            v_reuseFailAlloc_3222_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_e_3078_);
                            lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_snd_3208_);
                            v___x_3218_ = v_reuseFailAlloc_3222_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_3206_ == 0 {
                    lean_ctor_set(v___x_3205_, 0, v___x_3218_);
                    v___x_3220_ = v___x_3205_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_snd_3203_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3220_;
            }
            21 => {
                v_fst_3235_ = lean_ctor_get(v_fst_3230_, 0);
                v_snd_3236_ = lean_ctor_get(v_fst_3230_, 1);
                v_isSharedCheck_3248_ = (!lean_is_exclusive(v_fst_3230_)) as u8;
                if v_isSharedCheck_3248_ == 0 {
                    v___x_3238_ = v_fst_3230_;
                    v_isShared_3239_ = v_isSharedCheck_3248_;
                    state = 22;
                    continue;
                } else {
                    lean_inc(v_snd_3236_);
                    lean_inc(v_fst_3235_);
                    lean_dec(v_fst_3230_);
                    v___x_3238_ = lean_box(0);
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
                    lean_inc(v_data_3227_);
                    lean_del_object(v___x_3238_);
                    lean_del_object(v___x_3233_);
                    lean_dec_ref_known(v_e_3078_, 2);
                    v___x_3241_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_3227_, v_fst_3235_, v_snd_3236_, v_a_3081_, v_snd_3231_);
                    return v___x_3241_;
                } else {
                    lean_dec(v_fst_3235_);
                    if v_isShared_3239_ == 0 {
                        lean_ctor_set(v___x_3238_, 0, v_e_3078_);
                        v___x_3243_ = v___x_3238_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_e_3078_);
                        lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_snd_3236_);
                        v___x_3243_ = v_reuseFailAlloc_3247_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_3234_ == 0 {
                    lean_ctor_set(v___x_3233_, 0, v___x_3243_);
                    v___x_3245_ = v___x_3233_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
                    lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_snd_3231_);
                    v___x_3245_ = v_reuseFailAlloc_3246_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3245_;
            }
            25 => {
                v_fst_3259_ = lean_ctor_get(v_fst_3254_, 0);
                v_snd_3260_ = lean_ctor_get(v_fst_3254_, 1);
                v_isSharedCheck_3272_ = (!lean_is_exclusive(v_fst_3254_)) as u8;
                if v_isSharedCheck_3272_ == 0 {
                    v___x_3262_ = v_fst_3254_;
                    v_isShared_3263_ = v_isSharedCheck_3272_;
                    state = 26;
                    continue;
                } else {
                    lean_inc(v_snd_3260_);
                    lean_inc(v_fst_3259_);
                    lean_dec(v_fst_3254_);
                    v___x_3262_ = lean_box(0);
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
                    lean_inc(v_idx_3251_);
                    lean_inc(v_typeName_3250_);
                    lean_del_object(v___x_3262_);
                    lean_del_object(v___x_3257_);
                    lean_dec_ref_known(v_e_3078_, 3);
                    v___x_3265_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_3250_, v_idx_3251_, v_fst_3259_, v_snd_3260_, v_a_3081_, v_snd_3255_);
                    return v___x_3265_;
                } else {
                    lean_dec(v_fst_3259_);
                    if v_isShared_3263_ == 0 {
                        lean_ctor_set(v___x_3262_, 0, v_e_3078_);
                        v___x_3267_ = v___x_3262_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_e_3078_);
                        lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_snd_3260_);
                        v___x_3267_ = v_reuseFailAlloc_3271_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_3258_ == 0 {
                    lean_ctor_set(v___x_3257_, 0, v___x_3267_);
                    v___x_3269_ = v___x_3257_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
                    lean_ctor_set(v_reuseFailAlloc_3270_, 1, v_snd_3255_);
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
    mut v_n_3276_: *mut LeanObject,
    mut v_beginIdx_3277_: *mut LeanObject,
    mut v_subst_3278_: *mut LeanObject,
    mut v_e_3279_: *mut LeanObject,
    mut v_offset_3280_: *mut LeanObject,
    mut v_a_3281_: *mut LeanObject,
    mut v_a_3282_: u8,
    mut v_a_3283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_offset_3280_);
    lean_inc_ref(v_e_3279_);
    v_key_3284_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_key_3284_, 0, v_e_3279_);
    lean_ctor_set(v_key_3284_, 1, v_offset_3280_);
    v___x_3285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_3281_, v_key_3284_);
    if lean_obj_tag(v___x_3285_) == 1 {
        let mut v_val_3286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_key_3284_, 2);
        lean_dec(v_offset_3280_);
        lean_dec_ref(v_e_3279_);
        v_val_3286_ = lean_ctor_get(v___x_3285_, 0);
        lean_inc(v_val_3286_);
        lean_dec_ref_known(v___x_3285_, 1);
        v___x_3287_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3287_, 0, v_val_3286_);
        lean_ctor_set(v___x_3287_, 1, v_a_3281_);
        v___x_3288_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3288_, 0, v___x_3287_);
        lean_ctor_set(v___x_3288_, 1, v_a_3283_);
        return v___x_3288_;
    } else {
        lean_dec(v___x_3285_);
        match lean_obj_tag(v_e_3279_) {
            0 => {
                let mut v_deBruijnIndex_3289_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3290_: u8 = 0;
                v_deBruijnIndex_3289_ = lean_ctor_get(v_e_3279_, 0);
                v___x_3290_ = lean_nat_dec_le(v_offset_3280_, v_deBruijnIndex_3289_);
                if v___x_3290_ == 0 {
                    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_offset_3280_);
                    v___x_3291_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                        v_key_3284_,
                        v_e_3279_,
                        v_a_3281_,
                        v_a_3282_,
                        v_a_3283_,
                    );
                    return v___x_3291_;
                } else {
                    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3293_: u8 = 0;
                    lean_inc(v_deBruijnIndex_3289_);
                    lean_dec_ref_known(v_e_3279_, 1);
                    v___x_3292_ = lean_nat_add(v_offset_3280_, v_n_3276_);
                    v___x_3293_ = lean_nat_dec_lt(v_deBruijnIndex_3289_, v___x_3292_);
                    lean_dec(v___x_3292_);
                    if v___x_3293_ == 0 {
                        let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_fst_3296_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_snd_3297_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v_offset_3280_);
                        v___x_3294_ = lean_nat_sub(v_deBruijnIndex_3289_, v_n_3276_);
                        lean_dec(v_deBruijnIndex_3289_);
                        v___x_3295_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_3294_, v_a_3283_);
                        v_fst_3296_ = lean_ctor_get(v___x_3295_, 0);
                        lean_inc(v_fst_3296_);
                        v_snd_3297_ = lean_ctor_get(v___x_3295_, 1);
                        lean_inc(v_snd_3297_);
                        lean_dec_ref(v___x_3295_);
                        v___x_3298_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_save(
                            v_key_3284_,
                            v_fst_3296_,
                            v_a_3281_,
                            v_a_3282_,
                            v_snd_3297_,
                        );
                        return v___x_3298_;
                    } else {
                        let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_v_3301_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_fst_3304_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_snd_3305_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
                        v___x_3299_ = lean_nat_add(v_beginIdx_3277_, v_deBruijnIndex_3289_);
                        lean_dec(v_deBruijnIndex_3289_);
                        v___x_3300_ = lean_nat_sub(v___x_3299_, v_offset_3280_);
                        lean_dec(v___x_3299_);
                        v_v_3301_ = lean_array_fget_borrowed(v_subst_3278_, v___x_3300_);
                        lean_dec(v___x_3300_);
                        v___x_3302_ = lean_unsigned_to_nat(0);
                        lean_inc(v_v_3301_);
                        v___x_3303_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                            v_v_3301_,
                            v___x_3302_,
                            v_offset_3280_,
                            v_a_3282_,
                            v_a_3283_,
                        );
                        lean_dec(v_offset_3280_);
                        v_fst_3304_ = lean_ctor_get(v___x_3303_, 0);
                        lean_inc(v_fst_3304_);
                        v_snd_3305_ = lean_ctor_get(v___x_3303_, 1);
                        lean_inc(v_snd_3305_);
                        lean_dec_ref(v___x_3303_);
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
                let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_offset_3280_);
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
                let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_offset_3280_);
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
                let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_offset_3280_);
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
                let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_offset_3280_);
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
                let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_offset_3280_);
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
                let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3313_: u8 = 0;
                v___x_3312_ = l_Lean_Expr_looseBVarRange(v_e_3279_);
                v___x_3313_ = lean_nat_dec_le(v___x_3312_, v_offset_3280_);
                lean_dec(v___x_3312_);
                if v___x_3313_ == 0 {
                    match lean_obj_tag(v_e_3279_) {
                        9 => {
                            let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_3280_);
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
                            let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_3280_);
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
                            let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_3280_);
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
                            let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_3280_);
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
                            let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_3280_);
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
                            let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_offset_3280_);
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
                            let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_fst_3321_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_snd_3322_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_fst_3323_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_snd_3324_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
                            v___x_3320_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_3276_, v_beginIdx_3277_, v_subst_3278_, v_e_3279_, v_offset_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
                            v_fst_3321_ = lean_ctor_get(v___x_3320_, 0);
                            lean_inc(v_fst_3321_);
                            v_snd_3322_ = lean_ctor_get(v___x_3320_, 1);
                            lean_inc(v_snd_3322_);
                            lean_dec_ref(v___x_3320_);
                            v_fst_3323_ = lean_ctor_get(v_fst_3321_, 0);
                            lean_inc(v_fst_3323_);
                            v_snd_3324_ = lean_ctor_get(v_fst_3321_, 1);
                            lean_inc(v_snd_3324_);
                            lean_dec(v_fst_3321_);
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
                    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_offset_3280_);
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
    mut v_n_3327_: *mut LeanObject,
    mut v_beginIdx_3328_: *mut LeanObject,
    mut v_subst_3329_: *mut LeanObject,
    mut v_e_3330_: *mut LeanObject,
    mut v_offset_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
    mut v_a_3333_: *mut LeanObject,
    mut v_a_3334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3335_: u8 = 0;
    let mut v_res_3336_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3335_ = (lean_unbox(v_a_3333_) as u8);
    v_res_3336_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0_spec__0(v_n_3327_, v_beginIdx_3328_, v_subst_3329_, v_e_3330_, v_offset_3331_, v_a_3332_, v_a_boxed_3335_, v_a_3334_);
    lean_dec_ref(v_subst_3329_);
    lean_dec(v_beginIdx_3328_);
    lean_dec(v_n_3327_);
    return v_res_3336_;
}
pub unsafe fn l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0___boxed(
    mut v_n_3337_: *mut LeanObject,
    mut v_beginIdx_3338_: *mut LeanObject,
    mut v_subst_3339_: *mut LeanObject,
    mut v_e_3340_: *mut LeanObject,
    mut v_offset_3341_: *mut LeanObject,
    mut v_a_3342_: *mut LeanObject,
    mut v_a_3343_: *mut LeanObject,
    mut v_a_3344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3345_: u8 = 0;
    let mut v_res_3346_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3345_ = (lean_unbox(v_a_3343_) as u8);
    v_res_3346_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_3337_, v_beginIdx_3338_, v_subst_3339_, v_e_3340_, v_offset_3341_, v_a_3342_, v_a_boxed_3345_, v_a_3344_);
    lean_dec_ref(v_subst_3339_);
    lean_dec(v_beginIdx_3338_);
    lean_dec(v_n_3337_);
    return v_res_3346_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1()
-> *mut LeanObject {
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    v___x_3348_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_3349_ = lean_unsigned_to_nat(34);
    v___x_3350_ = lean_unsigned_to_nat(57);
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
-> *mut LeanObject {
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    v___x_3354_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_3355_ = lean_unsigned_to_nat(32);
    v___x_3356_ = lean_unsigned_to_nat(56);
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
    mut v_e_3360_: *mut LeanObject,
    mut v_beginIdx_3361_: *mut LeanObject,
    mut v_endIdx_3362_: *mut LeanObject,
    mut v_subst_3363_: *mut LeanObject,
    mut v_a_3364_: u8,
    mut v_a_3365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3366_: u8 = 0;
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: u8 = 0;
    let mut v_n_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: u8 = 0;
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: u8 = 0;
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3400_: u8 = 0;
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3404_: u8 = 0;
    let mut v_unused_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
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
                        v___x_3370_ = lean_unsigned_to_nat(0);
                        match lean_obj_tag(v_e_3360_) {
                            0 => {
                                v_deBruijnIndex_3371_ = lean_ctor_get(v_e_3360_, 0);
                                v___x_3372_ = lean_nat_dec_le(v___x_3370_, v_deBruijnIndex_3371_);
                                if v___x_3372_ == 0 {
                                    lean_dec(v_n_3369_);
                                    v___x_3373_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_3373_, 0, v_e_3360_);
                                    lean_ctor_set(v___x_3373_, 1, v_a_3365_);
                                    return v___x_3373_;
                                } else {
                                    lean_inc(v_deBruijnIndex_3371_);
                                    lean_dec_ref_known(v_e_3360_, 1);
                                    v___x_3374_ = lean_nat_dec_lt(v_deBruijnIndex_3371_, v_n_3369_);
                                    if v___x_3374_ == 0 {
                                        v___x_3375_ =
                                            lean_nat_sub(v_deBruijnIndex_3371_, v_n_3369_);
                                        lean_dec(v_n_3369_);
                                        lean_dec(v_deBruijnIndex_3371_);
                                        v___x_3376_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__1___redArg(v___x_3375_, v_a_3365_);
                                        return v___x_3376_;
                                    } else {
                                        lean_dec(v_n_3369_);
                                        v___x_3377_ =
                                            lean_nat_add(v_beginIdx_3361_, v_deBruijnIndex_3371_);
                                        lean_dec(v_deBruijnIndex_3371_);
                                        v_v_3378_ =
                                            lean_array_fget_borrowed(v_subst_3363_, v___x_3377_);
                                        lean_dec(v___x_3377_);
                                        lean_inc(v_v_3378_);
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
                                lean_dec(v_n_3369_);
                                v___x_3380_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3380_, 0, v_e_3360_);
                                lean_ctor_set(v___x_3380_, 1, v_a_3365_);
                                return v___x_3380_;
                            }
                            2 => {
                                lean_dec(v_n_3369_);
                                v___x_3381_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3381_, 0, v_e_3360_);
                                lean_ctor_set(v___x_3381_, 1, v_a_3365_);
                                return v___x_3381_;
                            }
                            1 => {
                                lean_dec(v_n_3369_);
                                v___x_3382_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3382_, 0, v_e_3360_);
                                lean_ctor_set(v___x_3382_, 1, v_a_3365_);
                                return v___x_3382_;
                            }
                            4 => {
                                lean_dec(v_n_3369_);
                                v___x_3383_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3383_, 0, v_e_3360_);
                                lean_ctor_set(v___x_3383_, 1, v_a_3365_);
                                return v___x_3383_;
                            }
                            3 => {
                                lean_dec(v_n_3369_);
                                v___x_3384_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3384_, 0, v_e_3360_);
                                lean_ctor_set(v___x_3384_, 1, v_a_3365_);
                                return v___x_3384_;
                            }
                            _ => {
                                v___x_3385_ = l_Lean_Expr_looseBVarRange(v_e_3360_);
                                v___x_3386_ = lean_nat_dec_le(v___x_3385_, v___x_3370_);
                                lean_dec(v___x_3385_);
                                if v___x_3386_ == 0 {
                                    match lean_obj_tag(v_e_3360_) {
                                        9 => {
                                            lean_dec(v_n_3369_);
                                            v___x_3387_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v___x_3387_, 0, v_e_3360_);
                                            lean_ctor_set(v___x_3387_, 1, v_a_3365_);
                                            return v___x_3387_;
                                        }
                                        2 => {
                                            lean_dec(v_n_3369_);
                                            v___x_3388_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v___x_3388_, 0, v_e_3360_);
                                            lean_ctor_set(v___x_3388_, 1, v_a_3365_);
                                            return v___x_3388_;
                                        }
                                        0 => {
                                            lean_dec(v_n_3369_);
                                            v___x_3389_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v___x_3389_, 0, v_e_3360_);
                                            lean_ctor_set(v___x_3389_, 1, v_a_3365_);
                                            return v___x_3389_;
                                        }
                                        1 => {
                                            lean_dec(v_n_3369_);
                                            v___x_3390_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v___x_3390_, 0, v_e_3360_);
                                            lean_ctor_set(v___x_3390_, 1, v_a_3365_);
                                            return v___x_3390_;
                                        }
                                        4 => {
                                            lean_dec(v_n_3369_);
                                            v___x_3391_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v___x_3391_, 0, v_e_3360_);
                                            lean_ctor_set(v___x_3391_, 1, v_a_3365_);
                                            return v___x_3391_;
                                        }
                                        3 => {
                                            lean_dec(v_n_3369_);
                                            v___x_3392_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v___x_3392_, 0, v_e_3360_);
                                            lean_ctor_set(v___x_3392_, 1, v_a_3365_);
                                            return v___x_3392_;
                                        }
                                        _ => {
                                            v___x_3393_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once), _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2);
                                            v___x_3394_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__0(v_n_3369_, v_beginIdx_3361_, v_subst_3363_, v_e_3360_, v___x_3370_, v___x_3393_, v_a_3364_, v_a_3365_);
                                            lean_dec(v_n_3369_);
                                            v_fst_3395_ = lean_ctor_get(v___x_3394_, 0);
                                            lean_inc(v_fst_3395_);
                                            v_snd_3396_ = lean_ctor_get(v___x_3394_, 1);
                                            lean_inc(v_snd_3396_);
                                            lean_dec_ref(v___x_3394_);
                                            v_fst_3397_ = lean_ctor_get(v_fst_3395_, 0);
                                            v_isSharedCheck_3404_ =
                                                (!lean_is_exclusive(v_fst_3395_)) as u8;
                                            if v_isSharedCheck_3404_ == 0 {
                                                v_unused_3405_ = lean_ctor_get(v_fst_3395_, 1);
                                                lean_dec(v_unused_3405_);
                                                v___x_3399_ = v_fst_3395_;
                                                v_isShared_3400_ = v_isSharedCheck_3404_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc(v_fst_3397_);
                                                lean_dec(v_fst_3395_);
                                                v___x_3399_ = lean_box(0);
                                                v_isShared_3400_ = v_isSharedCheck_3404_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_n_3369_);
                                    v___x_3406_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_3406_, 0, v_e_3360_);
                                    lean_ctor_set(v___x_3406_, 1, v_a_3365_);
                                    return v___x_3406_;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_3360_);
                        v___x_3407_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1_once), _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__1);
                        v___x_3408_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_3407_, v_a_3364_, v_a_3365_);
                        return v___x_3408_;
                    }
                } else {
                    lean_dec_ref(v_e_3360_);
                    v___x_3409_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2_once), _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27___closed__2);
                    v___x_3410_ = l_panic___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27_spec__1(v___x_3409_, v_a_3364_, v_a_3365_);
                    return v___x_3410_;
                }
            }
            1 => {
                if v_isShared_3400_ == 0 {
                    lean_ctor_set(v___x_3399_, 1, v_snd_3396_);
                    v___x_3402_ = v___x_3399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_fst_3397_);
                    lean_ctor_set(v_reuseFailAlloc_3403_, 1, v_snd_3396_);
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
    mut v_e_3411_: *mut LeanObject,
    mut v_beginIdx_3412_: *mut LeanObject,
    mut v_endIdx_3413_: *mut LeanObject,
    mut v_subst_3414_: *mut LeanObject,
    mut v_a_3415_: *mut LeanObject,
    mut v_a_3416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3417_: u8 = 0;
    let mut v_res_3418_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3417_ = (lean_unbox(v_a_3415_) as u8);
    v_res_3418_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(
        v_e_3411_,
        v_beginIdx_3412_,
        v_endIdx_3413_,
        v_subst_3414_,
        v_a_boxed_3417_,
        v_a_3416_,
    );
    lean_dec_ref(v_subst_3414_);
    lean_dec(v_endIdx_3413_);
    lean_dec(v_beginIdx_3412_);
    return v_res_3418_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(
    mut v_e_3419_: *mut LeanObject,
    mut v_subst_3420_: *mut LeanObject,
    mut v_a_3421_: u8,
    mut v_a_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    v___x_3423_ = lean_unsigned_to_nat(0);
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
    mut v_e_3426_: *mut LeanObject,
    mut v_subst_3427_: *mut LeanObject,
    mut v_a_3428_: *mut LeanObject,
    mut v_a_3429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3430_: u8 = 0;
    let mut v_res_3431_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3430_ = (lean_unbox(v_a_3428_) as u8);
    v_res_3431_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(
        v_e_3426_,
        v_subst_3427_,
        v_a_boxed_3430_,
        v_a_3429_,
    );
    lean_dec_ref(v_subst_3427_);
    return v_res_3431_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateS___redArg(
    mut v_e_3432_: *mut LeanObject,
    mut v_subst_3433_: *mut LeanObject,
    mut v_a_3434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_3447_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3450_: u8 = 0;
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_3456_: u8 = 0;
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_3470_: u8 = 0;
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3479_: u8 = 0;
    let mut v_unused_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3436_ = lean_st_ref_take(v_a_3434_);
                v_share_3437_ = lean_ctor_get(v___x_3436_, 0);
                v_maxFVar_3438_ = lean_ctor_get(v___x_3436_, 1);
                v_proofInstInfo_3439_ = lean_ctor_get(v___x_3436_, 2);
                v_inferType_3440_ = lean_ctor_get(v___x_3436_, 3);
                v_getLevel_3441_ = lean_ctor_get(v___x_3436_, 4);
                v_congrInfo_3442_ = lean_ctor_get(v___x_3436_, 5);
                v_defEqI_3443_ = lean_ctor_get(v___x_3436_, 6);
                v_extensions_3444_ = lean_ctor_get(v___x_3436_, 7);
                v_issues_3445_ = lean_ctor_get(v___x_3436_, 8);
                v_canon_3446_ = lean_ctor_get(v___x_3436_, 9);
                v_debug_3447_ = lean_ctor_get_uint8(
                    v___x_3436_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3482_ = (!lean_is_exclusive(v___x_3436_)) as u8;
                if v_isSharedCheck_3482_ == 0 {
                    v___x_3449_ = v___x_3436_;
                    v_isShared_3450_ = v_isSharedCheck_3482_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_3446_);
                    lean_inc(v_issues_3445_);
                    lean_inc(v_extensions_3444_);
                    lean_inc(v_defEqI_3443_);
                    lean_inc(v_congrInfo_3442_);
                    lean_inc(v_getLevel_3441_);
                    lean_inc(v_inferType_3440_);
                    lean_inc(v_proofInstInfo_3439_);
                    lean_inc(v_maxFVar_3438_);
                    lean_inc(v_share_3437_);
                    lean_dec(v___x_3436_);
                    v___x_3449_ = lean_box(0);
                    v_isShared_3450_ = v_isSharedCheck_3482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3451_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once),
                    _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0,
                );
                if v_isShared_3450_ == 0 {
                    lean_ctor_set(v___x_3449_, 0, v___x_3451_);
                    v___x_3453_ = v___x_3449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3451_);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_maxFVar_3438_);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 2, v_proofInstInfo_3439_);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 3, v_inferType_3440_);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 4, v_getLevel_3441_);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 5, v_congrInfo_3442_);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 6, v_defEqI_3443_);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 7, v_extensions_3444_);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 8, v_issues_3445_);
                    lean_ctor_set(v_reuseFailAlloc_3481_, 9, v_canon_3446_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3481_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
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
                v_debug_3456_ = lean_ctor_get_uint8(
                    v___x_3455_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_3455_);
                v___x_3457_ =
                    l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateS_x27(
                        v_e_3432_,
                        v_subst_3433_,
                        v_debug_3456_,
                        v_share_3437_,
                    );
                v_fst_3458_ = lean_ctor_get(v___x_3457_, 0);
                lean_inc(v_fst_3458_);
                v_snd_3459_ = lean_ctor_get(v___x_3457_, 1);
                lean_inc(v_snd_3459_);
                lean_dec_ref(v___x_3457_);
                v___x_3460_ = lean_st_ref_take(v_a_3434_);
                v_maxFVar_3461_ = lean_ctor_get(v___x_3460_, 1);
                v_proofInstInfo_3462_ = lean_ctor_get(v___x_3460_, 2);
                v_inferType_3463_ = lean_ctor_get(v___x_3460_, 3);
                v_getLevel_3464_ = lean_ctor_get(v___x_3460_, 4);
                v_congrInfo_3465_ = lean_ctor_get(v___x_3460_, 5);
                v_defEqI_3466_ = lean_ctor_get(v___x_3460_, 6);
                v_extensions_3467_ = lean_ctor_get(v___x_3460_, 7);
                v_issues_3468_ = lean_ctor_get(v___x_3460_, 8);
                v_canon_3469_ = lean_ctor_get(v___x_3460_, 9);
                v_debug_3470_ = lean_ctor_get_uint8(
                    v___x_3460_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_3479_ = (!lean_is_exclusive(v___x_3460_)) as u8;
                if v_isSharedCheck_3479_ == 0 {
                    v_unused_3480_ = lean_ctor_get(v___x_3460_, 0);
                    lean_dec(v_unused_3480_);
                    v___x_3472_ = v___x_3460_;
                    v_isShared_3473_ = v_isSharedCheck_3479_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_canon_3469_);
                    lean_inc(v_issues_3468_);
                    lean_inc(v_extensions_3467_);
                    lean_inc(v_defEqI_3466_);
                    lean_inc(v_congrInfo_3465_);
                    lean_inc(v_getLevel_3464_);
                    lean_inc(v_inferType_3463_);
                    lean_inc(v_proofInstInfo_3462_);
                    lean_inc(v_maxFVar_3461_);
                    lean_dec(v___x_3460_);
                    v___x_3472_ = lean_box(0);
                    v_isShared_3473_ = v_isSharedCheck_3479_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3473_ == 0 {
                    lean_ctor_set(v___x_3472_, 0, v_snd_3459_);
                    v___x_3475_ = v___x_3472_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_snd_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_maxFVar_3461_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_proofInstInfo_3462_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 3, v_inferType_3463_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 4, v_getLevel_3464_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 5, v_congrInfo_3465_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 6, v_defEqI_3466_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 7, v_extensions_3467_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 8, v_issues_3468_);
                    lean_ctor_set(v_reuseFailAlloc_3478_, 9, v_canon_3469_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3478_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_3470_,
                    );
                    v___x_3475_ = v_reuseFailAlloc_3478_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3476_ = lean_st_ref_set(v_a_3434_, v___x_3475_);
                v___x_3477_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3477_, 0, v_fst_3458_);
                return v___x_3477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_instantiateS___redArg___boxed(
    mut v_e_3483_: *mut LeanObject,
    mut v_subst_3484_: *mut LeanObject,
    mut v_a_3485_: *mut LeanObject,
    mut v_a_3486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3487_: *mut LeanObject = core::ptr::null_mut();
    v_res_3487_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_3483_, v_subst_3484_, v_a_3485_);
    lean_dec(v_a_3485_);
    lean_dec_ref(v_subst_3484_);
    return v_res_3487_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateS(
    mut v_e_3488_: *mut LeanObject,
    mut v_subst_3489_: *mut LeanObject,
    mut v_a_3490_: *mut LeanObject,
    mut v_a_3491_: *mut LeanObject,
    mut v_a_3492_: *mut LeanObject,
    mut v_a_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    v___x_3497_ = l_Lean_Meta_Sym_instantiateS___redArg(v_e_3488_, v_subst_3489_, v_a_3491_);
    return v___x_3497_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateS___boxed(
    mut v_e_3498_: *mut LeanObject,
    mut v_subst_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
    mut v_a_3501_: *mut LeanObject,
    mut v_a_3502_: *mut LeanObject,
    mut v_a_3503_: *mut LeanObject,
    mut v_a_3504_: *mut LeanObject,
    mut v_a_3505_: *mut LeanObject,
    mut v_a_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3507_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3505_);
    lean_dec_ref(v_a_3504_);
    lean_dec(v_a_3503_);
    lean_dec_ref(v_a_3502_);
    lean_dec(v_a_3501_);
    lean_dec_ref(v_a_3500_);
    lean_dec_ref(v_subst_3499_);
    return v_res_3507_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(
    mut v_f_3508_: *mut LeanObject,
    mut v_a_3509_: *mut LeanObject,
    mut v___y_3510_: u8,
    mut v___y_3511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___y_3510_ == 0 {
                    v___y_3513_ = v___y_3511_;
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_f_3508_);
                    v___x_3516_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_f_3508_,
                        v___y_3510_,
                        v___y_3511_,
                    );
                    v_snd_3517_ = lean_ctor_get(v___x_3516_, 1);
                    lean_inc(v_snd_3517_);
                    lean_dec_ref(v___x_3516_);
                    lean_inc_ref(v_a_3509_);
                    v___x_3518_ = l_Lean_Meta_Sym_Internal_Builder_assertShared(
                        v_a_3509_,
                        v___y_3510_,
                        v_snd_3517_,
                    );
                    v_snd_3519_ = lean_ctor_get(v___x_3518_, 1);
                    lean_inc(v_snd_3519_);
                    lean_dec_ref(v___x_3518_);
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
    mut v_f_3520_: *mut LeanObject,
    mut v_a_3521_: *mut LeanObject,
    mut v___y_3522_: *mut LeanObject,
    mut v___y_3523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1584__boxed_3524_: u8 = 0;
    let mut v_res_3525_: *mut LeanObject = core::ptr::null_mut();
    v___y_1584__boxed_3524_ = (lean_unbox(v___y_3522_) as u8);
    v_res_3525_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_f_3520_, v_a_3521_, v___y_1584__boxed_3524_, v___y_3523_);
    return v_res_3525_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(
    mut v_revArgs_3526_: *mut LeanObject,
    mut v_start_3527_: *mut LeanObject,
    mut v_b_3528_: *mut LeanObject,
    mut v_i_3529_: *mut LeanObject,
    mut v___y_3530_: u8,
    mut v___y_3531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3532_ = lean_nat_dec_le(v_i_3529_, v_start_3527_);
                if v___x_3532_ == 0 {
                    v___x_3533_ = lean_unsigned_to_nat(1);
                    v_i_3534_ = lean_nat_sub(v_i_3529_, v___x_3533_);
                    lean_dec(v_i_3529_);
                    v___x_3535_ = l_Lean_instInhabitedExpr;
                    v___x_3536_ = lean_array_get_borrowed(v___x_3535_, v_revArgs_3526_, v_i_3534_);
                    lean_inc(v___x_3536_);
                    v___x_3537_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0_spec__0(v_b_3528_, v___x_3536_, v___y_3530_, v___y_3531_);
                    v_fst_3538_ = lean_ctor_get(v___x_3537_, 0);
                    lean_inc(v_fst_3538_);
                    v_snd_3539_ = lean_ctor_get(v___x_3537_, 1);
                    lean_inc(v_snd_3539_);
                    lean_dec_ref(v___x_3537_);
                    v_b_3528_ = v_fst_3538_;
                    v_i_3529_ = v_i_3534_;
                    v___y_3531_ = v_snd_3539_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_i_3529_);
                    v___x_3541_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3541_, 0, v_b_3528_);
                    lean_ctor_set(v___x_3541_, 1, v___y_3531_);
                    return v___x_3541_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0___boxed(
    mut v_revArgs_3542_: *mut LeanObject,
    mut v_start_3543_: *mut LeanObject,
    mut v_b_3544_: *mut LeanObject,
    mut v_i_3545_: *mut LeanObject,
    mut v___y_3546_: *mut LeanObject,
    mut v___y_3547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1608__boxed_3548_: u8 = 0;
    let mut v_res_3549_: *mut LeanObject = core::ptr::null_mut();
    v___y_1608__boxed_3548_ = (lean_unbox(v___y_3546_) as u8);
    v_res_3549_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_3542_, v_start_3543_, v_b_3544_, v_i_3545_, v___y_1608__boxed_3548_, v___y_3547_);
    lean_dec(v_start_3543_);
    lean_dec_ref(v_revArgs_3542_);
    return v_res_3549_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(
    mut v_revArgs_3550_: *mut LeanObject,
    mut v_sz_3551_: *mut LeanObject,
    mut v_e_3552_: *mut LeanObject,
    mut v_i_3553_: *mut LeanObject,
    mut v_a_3554_: u8,
    mut v_a_3555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_body_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: u8 = 0;
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_3552_) {
                6 => {
                    v_body_3556_ = lean_ctor_get(v_e_3552_, 2);
                    lean_inc_ref(v_body_3556_);
                    lean_dec_ref_known(v_e_3552_, 3);
                    v___x_3557_ = lean_unsigned_to_nat(1);
                    v___x_3558_ = lean_nat_add(v_i_3553_, v___x_3557_);
                    lean_dec(v_i_3553_);
                    v___x_3559_ = lean_nat_dec_lt(v___x_3558_, v_sz_3551_);
                    if v___x_3559_ == 0 {
                        lean_dec(v___x_3558_);
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
                    v_expr_3562_ = lean_ctor_get(v_e_3552_, 1);
                    lean_inc_ref(v_expr_3562_);
                    lean_dec_ref_known(v_e_3552_, 2);
                    v_e_3552_ = v_expr_3562_;
                    state = 0;
                    continue;
                }
                _ => {
                    v_n_3564_ = lean_nat_sub(v_sz_3551_, v_i_3553_);
                    lean_dec(v_i_3553_);
                    v___x_3565_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRangeS_x27(v_e_3552_, v_n_3564_, v_sz_3551_, v_revArgs_3550_, v_a_3554_, v_a_3555_);
                    v_fst_3566_ = lean_ctor_get(v___x_3565_, 0);
                    lean_inc(v_fst_3566_);
                    v_snd_3567_ = lean_ctor_get(v___x_3565_, 1);
                    lean_inc(v_snd_3567_);
                    lean_dec_ref(v___x_3565_);
                    v___x_3568_ = lean_unsigned_to_nat(0);
                    v___x_3569_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go_spec__0(v_revArgs_3550_, v___x_3568_, v_fst_3566_, v_n_3564_, v_a_3554_, v_snd_3567_);
                    return v___x_3569_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go___boxed(
    mut v_revArgs_3570_: *mut LeanObject,
    mut v_sz_3571_: *mut LeanObject,
    mut v_e_3572_: *mut LeanObject,
    mut v_i_3573_: *mut LeanObject,
    mut v_a_3574_: *mut LeanObject,
    mut v_a_3575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3576_: u8 = 0;
    let mut v_res_3577_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3576_ = (lean_unbox(v_a_3574_) as u8);
    v_res_3577_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27_go(
        v_revArgs_3570_,
        v_sz_3571_,
        v_e_3572_,
        v_i_3573_,
        v_a_boxed_3576_,
        v_a_3575_,
    );
    lean_dec(v_sz_3571_);
    lean_dec_ref(v_revArgs_3570_);
    return v_res_3577_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(
    mut v_f_3578_: *mut LeanObject,
    mut v_revArgs_3579_: *mut LeanObject,
    mut v_a_3580_: u8,
    mut v_a_3581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    v_sz_3582_ = lean_array_get_size(v_revArgs_3579_);
    v___x_3583_ = lean_unsigned_to_nat(0);
    v___x_3584_ = lean_nat_dec_eq(v_sz_3582_, v___x_3583_);
    if v___x_3584_ == 0 {
        let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
        v___x_3586_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3586_, 0, v_f_3578_);
        lean_ctor_set(v___x_3586_, 1, v_a_3581_);
        return v___x_3586_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27___boxed(
    mut v_f_3587_: *mut LeanObject,
    mut v_revArgs_3588_: *mut LeanObject,
    mut v_a_3589_: *mut LeanObject,
    mut v_a_3590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3591_: u8 = 0;
    let mut v_res_3592_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3591_ = (lean_unbox(v_a_3589_) as u8);
    v_res_3592_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(
        v_f_3587_,
        v_revArgs_3588_,
        v_a_boxed_3591_,
        v_a_3590_,
    );
    lean_dec_ref(v_revArgs_3588_);
    return v_res_3592_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_3593_: *mut LeanObject,
    mut v_x_3594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3600_: u8 = 0;
    let mut v_fst_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3594_) == 0 {
                    return v_x_3593_;
                } else {
                    v_key_3595_ = lean_ctor_get(v_x_3594_, 0);
                    v_value_3596_ = lean_ctor_get(v_x_3594_, 1);
                    v_tail_3597_ = lean_ctor_get(v_x_3594_, 2);
                    v_isSharedCheck_3624_ = (!lean_is_exclusive(v_x_3594_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v___x_3599_ = v_x_3594_;
                        v_isShared_3600_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3597_);
                        lean_inc(v_value_3596_);
                        lean_inc(v_key_3595_);
                        lean_dec(v_x_3594_);
                        v___x_3599_ = lean_box(0);
                        v_isShared_3600_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3601_ = lean_ctor_get(v_key_3595_, 0);
                v_snd_3602_ = lean_ctor_get(v_key_3595_, 1);
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
                lean_inc(v___x_3618_);
                if v_isShared_3600_ == 0 {
                    lean_ctor_set(v___x_3599_, 2, v___x_3618_);
                    v___x_3620_ = v___x_3599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_key_3595_);
                    lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_value_3596_);
                    lean_ctor_set(v_reuseFailAlloc_3623_, 2, v___x_3618_);
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
    mut v_i_3625_: *mut LeanObject,
    mut v_source_3626_: *mut LeanObject,
    mut v_target_3627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v_es_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3628_ = lean_array_get_size(v_source_3626_);
                v___x_3629_ = lean_nat_dec_lt(v_i_3625_, v___x_3628_);
                if v___x_3629_ == 0 {
                    lean_dec_ref(v_source_3626_);
                    lean_dec(v_i_3625_);
                    return v_target_3627_;
                } else {
                    v_es_3630_ = lean_array_fget(v_source_3626_, v_i_3625_);
                    v___x_3631_ = lean_box(0);
                    v_source_3632_ = lean_array_fset(v_source_3626_, v_i_3625_, v___x_3631_);
                    v_target_3633_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3627_, v_es_3630_);
                    v___x_3634_ = lean_unsigned_to_nat(1);
                    v___x_3635_ = lean_nat_add(v_i_3625_, v___x_3634_);
                    lean_dec(v_i_3625_);
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
    mut v_data_3637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    v___x_3638_ = lean_array_get_size(v_data_3637_);
    v___x_3639_ = lean_unsigned_to_nat(2);
    v_nbuckets_3640_ = lean_nat_mul(v___x_3638_, v___x_3639_);
    v___x_3641_ = lean_unsigned_to_nat(0);
    v___x_3642_ = lean_box(0);
    v___x_3643_ = lean_mk_array(v_nbuckets_3640_, v___x_3642_);
    v___x_3644_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v___x_3641_, v_data_3637_, v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(
    mut v_a_3645_: *mut LeanObject,
    mut v_b_3646_: *mut LeanObject,
    mut v_x_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___y_3655_: u8 = 0;
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: u8 = 0;
    let mut v___x_3668_: u8 = 0;
    let mut v_isSharedCheck_3669_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3647_) == 0 {
                    lean_dec(v_b_3646_);
                    lean_dec_ref(v_a_3645_);
                    return v_x_3647_;
                } else {
                    v_key_3648_ = lean_ctor_get(v_x_3647_, 0);
                    v_value_3649_ = lean_ctor_get(v_x_3647_, 1);
                    v_tail_3650_ = lean_ctor_get(v_x_3647_, 2);
                    v_isSharedCheck_3669_ = (!lean_is_exclusive(v_x_3647_)) as u8;
                    if v_isSharedCheck_3669_ == 0 {
                        v___x_3652_ = v_x_3647_;
                        v_isShared_3653_ = v_isSharedCheck_3669_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3650_);
                        lean_inc(v_value_3649_);
                        lean_inc(v_key_3648_);
                        lean_dec(v_x_3647_);
                        v___x_3652_ = lean_box(0);
                        v_isShared_3653_ = v_isSharedCheck_3669_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3663_ = lean_ctor_get(v_key_3648_, 0);
                v_snd_3664_ = lean_ctor_get(v_key_3648_, 1);
                v_fst_3665_ = lean_ctor_get(v_a_3645_, 0);
                v_snd_3666_ = lean_ctor_get(v_a_3645_, 1);
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
                        lean_ctor_set(v___x_3652_, 2, v___x_3656_);
                        v___x_3658_ = v___x_3652_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3659_, 0, v_key_3648_);
                        lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_value_3649_);
                        lean_ctor_set(v_reuseFailAlloc_3659_, 2, v___x_3656_);
                        v___x_3658_ = v_reuseFailAlloc_3659_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3649_);
                    lean_dec(v_key_3648_);
                    if v_isShared_3653_ == 0 {
                        lean_ctor_set(v___x_3652_, 1, v_b_3646_);
                        lean_ctor_set(v___x_3652_, 0, v_a_3645_);
                        v___x_3661_ = v___x_3652_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3645_);
                        lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_b_3646_);
                        lean_ctor_set(v_reuseFailAlloc_3662_, 2, v_tail_3650_);
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
    mut v_a_3670_: *mut LeanObject,
    mut v_x_3671_: *mut LeanObject,
) -> u8 {
    let mut v___x_3672_: u8 = 0;
    let mut v_key_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3676_: u8 = 0;
    let mut v_fst_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3671_) == 0 {
                    v___x_3672_ = 0;
                    return v___x_3672_;
                } else {
                    v_key_3673_ = lean_ctor_get(v_x_3671_, 0);
                    v_tail_3674_ = lean_ctor_get(v_x_3671_, 2);
                    v_fst_3678_ = lean_ctor_get(v_key_3673_, 0);
                    v_snd_3679_ = lean_ctor_get(v_key_3673_, 1);
                    v_fst_3680_ = lean_ctor_get(v_a_3670_, 0);
                    v_snd_3681_ = lean_ctor_get(v_a_3670_, 1);
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
    mut v_a_3684_: *mut LeanObject,
    mut v_x_3685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3686_: u8 = 0;
    let mut v_r_3687_: *mut LeanObject = core::ptr::null_mut();
    v_res_3686_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_3684_, v_x_3685_);
    lean_dec(v_x_3685_);
    lean_dec_ref(v_a_3684_);
    v_r_3687_ = lean_box((v_res_3686_) as usize);
    return v_r_3687_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(
    mut v_m_3688_: *mut LeanObject,
    mut v_a_3689_: *mut LeanObject,
    mut v_b_3690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v_fst_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: u8 = 0;
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: u8 = 0;
    let mut v_val_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3691_ = lean_ctor_get(v_m_3688_, 0);
                v_buckets_3692_ = lean_ctor_get(v_m_3688_, 1);
                v_isSharedCheck_3739_ = (!lean_is_exclusive(v_m_3688_)) as u8;
                if v_isSharedCheck_3739_ == 0 {
                    v___x_3694_ = v_m_3688_;
                    v_isShared_3695_ = v_isSharedCheck_3739_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3692_);
                    lean_inc(v_size_3691_);
                    lean_dec(v_m_3688_);
                    v___x_3694_ = lean_box(0);
                    v_isShared_3695_ = v_isSharedCheck_3739_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3696_ = lean_ctor_get(v_a_3689_, 0);
                v_snd_3697_ = lean_ctor_get(v_a_3689_, 1);
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
                    v___x_3715_ = lean_unsigned_to_nat(1);
                    v_size_x27_3716_ = lean_nat_add(v_size_3691_, v___x_3715_);
                    lean_dec(v_size_3691_);
                    lean_inc(v_bkt_3713_);
                    v___x_3717_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3717_, 0, v_a_3689_);
                    lean_ctor_set(v___x_3717_, 1, v_b_3690_);
                    lean_ctor_set(v___x_3717_, 2, v_bkt_3713_);
                    v_buckets_x27_3718_ =
                        lean_array_uset(v_buckets_3692_, v___x_3712_, v___x_3717_);
                    v___x_3719_ = lean_unsigned_to_nat(4);
                    v___x_3720_ = lean_nat_mul(v_size_x27_3716_, v___x_3719_);
                    v___x_3721_ = lean_unsigned_to_nat(3);
                    v___x_3722_ = lean_nat_div(v___x_3720_, v___x_3721_);
                    lean_dec(v___x_3720_);
                    v___x_3723_ = lean_array_get_size(v_buckets_x27_3718_);
                    v___x_3724_ = lean_nat_dec_le(v___x_3722_, v___x_3723_);
                    lean_dec(v___x_3722_);
                    if v___x_3724_ == 0 {
                        v_val_3725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_buckets_x27_3718_);
                        if v_isShared_3695_ == 0 {
                            lean_ctor_set(v___x_3694_, 1, v_val_3725_);
                            lean_ctor_set(v___x_3694_, 0, v_size_x27_3716_);
                            v___x_3727_ = v___x_3694_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_size_x27_3716_);
                            lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_val_3725_);
                            v___x_3727_ = v_reuseFailAlloc_3728_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3695_ == 0 {
                            lean_ctor_set(v___x_3694_, 1, v_buckets_x27_3718_);
                            lean_ctor_set(v___x_3694_, 0, v_size_x27_3716_);
                            v___x_3730_ = v___x_3694_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_size_x27_3716_);
                            lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_buckets_x27_3718_);
                            v___x_3730_ = v_reuseFailAlloc_3731_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3713_);
                    v___x_3732_ = lean_box(0);
                    v_buckets_x27_3733_ =
                        lean_array_uset(v_buckets_3692_, v___x_3712_, v___x_3732_);
                    v___x_3734_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_3689_, v_b_3690_, v_bkt_3713_);
                    v___x_3735_ = lean_array_uset(v_buckets_x27_3733_, v___x_3712_, v___x_3734_);
                    if v_isShared_3695_ == 0 {
                        lean_ctor_set(v___x_3694_, 1, v___x_3735_);
                        v___x_3737_ = v___x_3694_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_size_3691_);
                        lean_ctor_set(v_reuseFailAlloc_3738_, 1, v___x_3735_);
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
    mut v_key_3740_: *mut LeanObject,
    mut v_r_3741_: *mut LeanObject,
    mut v_a_3742_: *mut LeanObject,
    mut v_a_3743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_r_3741_);
    v___x_3744_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_a_3742_, v_key_3740_, v_r_3741_);
    v___x_3745_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3745_, 0, v_r_3741_);
    lean_ctor_set(v___x_3745_, 1, v___x_3744_);
    v___x_3746_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3746_, 0, v___x_3745_);
    lean_ctor_set(v___x_3746_, 1, v_a_3743_);
    return v___x_3746_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save(
    mut v_key_3747_: *mut LeanObject,
    mut v_r_3748_: *mut LeanObject,
    mut v_a_3749_: *mut LeanObject,
    mut v_a_3750_: u8,
    mut v_a_3751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    v___x_3752_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
        v_key_3747_,
        v_r_3748_,
        v_a_3749_,
        v_a_3751_,
    );
    return v___x_3752_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___boxed(
    mut v_key_3753_: *mut LeanObject,
    mut v_r_3754_: *mut LeanObject,
    mut v_a_3755_: *mut LeanObject,
    mut v_a_3756_: *mut LeanObject,
    mut v_a_3757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3758_: u8 = 0;
    let mut v_res_3759_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3758_ = (lean_unbox(v_a_3756_) as u8);
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
    mut v_00_u03b2_3760_: *mut LeanObject,
    mut v_m_3761_: *mut LeanObject,
    mut v_a_3762_: *mut LeanObject,
    mut v_b_3763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    v___x_3764_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0___redArg(v_m_3761_, v_a_3762_, v_b_3763_);
    return v___x_3764_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(
    mut v_00_u03b2_3765_: *mut LeanObject,
    mut v_a_3766_: *mut LeanObject,
    mut v_x_3767_: *mut LeanObject,
) -> u8 {
    let mut v___x_3768_: u8 = 0;
    v___x_3768_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___redArg(v_a_3766_, v_x_3767_);
    return v___x_3768_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0___boxed(
    mut v_00_u03b2_3769_: *mut LeanObject,
    mut v_a_3770_: *mut LeanObject,
    mut v_x_3771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3772_: u8 = 0;
    let mut v_r_3773_: *mut LeanObject = core::ptr::null_mut();
    v_res_3772_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__0(v_00_u03b2_3769_, v_a_3770_, v_x_3771_);
    lean_dec(v_x_3771_);
    lean_dec_ref(v_a_3770_);
    v_r_3773_ = lean_box((v_res_3772_) as usize);
    return v_r_3773_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1(
    mut v_00_u03b2_3774_: *mut LeanObject,
    mut v_data_3775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1___redArg(v_data_3775_);
    return v___x_3776_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2(
    mut v_00_u03b2_3777_: *mut LeanObject,
    mut v_a_3778_: *mut LeanObject,
    mut v_b_3779_: *mut LeanObject,
    mut v_x_3780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    v___x_3781_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__2___redArg(v_a_3778_, v_b_3779_, v_x_3780_);
    return v___x_3781_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3782_: *mut LeanObject,
    mut v_i_3783_: *mut LeanObject,
    mut v_source_3784_: *mut LeanObject,
    mut v_target_3785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    v___x_3786_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2___redArg(v_i_3783_, v_source_3784_, v_target_3785_);
    return v___x_3786_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3787_: *mut LeanObject,
    mut v_x_3788_: *mut LeanObject,
    mut v_x_3789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    v___x_3790_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save_spec__0_spec__1_spec__2_spec__3___redArg(v_x_3788_, v_x_3789_);
    return v___x_3790_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(
    mut v_idx_3791_: *mut LeanObject,
    mut v___y_3792_: *mut LeanObject,
    mut v___y_3793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3800_: u8 = 0;
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3794_ = l_Lean_Expr_bvar___override(v_idx_3791_);
                v___x_3795_ =
                    l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v___x_3794_, v___y_3793_);
                v_fst_3796_ = lean_ctor_get(v___x_3795_, 0);
                v_snd_3797_ = lean_ctor_get(v___x_3795_, 1);
                v_isSharedCheck_3805_ = (!lean_is_exclusive(v___x_3795_)) as u8;
                if v_isSharedCheck_3805_ == 0 {
                    v___x_3799_ = v___x_3795_;
                    v_isShared_3800_ = v_isSharedCheck_3805_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_3797_);
                    lean_inc(v_fst_3796_);
                    lean_dec(v___x_3795_);
                    v___x_3799_ = lean_box(0);
                    v_isShared_3800_ = v_isSharedCheck_3805_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3800_ == 0 {
                    lean_ctor_set(v___x_3799_, 1, v___y_3792_);
                    v___x_3802_ = v___x_3799_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_fst_3796_);
                    lean_ctor_set(v_reuseFailAlloc_3804_, 1, v___y_3792_);
                    v___x_3802_ = v_reuseFailAlloc_3804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3803_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3803_, 0, v___x_3802_);
                lean_ctor_set(v___x_3803_, 1, v_snd_3797_);
                return v___x_3803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(
    mut v_idx_3806_: *mut LeanObject,
    mut v___y_3807_: *mut LeanObject,
    mut v___y_3808_: u8,
    mut v___y_3809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    v___x_3810_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v_idx_3806_, v___y_3807_, v___y_3809_);
    return v___x_3810_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___boxed(
    mut v_idx_3811_: *mut LeanObject,
    mut v___y_3812_: *mut LeanObject,
    mut v___y_3813_: *mut LeanObject,
    mut v___y_3814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1291__boxed_3815_: u8 = 0;
    let mut v_res_3816_: *mut LeanObject = core::ptr::null_mut();
    v___y_1291__boxed_3815_ = (lean_unbox(v___y_3813_) as u8);
    v_res_3816_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0(v_idx_3811_, v___y_3812_, v___y_1291__boxed_3815_, v___y_3814_);
    return v_res_3816_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(
    mut v_subst_3817_: *mut LeanObject,
    mut v_e_3818_: *mut LeanObject,
    mut v_bidx_3819_: *mut LeanObject,
    mut v_offset_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
    mut v_a_3822_: u8,
    mut v_a_3823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3824_ = lean_nat_dec_le(v_offset_3820_, v_bidx_3819_);
                if v___x_3824_ == 0 {
                    v___x_3825_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3825_, 0, v_e_3818_);
                    lean_ctor_set(v___x_3825_, 1, v_a_3821_);
                    v___x_3826_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3826_, 0, v___x_3825_);
                    lean_ctor_set(v___x_3826_, 1, v_a_3823_);
                    return v___x_3826_;
                } else {
                    lean_dec_ref(v_e_3818_);
                    v_n_3827_ = lean_array_get_size(v_subst_3817_);
                    v___x_3828_ = lean_nat_add(v_offset_3820_, v_n_3827_);
                    v___x_3829_ = lean_nat_dec_lt(v_bidx_3819_, v___x_3828_);
                    lean_dec(v___x_3828_);
                    if v___x_3829_ == 0 {
                        v___x_3830_ = lean_nat_sub(v_bidx_3819_, v_n_3827_);
                        v___x_3831_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00__private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar_spec__0___redArg(v___x_3830_, v_a_3821_, v_a_3823_);
                        return v___x_3831_;
                    } else {
                        v___x_3832_ = lean_nat_sub(v_bidx_3819_, v_offset_3820_);
                        v___x_3833_ = lean_nat_sub(v_n_3827_, v___x_3832_);
                        lean_dec(v___x_3832_);
                        v___x_3834_ = lean_unsigned_to_nat(1);
                        v___x_3835_ = lean_nat_sub(v___x_3833_, v___x_3834_);
                        lean_dec(v___x_3833_);
                        v_v_3836_ = lean_array_fget_borrowed(v_subst_3817_, v___x_3835_);
                        lean_dec(v___x_3835_);
                        v___x_3837_ = lean_unsigned_to_nat(0);
                        lean_inc(v_v_3836_);
                        v___x_3838_ = l_Lean_Meta_Sym_liftLooseBVarsS_x27(
                            v_v_3836_,
                            v___x_3837_,
                            v_offset_3820_,
                            v_a_3822_,
                            v_a_3823_,
                        );
                        v_fst_3839_ = lean_ctor_get(v___x_3838_, 0);
                        v_snd_3840_ = lean_ctor_get(v___x_3838_, 1);
                        v_isSharedCheck_3848_ = (!lean_is_exclusive(v___x_3838_)) as u8;
                        if v_isSharedCheck_3848_ == 0 {
                            v___x_3842_ = v___x_3838_;
                            v_isShared_3843_ = v_isSharedCheck_3848_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_3840_);
                            lean_inc(v_fst_3839_);
                            lean_dec(v___x_3838_);
                            v___x_3842_ = lean_box(0);
                            v_isShared_3843_ = v_isSharedCheck_3848_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3843_ == 0 {
                    lean_ctor_set(v___x_3842_, 1, v_a_3821_);
                    v___x_3845_ = v___x_3842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_fst_3839_);
                    lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_a_3821_);
                    v___x_3845_ = v_reuseFailAlloc_3847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3846_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3846_, 0, v___x_3845_);
                lean_ctor_set(v___x_3846_, 1, v_snd_3840_);
                return v___x_3846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar___boxed(
    mut v_subst_3849_: *mut LeanObject,
    mut v_e_3850_: *mut LeanObject,
    mut v_bidx_3851_: *mut LeanObject,
    mut v_offset_3852_: *mut LeanObject,
    mut v_a_3853_: *mut LeanObject,
    mut v_a_3854_: *mut LeanObject,
    mut v_a_3855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_3856_: u8 = 0;
    let mut v_res_3857_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_3856_ = (lean_unbox(v_a_3854_) as u8);
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
    lean_dec(v_offset_3852_);
    lean_dec(v_bidx_3851_);
    lean_dec_ref(v_subst_3849_);
    return v_res_3857_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    v___x_3861_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__2;
    v___x_3862_ = lean_unsigned_to_nat(25);
    v___x_3863_ = lean_unsigned_to_nat(148);
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
-> *mut LeanObject {
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    v___x_3868_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_3869_ = lean_unsigned_to_nat(11);
    v___x_3870_ = lean_unsigned_to_nat(165);
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
    mut v_subst_3874_: *mut LeanObject,
    mut v_e_3875_: *mut LeanObject,
    mut v_f_3876_: *mut LeanObject,
    mut v_argsRev_3877_: *mut LeanObject,
    mut v_offset_3878_: *mut LeanObject,
    mut v_modified_3879_: u8,
    mut v_a_3880_: *mut LeanObject,
    mut v_a_3881_: u8,
    mut v_a_3882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: u8 = 0;
    let mut v___x_3892_: u8 = 0;
    let mut v_deBruijnIndex_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v_fst_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3921_: u8 = 0;
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_f_3876_) {
                    5 => {
                        v_fn_3883_ = lean_ctor_get(v_f_3876_, 0);
                        lean_inc_ref(v_fn_3883_);
                        v_arg_3884_ = lean_ctor_get(v_f_3876_, 1);
                        lean_inc_ref_n(v_arg_3884_, 2);
                        lean_dec_ref_known(v_f_3876_, 2);
                        lean_inc(v_offset_3878_);
                        v___x_3885_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3874_, v_arg_3884_, v_offset_3878_, v_a_3880_, v_a_3881_, v_a_3882_);
                        v_fst_3886_ = lean_ctor_get(v___x_3885_, 0);
                        lean_inc(v_fst_3886_);
                        v_snd_3887_ = lean_ctor_get(v___x_3885_, 1);
                        lean_inc(v_snd_3887_);
                        lean_dec_ref(v___x_3885_);
                        v_fst_3888_ = lean_ctor_get(v_fst_3886_, 0);
                        lean_inc_n(v_fst_3888_, 2);
                        v_snd_3889_ = lean_ctor_get(v_fst_3886_, 1);
                        lean_inc(v_snd_3889_);
                        lean_dec(v_fst_3886_);
                        v___x_3890_ = lean_array_push(v_argsRev_3877_, v_fst_3888_);
                        if v_modified_3879_ == 0 {
                            v___x_3891_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_3884_, v_fst_3888_);
                            lean_dec(v_fst_3888_);
                            lean_dec_ref(v_arg_3884_);
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
                            lean_dec(v_fst_3888_);
                            lean_dec_ref(v_arg_3884_);
                            v_f_3876_ = v_fn_3883_;
                            v_argsRev_3877_ = v___x_3890_;
                            v_a_3880_ = v_snd_3889_;
                            v_a_3882_ = v_snd_3887_;
                            state = 0;
                            continue;
                        }
                    }
                    0 => {
                        v_deBruijnIndex_3896_ = lean_ctor_get(v_f_3876_, 0);
                        lean_inc_ref(v_f_3876_);
                        v___x_3897_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_3874_, v_f_3876_, v_deBruijnIndex_3896_, v_offset_3878_, v_a_3880_, v_a_3881_, v_a_3882_);
                        lean_dec(v_offset_3878_);
                        v_fst_3898_ = lean_ctor_get(v___x_3897_, 0);
                        v_snd_3899_ = lean_ctor_get(v___x_3897_, 1);
                        v_isSharedCheck_3928_ = (!lean_is_exclusive(v___x_3897_)) as u8;
                        if v_isSharedCheck_3928_ == 0 {
                            v___x_3901_ = v___x_3897_;
                            v_isShared_3902_ = v_isSharedCheck_3928_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_3899_);
                            lean_inc(v_fst_3898_);
                            lean_dec(v___x_3897_);
                            v___x_3901_ = lean_box(0);
                            v_isShared_3902_ = v_isSharedCheck_3928_;
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_offset_3878_);
                        lean_dec_ref(v_argsRev_3877_);
                        lean_dec_ref(v_f_3876_);
                        lean_dec_ref(v_e_3875_);
                        v___x_3929_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1_once), _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___closed__1);
                        v___x_3930_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_3929_, v_a_3880_, v_a_3881_, v_a_3882_);
                        return v___x_3930_;
                    }
                }
            }
            1 => {
                v_fst_3903_ = lean_ctor_get(v_fst_3898_, 0);
                v_snd_3904_ = lean_ctor_get(v_fst_3898_, 1);
                v_isSharedCheck_3927_ = (!lean_is_exclusive(v_fst_3898_)) as u8;
                if v_isSharedCheck_3927_ == 0 {
                    v___x_3906_ = v_fst_3898_;
                    v_isShared_3907_ = v_isSharedCheck_3927_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3904_);
                    lean_inc(v_fst_3903_);
                    lean_dec(v_fst_3898_);
                    v___x_3906_ = lean_box(0);
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
                    lean_dec_ref_known(v_f_3876_, 1);
                    if v___x_3922_ == 0 {
                        lean_del_object(v___x_3901_);
                        lean_dec_ref(v_e_3875_);
                        state = 3;
                        continue;
                    } else {
                        lean_del_object(v___x_3906_);
                        lean_dec(v_fst_3903_);
                        lean_dec_ref(v_argsRev_3877_);
                        if v_isShared_3902_ == 0 {
                            lean_ctor_set(v___x_3901_, 1, v_snd_3904_);
                            lean_ctor_set(v___x_3901_, 0, v_e_3875_);
                            v___x_3924_ = v___x_3901_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_e_3875_);
                            lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_snd_3904_);
                            v___x_3924_ = v_reuseFailAlloc_3926_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3901_);
                    lean_dec_ref_known(v_f_3876_, 1);
                    lean_dec_ref(v_e_3875_);
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
                lean_dec_ref(v_argsRev_3877_);
                v_fst_3910_ = lean_ctor_get(v___x_3909_, 0);
                v_snd_3911_ = lean_ctor_get(v___x_3909_, 1);
                v_isSharedCheck_3921_ = (!lean_is_exclusive(v___x_3909_)) as u8;
                if v_isSharedCheck_3921_ == 0 {
                    v___x_3913_ = v___x_3909_;
                    v_isShared_3914_ = v_isSharedCheck_3921_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_3911_);
                    lean_inc(v_fst_3910_);
                    lean_dec(v___x_3909_);
                    v___x_3913_ = lean_box(0);
                    v_isShared_3914_ = v_isSharedCheck_3921_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3914_ == 0 {
                    lean_ctor_set(v___x_3913_, 1, v_snd_3904_);
                    v___x_3916_ = v___x_3913_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_fst_3910_);
                    lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_snd_3904_);
                    v___x_3916_ = v_reuseFailAlloc_3920_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3907_ == 0 {
                    lean_ctor_set(v___x_3906_, 1, v_snd_3911_);
                    lean_ctor_set(v___x_3906_, 0, v___x_3916_);
                    v___x_3918_ = v___x_3906_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
                    lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_snd_3911_);
                    v___x_3918_ = v_reuseFailAlloc_3919_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3918_;
            }
            7 => {
                v___x_3925_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3925_, 0, v___x_3924_);
                lean_ctor_set(v___x_3925_, 1, v_snd_3899_);
                return v___x_3925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(
    mut v_subst_3931_: *mut LeanObject,
    mut v_e_3932_: *mut LeanObject,
    mut v_f_3933_: *mut LeanObject,
    mut v_arg_3934_: *mut LeanObject,
    mut v_offset_3935_: *mut LeanObject,
    mut v_a_3936_: *mut LeanObject,
    mut v_a_3937_: u8,
    mut v_a_3938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3951_: u8 = 0;
    let mut v_fst_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___y_3958_: u8 = 0;
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3969_: u8 = 0;
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v_isSharedCheck_3973_: u8 = 0;
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: u8 = 0;
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_offset_3935_);
                lean_inc_ref(v_arg_3934_);
                v___x_3939_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3931_, v_arg_3934_, v_offset_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
                v_fst_3940_ = lean_ctor_get(v___x_3939_, 0);
                lean_inc(v_fst_3940_);
                v_snd_3941_ = lean_ctor_get(v___x_3939_, 1);
                lean_inc(v_snd_3941_);
                lean_dec_ref(v___x_3939_);
                v_fst_3942_ = lean_ctor_get(v_fst_3940_, 0);
                lean_inc(v_fst_3942_);
                v_snd_3943_ = lean_ctor_get(v_fst_3940_, 1);
                lean_inc(v_snd_3943_);
                lean_dec(v_fst_3940_);
                v___x_3944_ = l_Lean_Expr_getAppFn(v_f_3933_);
                v___x_3945_ = l_Lean_Expr_isBVar(v___x_3944_);
                lean_dec_ref(v___x_3944_);
                if v___x_3945_ == 0 {
                    lean_dec_ref(v_arg_3934_);
                    v___x_3946_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_3931_, v_f_3933_, v_offset_3935_, v_snd_3943_, v_a_3937_, v_snd_3941_);
                    v_fst_3947_ = lean_ctor_get(v___x_3946_, 0);
                    v_snd_3948_ = lean_ctor_get(v___x_3946_, 1);
                    v_isSharedCheck_3973_ = (!lean_is_exclusive(v___x_3946_)) as u8;
                    if v_isSharedCheck_3973_ == 0 {
                        v___x_3950_ = v___x_3946_;
                        v_isShared_3951_ = v_isSharedCheck_3973_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3948_);
                        lean_inc(v_fst_3947_);
                        lean_dec(v___x_3946_);
                        v___x_3950_ = lean_box(0);
                        v_isShared_3951_ = v_isSharedCheck_3973_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3974_ = lean_unsigned_to_nat(1);
                    v___x_3975_ = lean_mk_empty_array_with_capacity(v___x_3974_);
                    lean_inc(v_fst_3942_);
                    v___x_3976_ = lean_array_push(v___x_3975_, v_fst_3942_);
                    v___x_3977_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_3934_,
                            v_fst_3942_,
                        );
                    lean_dec(v_fst_3942_);
                    lean_dec_ref(v_arg_3934_);
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
                v_fst_3952_ = lean_ctor_get(v_fst_3947_, 0);
                v_snd_3953_ = lean_ctor_get(v_fst_3947_, 1);
                v_isSharedCheck_3972_ = (!lean_is_exclusive(v_fst_3947_)) as u8;
                if v_isSharedCheck_3972_ == 0 {
                    v___x_3955_ = v_fst_3947_;
                    v_isShared_3956_ = v_isSharedCheck_3972_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3953_);
                    lean_inc(v_fst_3952_);
                    lean_dec(v_fst_3947_);
                    v___x_3955_ = lean_box(0);
                    v_isShared_3956_ = v_isSharedCheck_3972_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v_e_3932_) == 5 {
                    v_fn_3966_ = lean_ctor_get(v_e_3932_, 0);
                    v_arg_3967_ = lean_ctor_get(v_e_3932_, 1);
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
                    lean_del_object(v___x_3955_);
                    lean_dec(v_fst_3952_);
                    lean_del_object(v___x_3950_);
                    lean_dec(v_fst_3942_);
                    lean_dec_ref(v_e_3932_);
                    v___x_3970_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3_once), _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___closed__3);
                    v___x_3971_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_3970_, v_snd_3953_, v_a_3937_, v_snd_3948_);
                    return v___x_3971_;
                }
            }
            3 => {
                if v___y_3958_ == 0 {
                    lean_del_object(v___x_3955_);
                    lean_del_object(v___x_3950_);
                    lean_dec_ref(v_e_3932_);
                    v___x_3959_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_3952_, v_fst_3942_, v_snd_3953_, v_a_3937_, v_snd_3948_);
                    return v___x_3959_;
                } else {
                    lean_dec(v_fst_3952_);
                    lean_dec(v_fst_3942_);
                    if v_isShared_3956_ == 0 {
                        lean_ctor_set(v___x_3955_, 0, v_e_3932_);
                        v___x_3961_ = v___x_3955_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_e_3932_);
                        lean_ctor_set(v_reuseFailAlloc_3965_, 1, v_snd_3953_);
                        v___x_3961_ = v_reuseFailAlloc_3965_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3951_ == 0 {
                    lean_ctor_set(v___x_3950_, 0, v___x_3961_);
                    v___x_3963_ = v___x_3950_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3961_);
                    lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_snd_3948_);
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
-> *mut LeanObject {
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    v___x_3982_ = l___private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2___closed__2;
    v___x_3983_ = lean_unsigned_to_nat(59);
    v___x_3984_ = lean_unsigned_to_nat(176);
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
    mut v_subst_3988_: *mut LeanObject,
    mut v_e_3989_: *mut LeanObject,
    mut v_offset_3990_: *mut LeanObject,
    mut v_a_3991_: *mut LeanObject,
    mut v_a_3992_: u8,
    mut v_a_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_deBruijnIndex_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4002_: u8 = 0;
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4015_: u8 = 0;
    let mut v_fst_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4020_: u8 = 0;
    let mut v___y_4022_: u8 = 0;
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: u8 = 0;
    let mut v___x_4031_: u8 = 0;
    let mut v_isSharedCheck_4032_: u8 = 0;
    let mut v_isSharedCheck_4033_: u8 = 0;
    let mut v_binderName_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4037_: u8 = 0;
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4050_: u8 = 0;
    let mut v_fst_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4055_: u8 = 0;
    let mut v___y_4057_: u8 = 0;
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: u8 = 0;
    let mut v___x_4066_: u8 = 0;
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut v_declName_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_4073_: u8 = 0;
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v_fst_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4096_: u8 = 0;
    let mut v___y_4098_: u8 = 0;
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: u8 = 0;
    let mut v_isSharedCheck_4110_: u8 = 0;
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut v_data_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4119_: u8 = 0;
    let mut v_fst_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4133_: u8 = 0;
    let mut v_isSharedCheck_4134_: u8 = 0;
    let mut v_typeName_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4143_: u8 = 0;
    let mut v_fst_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4148_: u8 = 0;
    let mut v___x_4149_: u8 = 0;
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4157_: u8 = 0;
    let mut v_isSharedCheck_4158_: u8 = 0;
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_3989_) {
                0 => {
                    v_deBruijnIndex_3994_ = lean_ctor_get(v_e_3989_, 0);
                    lean_inc(v_deBruijnIndex_3994_);
                    v___x_3995_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_3988_, v_e_3989_, v_deBruijnIndex_3994_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    lean_dec(v_offset_3990_);
                    lean_dec(v_deBruijnIndex_3994_);
                    return v___x_3995_;
                }
                5 => {
                    v_fn_3996_ = lean_ctor_get(v_e_3989_, 0);
                    lean_inc_ref(v_fn_3996_);
                    v_arg_3997_ = lean_ctor_get(v_e_3989_, 1);
                    lean_inc_ref(v_arg_3997_);
                    v___x_3998_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_3988_, v_e_3989_, v_fn_3996_, v_arg_3997_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    return v___x_3998_;
                }
                6 => {
                    v_binderName_3999_ = lean_ctor_get(v_e_3989_, 0);
                    v_binderType_4000_ = lean_ctor_get(v_e_3989_, 1);
                    v_body_4001_ = lean_ctor_get(v_e_3989_, 2);
                    v_binderInfo_4002_ = lean_ctor_get_uint8(
                        v_e_3989_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_3990_);
                    lean_inc_ref(v_binderType_4000_);
                    v___x_4003_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_binderType_4000_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    v_fst_4004_ = lean_ctor_get(v___x_4003_, 0);
                    lean_inc(v_fst_4004_);
                    v_snd_4005_ = lean_ctor_get(v___x_4003_, 1);
                    lean_inc(v_snd_4005_);
                    lean_dec_ref(v___x_4003_);
                    v_fst_4006_ = lean_ctor_get(v_fst_4004_, 0);
                    lean_inc(v_fst_4006_);
                    v_snd_4007_ = lean_ctor_get(v_fst_4004_, 1);
                    lean_inc(v_snd_4007_);
                    lean_dec(v_fst_4004_);
                    v___x_4008_ = lean_unsigned_to_nat(1);
                    v___x_4009_ = lean_nat_add(v_offset_3990_, v___x_4008_);
                    lean_dec(v_offset_3990_);
                    lean_inc_ref(v_body_4001_);
                    v___x_4010_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_body_4001_, v___x_4009_, v_snd_4007_, v_a_3992_, v_snd_4005_);
                    v_fst_4011_ = lean_ctor_get(v___x_4010_, 0);
                    v_snd_4012_ = lean_ctor_get(v___x_4010_, 1);
                    v_isSharedCheck_4033_ = (!lean_is_exclusive(v___x_4010_)) as u8;
                    if v_isSharedCheck_4033_ == 0 {
                        v___x_4014_ = v___x_4010_;
                        v_isShared_4015_ = v_isSharedCheck_4033_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4012_);
                        lean_inc(v_fst_4011_);
                        lean_dec(v___x_4010_);
                        v___x_4014_ = lean_box(0);
                        v_isShared_4015_ = v_isSharedCheck_4033_;
                        state = 1;
                        continue;
                    }
                }
                7 => {
                    v_binderName_4034_ = lean_ctor_get(v_e_3989_, 0);
                    v_binderType_4035_ = lean_ctor_get(v_e_3989_, 1);
                    v_body_4036_ = lean_ctor_get(v_e_3989_, 2);
                    v_binderInfo_4037_ = lean_ctor_get_uint8(
                        v_e_3989_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc(v_offset_3990_);
                    lean_inc_ref(v_binderType_4035_);
                    v___x_4038_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_binderType_4035_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    v_fst_4039_ = lean_ctor_get(v___x_4038_, 0);
                    lean_inc(v_fst_4039_);
                    v_snd_4040_ = lean_ctor_get(v___x_4038_, 1);
                    lean_inc(v_snd_4040_);
                    lean_dec_ref(v___x_4038_);
                    v_fst_4041_ = lean_ctor_get(v_fst_4039_, 0);
                    lean_inc(v_fst_4041_);
                    v_snd_4042_ = lean_ctor_get(v_fst_4039_, 1);
                    lean_inc(v_snd_4042_);
                    lean_dec(v_fst_4039_);
                    v___x_4043_ = lean_unsigned_to_nat(1);
                    v___x_4044_ = lean_nat_add(v_offset_3990_, v___x_4043_);
                    lean_dec(v_offset_3990_);
                    lean_inc_ref(v_body_4036_);
                    v___x_4045_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_body_4036_, v___x_4044_, v_snd_4042_, v_a_3992_, v_snd_4040_);
                    v_fst_4046_ = lean_ctor_get(v___x_4045_, 0);
                    v_snd_4047_ = lean_ctor_get(v___x_4045_, 1);
                    v_isSharedCheck_4068_ = (!lean_is_exclusive(v___x_4045_)) as u8;
                    if v_isSharedCheck_4068_ == 0 {
                        v___x_4049_ = v___x_4045_;
                        v_isShared_4050_ = v_isSharedCheck_4068_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_4047_);
                        lean_inc(v_fst_4046_);
                        lean_dec(v___x_4045_);
                        v___x_4049_ = lean_box(0);
                        v_isShared_4050_ = v_isSharedCheck_4068_;
                        state = 6;
                        continue;
                    }
                }
                8 => {
                    v_declName_4069_ = lean_ctor_get(v_e_3989_, 0);
                    v_type_4070_ = lean_ctor_get(v_e_3989_, 1);
                    v_value_4071_ = lean_ctor_get(v_e_3989_, 2);
                    v_body_4072_ = lean_ctor_get(v_e_3989_, 3);
                    v_nondep_4073_ = lean_ctor_get_uint8(
                        v_e_3989_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_inc_n(v_offset_3990_, 2);
                    lean_inc_ref(v_type_4070_);
                    v___x_4074_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_type_4070_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    v_fst_4075_ = lean_ctor_get(v___x_4074_, 0);
                    lean_inc(v_fst_4075_);
                    v_snd_4076_ = lean_ctor_get(v___x_4074_, 1);
                    lean_inc(v_snd_4076_);
                    lean_dec_ref(v___x_4074_);
                    v_fst_4077_ = lean_ctor_get(v_fst_4075_, 0);
                    lean_inc(v_fst_4077_);
                    v_snd_4078_ = lean_ctor_get(v_fst_4075_, 1);
                    lean_inc(v_snd_4078_);
                    lean_dec(v_fst_4075_);
                    lean_inc_ref(v_value_4071_);
                    v___x_4079_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_value_4071_, v_offset_3990_, v_snd_4078_, v_a_3992_, v_snd_4076_);
                    v_fst_4080_ = lean_ctor_get(v___x_4079_, 0);
                    lean_inc(v_fst_4080_);
                    v_snd_4081_ = lean_ctor_get(v___x_4079_, 1);
                    lean_inc(v_snd_4081_);
                    lean_dec_ref(v___x_4079_);
                    v_fst_4082_ = lean_ctor_get(v_fst_4080_, 0);
                    lean_inc(v_fst_4082_);
                    v_snd_4083_ = lean_ctor_get(v_fst_4080_, 1);
                    lean_inc(v_snd_4083_);
                    lean_dec(v_fst_4080_);
                    v___x_4084_ = lean_unsigned_to_nat(1);
                    v___x_4085_ = lean_nat_add(v_offset_3990_, v___x_4084_);
                    lean_dec(v_offset_3990_);
                    lean_inc_ref(v_body_4072_);
                    v___x_4086_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_body_4072_, v___x_4085_, v_snd_4083_, v_a_3992_, v_snd_4081_);
                    v_fst_4087_ = lean_ctor_get(v___x_4086_, 0);
                    v_snd_4088_ = lean_ctor_get(v___x_4086_, 1);
                    v_isSharedCheck_4111_ = (!lean_is_exclusive(v___x_4086_)) as u8;
                    if v_isSharedCheck_4111_ == 0 {
                        v___x_4090_ = v___x_4086_;
                        v_isShared_4091_ = v_isSharedCheck_4111_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_snd_4088_);
                        lean_inc(v_fst_4087_);
                        lean_dec(v___x_4086_);
                        v___x_4090_ = lean_box(0);
                        v_isShared_4091_ = v_isSharedCheck_4111_;
                        state = 11;
                        continue;
                    }
                }
                10 => {
                    v_data_4112_ = lean_ctor_get(v_e_3989_, 0);
                    v_expr_4113_ = lean_ctor_get(v_e_3989_, 1);
                    lean_inc_ref(v_expr_4113_);
                    v___x_4114_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_expr_4113_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    v_fst_4115_ = lean_ctor_get(v___x_4114_, 0);
                    v_snd_4116_ = lean_ctor_get(v___x_4114_, 1);
                    v_isSharedCheck_4134_ = (!lean_is_exclusive(v___x_4114_)) as u8;
                    if v_isSharedCheck_4134_ == 0 {
                        v___x_4118_ = v___x_4114_;
                        v_isShared_4119_ = v_isSharedCheck_4134_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_snd_4116_);
                        lean_inc(v_fst_4115_);
                        lean_dec(v___x_4114_);
                        v___x_4118_ = lean_box(0);
                        v_isShared_4119_ = v_isSharedCheck_4134_;
                        state = 16;
                        continue;
                    }
                }
                11 => {
                    v_typeName_4135_ = lean_ctor_get(v_e_3989_, 0);
                    v_idx_4136_ = lean_ctor_get(v_e_3989_, 1);
                    v_struct_4137_ = lean_ctor_get(v_e_3989_, 2);
                    lean_inc_ref(v_struct_4137_);
                    v___x_4138_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_3988_, v_struct_4137_, v_offset_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
                    v_fst_4139_ = lean_ctor_get(v___x_4138_, 0);
                    v_snd_4140_ = lean_ctor_get(v___x_4138_, 1);
                    v_isSharedCheck_4158_ = (!lean_is_exclusive(v___x_4138_)) as u8;
                    if v_isSharedCheck_4158_ == 0 {
                        v___x_4142_ = v___x_4138_;
                        v_isShared_4143_ = v_isSharedCheck_4158_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_snd_4140_);
                        lean_inc(v_fst_4139_);
                        lean_dec(v___x_4138_);
                        v___x_4142_ = lean_box(0);
                        v_isShared_4143_ = v_isSharedCheck_4158_;
                        state = 20;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_offset_3990_);
                    lean_dec_ref(v_e_3989_);
                    v___x_4159_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1_once), _init_l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___closed__1);
                    v___x_4160_ = l_panic___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__9(v___x_4159_, v_a_3991_, v_a_3992_, v_a_3993_);
                    return v___x_4160_;
                }
            },
            1 => {
                v_fst_4016_ = lean_ctor_get(v_fst_4011_, 0);
                v_snd_4017_ = lean_ctor_get(v_fst_4011_, 1);
                v_isSharedCheck_4032_ = (!lean_is_exclusive(v_fst_4011_)) as u8;
                if v_isSharedCheck_4032_ == 0 {
                    v___x_4019_ = v_fst_4011_;
                    v_isShared_4020_ = v_isSharedCheck_4032_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4017_);
                    lean_inc(v_fst_4016_);
                    lean_dec(v_fst_4011_);
                    v___x_4019_ = lean_box(0);
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
                    lean_inc(v_binderName_3999_);
                    lean_del_object(v___x_4019_);
                    lean_del_object(v___x_4014_);
                    lean_dec_ref_known(v_e_3989_, 3);
                    v___x_4023_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__4(v_binderName_3999_, v_binderInfo_4002_, v_fst_4006_, v_fst_4016_, v_snd_4017_, v_a_3992_, v_snd_4012_);
                    return v___x_4023_;
                } else {
                    lean_dec(v_fst_4016_);
                    lean_dec(v_fst_4006_);
                    if v_isShared_4020_ == 0 {
                        lean_ctor_set(v___x_4019_, 0, v_e_3989_);
                        v___x_4025_ = v___x_4019_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_e_3989_);
                        lean_ctor_set(v_reuseFailAlloc_4029_, 1, v_snd_4017_);
                        v___x_4025_ = v_reuseFailAlloc_4029_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4015_ == 0 {
                    lean_ctor_set(v___x_4014_, 0, v___x_4025_);
                    v___x_4027_ = v___x_4014_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4025_);
                    lean_ctor_set(v_reuseFailAlloc_4028_, 1, v_snd_4012_);
                    v___x_4027_ = v_reuseFailAlloc_4028_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4027_;
            }
            6 => {
                v_fst_4051_ = lean_ctor_get(v_fst_4046_, 0);
                v_snd_4052_ = lean_ctor_get(v_fst_4046_, 1);
                v_isSharedCheck_4067_ = (!lean_is_exclusive(v_fst_4046_)) as u8;
                if v_isSharedCheck_4067_ == 0 {
                    v___x_4054_ = v_fst_4046_;
                    v_isShared_4055_ = v_isSharedCheck_4067_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_4052_);
                    lean_inc(v_fst_4051_);
                    lean_dec(v_fst_4046_);
                    v___x_4054_ = lean_box(0);
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
                    lean_inc(v_binderName_4034_);
                    lean_del_object(v___x_4054_);
                    lean_del_object(v___x_4049_);
                    lean_dec_ref_known(v_e_3989_, 3);
                    v___x_4058_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__5(v_binderName_4034_, v_binderInfo_4037_, v_fst_4041_, v_fst_4051_, v_snd_4052_, v_a_3992_, v_snd_4047_);
                    return v___x_4058_;
                } else {
                    lean_dec(v_fst_4051_);
                    lean_dec(v_fst_4041_);
                    if v_isShared_4055_ == 0 {
                        lean_ctor_set(v___x_4054_, 0, v_e_3989_);
                        v___x_4060_ = v___x_4054_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_e_3989_);
                        lean_ctor_set(v_reuseFailAlloc_4064_, 1, v_snd_4052_);
                        v___x_4060_ = v_reuseFailAlloc_4064_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4050_ == 0 {
                    lean_ctor_set(v___x_4049_, 0, v___x_4060_);
                    v___x_4062_ = v___x_4049_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4060_);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_snd_4047_);
                    v___x_4062_ = v_reuseFailAlloc_4063_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4062_;
            }
            11 => {
                v_fst_4092_ = lean_ctor_get(v_fst_4087_, 0);
                v_snd_4093_ = lean_ctor_get(v_fst_4087_, 1);
                v_isSharedCheck_4110_ = (!lean_is_exclusive(v_fst_4087_)) as u8;
                if v_isSharedCheck_4110_ == 0 {
                    v___x_4095_ = v_fst_4087_;
                    v_isShared_4096_ = v_isSharedCheck_4110_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_snd_4093_);
                    lean_inc(v_fst_4092_);
                    lean_dec(v_fst_4087_);
                    v___x_4095_ = lean_box(0);
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
                    lean_inc(v_declName_4069_);
                    lean_del_object(v___x_4095_);
                    lean_del_object(v___x_4090_);
                    lean_dec_ref_known(v_e_3989_, 4);
                    v___x_4099_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_4069_, v_fst_4077_, v_fst_4082_, v_fst_4092_, v_nondep_4073_, v_snd_4093_, v_a_3992_, v_snd_4088_);
                    return v___x_4099_;
                } else {
                    v___x_4100_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_4072_,
                            v_fst_4092_,
                        );
                    if v___x_4100_ == 0 {
                        lean_inc(v_declName_4069_);
                        lean_del_object(v___x_4095_);
                        lean_del_object(v___x_4090_);
                        lean_dec_ref_known(v_e_3989_, 4);
                        v___x_4101_ = l_Lean_Meta_Sym_Internal_mkLetS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__6(v_declName_4069_, v_fst_4077_, v_fst_4082_, v_fst_4092_, v_nondep_4073_, v_snd_4093_, v_a_3992_, v_snd_4088_);
                        return v___x_4101_;
                    } else {
                        lean_dec(v_fst_4092_);
                        lean_dec(v_fst_4082_);
                        lean_dec(v_fst_4077_);
                        if v_isShared_4096_ == 0 {
                            lean_ctor_set(v___x_4095_, 0, v_e_3989_);
                            v___x_4103_ = v___x_4095_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_e_3989_);
                            lean_ctor_set(v_reuseFailAlloc_4107_, 1, v_snd_4093_);
                            v___x_4103_ = v_reuseFailAlloc_4107_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            14 => {
                if v_isShared_4091_ == 0 {
                    lean_ctor_set(v___x_4090_, 0, v___x_4103_);
                    v___x_4105_ = v___x_4090_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4106_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4106_, 0, v___x_4103_);
                    lean_ctor_set(v_reuseFailAlloc_4106_, 1, v_snd_4088_);
                    v___x_4105_ = v_reuseFailAlloc_4106_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4105_;
            }
            16 => {
                v_fst_4120_ = lean_ctor_get(v_fst_4115_, 0);
                v_snd_4121_ = lean_ctor_get(v_fst_4115_, 1);
                v_isSharedCheck_4133_ = (!lean_is_exclusive(v_fst_4115_)) as u8;
                if v_isSharedCheck_4133_ == 0 {
                    v___x_4123_ = v_fst_4115_;
                    v_isShared_4124_ = v_isSharedCheck_4133_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_snd_4121_);
                    lean_inc(v_fst_4120_);
                    lean_dec(v_fst_4115_);
                    v___x_4123_ = lean_box(0);
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
                    lean_inc(v_data_4112_);
                    lean_del_object(v___x_4123_);
                    lean_del_object(v___x_4118_);
                    lean_dec_ref_known(v_e_3989_, 2);
                    v___x_4126_ = l_Lean_Meta_Sym_Internal_mkMDataS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__7(v_data_4112_, v_fst_4120_, v_snd_4121_, v_a_3992_, v_snd_4116_);
                    return v___x_4126_;
                } else {
                    lean_dec(v_fst_4120_);
                    if v_isShared_4124_ == 0 {
                        lean_ctor_set(v___x_4123_, 0, v_e_3989_);
                        v___x_4128_ = v___x_4123_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_e_3989_);
                        lean_ctor_set(v_reuseFailAlloc_4132_, 1, v_snd_4121_);
                        v___x_4128_ = v_reuseFailAlloc_4132_;
                        state = 18;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4119_ == 0 {
                    lean_ctor_set(v___x_4118_, 0, v___x_4128_);
                    v___x_4130_ = v___x_4118_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4131_, 0, v___x_4128_);
                    lean_ctor_set(v_reuseFailAlloc_4131_, 1, v_snd_4116_);
                    v___x_4130_ = v_reuseFailAlloc_4131_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4130_;
            }
            20 => {
                v_fst_4144_ = lean_ctor_get(v_fst_4139_, 0);
                v_snd_4145_ = lean_ctor_get(v_fst_4139_, 1);
                v_isSharedCheck_4157_ = (!lean_is_exclusive(v_fst_4139_)) as u8;
                if v_isSharedCheck_4157_ == 0 {
                    v___x_4147_ = v_fst_4139_;
                    v_isShared_4148_ = v_isSharedCheck_4157_;
                    state = 21;
                    continue;
                } else {
                    lean_inc(v_snd_4145_);
                    lean_inc(v_fst_4144_);
                    lean_dec(v_fst_4139_);
                    v___x_4147_ = lean_box(0);
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
                    lean_inc(v_idx_4136_);
                    lean_inc(v_typeName_4135_);
                    lean_del_object(v___x_4147_);
                    lean_del_object(v___x_4142_);
                    lean_dec_ref_known(v_e_3989_, 3);
                    v___x_4150_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__8(v_typeName_4135_, v_idx_4136_, v_fst_4144_, v_snd_4145_, v_a_3992_, v_snd_4140_);
                    return v___x_4150_;
                } else {
                    lean_dec(v_fst_4144_);
                    if v_isShared_4148_ == 0 {
                        lean_ctor_set(v___x_4147_, 0, v_e_3989_);
                        v___x_4152_ = v___x_4147_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_e_3989_);
                        lean_ctor_set(v_reuseFailAlloc_4156_, 1, v_snd_4145_);
                        v___x_4152_ = v_reuseFailAlloc_4156_;
                        state = 22;
                        continue;
                    }
                }
            }
            22 => {
                if v_isShared_4143_ == 0 {
                    lean_ctor_set(v___x_4142_, 0, v___x_4152_);
                    v___x_4154_ = v___x_4142_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4155_, 0, v___x_4152_);
                    lean_ctor_set(v_reuseFailAlloc_4155_, 1, v_snd_4140_);
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
    mut v_subst_4161_: *mut LeanObject,
    mut v_e_4162_: *mut LeanObject,
    mut v_offset_4163_: *mut LeanObject,
    mut v_a_4164_: *mut LeanObject,
    mut v_a_4165_: u8,
    mut v_a_4166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: u8 = 0;
    v___x_4167_ = l_Lean_Expr_looseBVarRange(v_e_4162_);
    v___x_4168_ = lean_nat_dec_le(v___x_4167_, v_offset_4163_);
    lean_dec(v___x_4167_);
    if v___x_4168_ == 0 {
        let mut v_key_4169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_offset_4163_);
        lean_inc_ref(v_e_4162_);
        v_key_4169_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v_key_4169_, 0, v_e_4162_);
        lean_ctor_set(v_key_4169_, 1, v_offset_4163_);
        v___x_4170_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_4164_, v_key_4169_);
        if lean_obj_tag(v___x_4170_) == 1 {
            let mut v_val_4171_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v_key_4169_, 2);
            lean_dec(v_offset_4163_);
            lean_dec_ref(v_e_4162_);
            v_val_4171_ = lean_ctor_get(v___x_4170_, 0);
            lean_inc(v_val_4171_);
            lean_dec_ref_known(v___x_4170_, 1);
            v___x_4172_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_4172_, 0, v_val_4171_);
            lean_ctor_set(v___x_4172_, 1, v_a_4164_);
            v___x_4173_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_4173_, 0, v___x_4172_);
            lean_ctor_set(v___x_4173_, 1, v_a_4166_);
            return v___x_4173_;
        } else {
            lean_dec(v___x_4170_);
            match lean_obj_tag(v_e_4162_) {
                0 => {
                    let mut v_deBruijnIndex_4174_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_fst_4176_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_snd_4177_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_fst_4178_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_snd_4179_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
                    v_deBruijnIndex_4174_ = lean_ctor_get(v_e_4162_, 0);
                    lean_inc(v_deBruijnIndex_4174_);
                    v___x_4175_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitBVar(v_subst_4161_, v_e_4162_, v_deBruijnIndex_4174_, v_offset_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
                    lean_dec(v_offset_4163_);
                    lean_dec(v_deBruijnIndex_4174_);
                    v_fst_4176_ = lean_ctor_get(v___x_4175_, 0);
                    lean_inc(v_fst_4176_);
                    v_snd_4177_ = lean_ctor_get(v___x_4175_, 1);
                    lean_inc(v_snd_4177_);
                    lean_dec_ref(v___x_4175_);
                    v_fst_4178_ = lean_ctor_get(v_fst_4176_, 0);
                    lean_inc(v_fst_4178_);
                    v_snd_4179_ = lean_ctor_get(v_fst_4176_, 1);
                    lean_inc(v_snd_4179_);
                    lean_dec(v_fst_4176_);
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
                    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_offset_4163_);
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
                    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_offset_4163_);
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
                    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_offset_4163_);
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
                    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_offset_4163_);
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
                    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v_offset_4163_);
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
                    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_fst_4187_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_snd_4188_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_fst_4189_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_snd_4190_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4186_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_4161_, v_e_4162_, v_offset_4163_, v_a_4164_, v_a_4165_, v_a_4166_);
                    v_fst_4187_ = lean_ctor_get(v___x_4186_, 0);
                    lean_inc(v_fst_4187_);
                    v_snd_4188_ = lean_ctor_get(v___x_4186_, 1);
                    lean_inc(v_snd_4188_);
                    lean_dec_ref(v___x_4186_);
                    v_fst_4189_ = lean_ctor_get(v_fst_4187_, 0);
                    lean_inc(v_fst_4189_);
                    v_snd_4190_ = lean_ctor_get(v_fst_4187_, 1);
                    lean_inc(v_snd_4190_);
                    lean_dec(v_fst_4187_);
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
        let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_offset_4163_);
        v___x_4192_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4192_, 0, v_e_4162_);
        lean_ctor_set(v___x_4192_, 1, v_a_4164_);
        v___x_4193_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4193_, 0, v___x_4192_);
        lean_ctor_set(v___x_4193_, 1, v_a_4166_);
        return v___x_4193_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(
    mut v_subst_4194_: *mut LeanObject,
    mut v_e_4195_: *mut LeanObject,
    mut v_offset_4196_: *mut LeanObject,
    mut v_a_4197_: *mut LeanObject,
    mut v_a_4198_: u8,
    mut v_a_4199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: u8 = 0;
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: u8 = 0;
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_4195_) == 5 {
                    v_fn_4200_ = lean_ctor_get(v_e_4195_, 0);
                    v_arg_4201_ = lean_ctor_get(v_e_4195_, 1);
                    lean_inc(v_offset_4196_);
                    lean_inc_ref(v_e_4195_);
                    v_key_4202_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_key_4202_, 0, v_e_4195_);
                    lean_ctor_set(v_key_4202_, 1, v_offset_4196_);
                    v___x_4203_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visitChild___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__2_spec__4___redArg(v_a_4197_, v_key_4202_);
                    if lean_obj_tag(v___x_4203_) == 1 {
                        lean_dec_ref_known(v_key_4202_, 2);
                        lean_dec_ref_known(v_e_4195_, 2);
                        lean_dec(v_offset_4196_);
                        v_val_4204_ = lean_ctor_get(v___x_4203_, 0);
                        lean_inc(v_val_4204_);
                        lean_dec_ref_known(v___x_4203_, 1);
                        v___x_4205_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4205_, 0, v_val_4204_);
                        lean_ctor_set(v___x_4205_, 1, v_a_4197_);
                        v___x_4206_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4206_, 0, v___x_4205_);
                        lean_ctor_set(v___x_4206_, 1, v_a_4199_);
                        return v___x_4206_;
                    } else {
                        lean_dec(v___x_4203_);
                        lean_inc(v_offset_4196_);
                        lean_inc_ref(v_fn_4200_);
                        v___x_4207_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_4194_, v_fn_4200_, v_offset_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
                        v_fst_4208_ = lean_ctor_get(v___x_4207_, 0);
                        lean_inc(v_fst_4208_);
                        v_snd_4209_ = lean_ctor_get(v___x_4207_, 1);
                        lean_inc(v_snd_4209_);
                        lean_dec_ref(v___x_4207_);
                        v_fst_4210_ = lean_ctor_get(v_fst_4208_, 0);
                        lean_inc(v_fst_4210_);
                        v_snd_4211_ = lean_ctor_get(v_fst_4208_, 1);
                        lean_inc(v_snd_4211_);
                        lean_dec(v_fst_4208_);
                        lean_inc_ref(v_arg_4201_);
                        v___x_4212_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(v_subst_4194_, v_arg_4201_, v_offset_4196_, v_snd_4211_, v_a_4198_, v_snd_4209_);
                        v_fst_4213_ = lean_ctor_get(v___x_4212_, 0);
                        lean_inc(v_fst_4213_);
                        v_snd_4214_ = lean_ctor_get(v___x_4212_, 1);
                        lean_inc(v_snd_4214_);
                        lean_dec_ref(v___x_4212_);
                        v_fst_4215_ = lean_ctor_get(v_fst_4213_, 0);
                        lean_inc(v_fst_4215_);
                        v_snd_4216_ = lean_ctor_get(v_fst_4213_, 1);
                        lean_inc(v_snd_4216_);
                        lean_dec(v_fst_4213_);
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
                    lean_dec_ref_known(v_e_4195_, 2);
                    v___x_4219_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_ReplaceS_0__Lean_Meta_Sym_visit___at___00Lean_Meta_Sym_instantiateRevRangeS_spec__2_spec__3(v_fst_4210_, v_fst_4215_, v_snd_4216_, v_a_4198_, v_snd_4214_);
                    v_fst_4220_ = lean_ctor_get(v___x_4219_, 0);
                    lean_inc(v_fst_4220_);
                    v_snd_4221_ = lean_ctor_get(v___x_4219_, 1);
                    lean_inc(v_snd_4221_);
                    lean_dec_ref(v___x_4219_);
                    v_fst_4222_ = lean_ctor_get(v_fst_4220_, 0);
                    lean_inc(v_fst_4222_);
                    v_snd_4223_ = lean_ctor_get(v_fst_4220_, 1);
                    lean_inc(v_snd_4223_);
                    lean_dec(v_fst_4220_);
                    v___x_4224_ =
                        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_save___redArg(
                            v_key_4202_,
                            v_fst_4222_,
                            v_snd_4223_,
                            v_snd_4221_,
                        );
                    return v___x_4224_;
                } else {
                    lean_dec(v_fst_4215_);
                    lean_dec(v_fst_4210_);
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
    mut v_subst_4229_: *mut LeanObject,
    mut v_e_4230_: *mut LeanObject,
    mut v_offset_4231_: *mut LeanObject,
    mut v_a_4232_: *mut LeanObject,
    mut v_a_4233_: *mut LeanObject,
    mut v_a_4234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_4235_: u8 = 0;
    let mut v_res_4236_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_4235_ = (lean_unbox(v_a_4233_) as u8);
    v_res_4236_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppDefault(v_subst_4229_, v_e_4230_, v_offset_4231_, v_a_4232_, v_a_boxed_4235_, v_a_4234_);
    lean_dec_ref(v_subst_4229_);
    return v_res_4236_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild___boxed(
    mut v_subst_4237_: *mut LeanObject,
    mut v_e_4238_: *mut LeanObject,
    mut v_offset_4239_: *mut LeanObject,
    mut v_a_4240_: *mut LeanObject,
    mut v_a_4241_: *mut LeanObject,
    mut v_a_4242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_4243_: u8 = 0;
    let mut v_res_4244_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_4243_ = (lean_unbox(v_a_4241_) as u8);
    v_res_4244_ =
        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitChild(
            v_subst_4237_,
            v_e_4238_,
            v_offset_4239_,
            v_a_4240_,
            v_a_boxed_4243_,
            v_a_4242_,
        );
    lean_dec_ref(v_subst_4237_);
    return v_res_4244_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg___boxed(
    mut v_subst_4245_: *mut LeanObject,
    mut v_e_4246_: *mut LeanObject,
    mut v_f_4247_: *mut LeanObject,
    mut v_arg_4248_: *mut LeanObject,
    mut v_offset_4249_: *mut LeanObject,
    mut v_a_4250_: *mut LeanObject,
    mut v_a_4251_: *mut LeanObject,
    mut v_a_4252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_4253_: u8 = 0;
    let mut v_res_4254_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_4253_ = (lean_unbox(v_a_4251_) as u8);
    v_res_4254_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_4245_, v_e_4246_, v_f_4247_, v_arg_4248_, v_offset_4249_, v_a_4250_, v_a_boxed_4253_, v_a_4252_);
    lean_dec_ref(v_subst_4245_);
    return v_res_4254_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta___boxed(
    mut v_subst_4255_: *mut LeanObject,
    mut v_e_4256_: *mut LeanObject,
    mut v_f_4257_: *mut LeanObject,
    mut v_argsRev_4258_: *mut LeanObject,
    mut v_offset_4259_: *mut LeanObject,
    mut v_modified_4260_: *mut LeanObject,
    mut v_a_4261_: *mut LeanObject,
    mut v_a_4262_: *mut LeanObject,
    mut v_a_4263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modified_boxed_4264_: u8 = 0;
    let mut v_a_boxed_4265_: u8 = 0;
    let mut v_res_4266_: *mut LeanObject = core::ptr::null_mut();
    v_modified_boxed_4264_ = (lean_unbox(v_modified_4260_) as u8);
    v_a_boxed_4265_ = (lean_unbox(v_a_4262_) as u8);
    v_res_4266_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitAppBeta(v_subst_4255_, v_e_4256_, v_f_4257_, v_argsRev_4258_, v_offset_4259_, v_modified_boxed_4264_, v_a_4261_, v_a_boxed_4265_, v_a_4263_);
    lean_dec_ref(v_subst_4255_);
    return v_res_4266_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit___boxed(
    mut v_subst_4267_: *mut LeanObject,
    mut v_e_4268_: *mut LeanObject,
    mut v_offset_4269_: *mut LeanObject,
    mut v_a_4270_: *mut LeanObject,
    mut v_a_4271_: *mut LeanObject,
    mut v_a_4272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_4273_: u8 = 0;
    let mut v_res_4274_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_4273_ = (lean_unbox(v_a_4271_) as u8);
    v_res_4274_ =
        l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(
            v_subst_4267_,
            v_e_4268_,
            v_offset_4269_,
            v_a_4270_,
            v_a_boxed_4273_,
            v_a_4272_,
        );
    lean_dec_ref(v_subst_4267_);
    return v_res_4274_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp(
    mut v_subst_4275_: *mut LeanObject,
    mut v_e_4276_: *mut LeanObject,
    mut v_f_4277_: *mut LeanObject,
    mut v_arg_4278_: *mut LeanObject,
    mut v_offset_4279_: *mut LeanObject,
    mut v_x_4280_: *mut LeanObject,
    mut v_a_4281_: *mut LeanObject,
    mut v_a_4282_: u8,
    mut v_a_4283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    v___x_4284_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___redArg(v_subst_4275_, v_e_4276_, v_f_4277_, v_arg_4278_, v_offset_4279_, v_a_4281_, v_a_4282_, v_a_4283_);
    return v___x_4284_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visitApp___boxed(
    mut v_subst_4285_: *mut LeanObject,
    mut v_e_4286_: *mut LeanObject,
    mut v_f_4287_: *mut LeanObject,
    mut v_arg_4288_: *mut LeanObject,
    mut v_offset_4289_: *mut LeanObject,
    mut v_x_4290_: *mut LeanObject,
    mut v_a_4291_: *mut LeanObject,
    mut v_a_4292_: *mut LeanObject,
    mut v_a_4293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_4294_: u8 = 0;
    let mut v_res_4295_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_4294_ = (lean_unbox(v_a_4292_) as u8);
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
    lean_dec_ref(v_subst_4285_);
    return v_res_4295_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(
    mut v_e_4296_: *mut LeanObject,
    mut v_subst_4297_: *mut LeanObject,
    mut v_a_4298_: u8,
    mut v_a_4299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4301_: u8 = 0;
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4310_: u8 = 0;
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut v_unused_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: u8 = 0;
    let mut v___x_4320_: u8 = 0;
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4317_ = lean_array_get_size(v_subst_4297_);
                v___x_4318_ = lean_unsigned_to_nat(0);
                v___x_4319_ = lean_nat_dec_eq(v___x_4317_, v___x_4318_);
                if v___x_4319_ == 0 {
                    v___x_4320_ = l_Lean_Expr_hasLooseBVars(v_e_4296_);
                    if v___x_4320_ == 0 {
                        v___x_4321_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4321_, 0, v_e_4296_);
                        lean_ctor_set(v___x_4321_, 1, v_a_4299_);
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
                    v___x_4302_ = lean_unsigned_to_nat(0);
                    v___x_4303_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_instantiateRevRangeS___closed__2_once
                        ),
                        _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__2,
                    );
                    v___x_4304_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27_visit(v_subst_4297_, v_e_4296_, v___x_4302_, v___x_4303_, v_a_4298_, v_a_4299_);
                    v_fst_4305_ = lean_ctor_get(v___x_4304_, 0);
                    lean_inc(v_fst_4305_);
                    v_snd_4306_ = lean_ctor_get(v___x_4304_, 1);
                    lean_inc(v_snd_4306_);
                    lean_dec_ref(v___x_4304_);
                    v_fst_4307_ = lean_ctor_get(v_fst_4305_, 0);
                    v_isSharedCheck_4314_ = (!lean_is_exclusive(v_fst_4305_)) as u8;
                    if v_isSharedCheck_4314_ == 0 {
                        v_unused_4315_ = lean_ctor_get(v_fst_4305_, 1);
                        lean_dec(v_unused_4315_);
                        v___x_4309_ = v_fst_4305_;
                        v_isShared_4310_ = v_isSharedCheck_4314_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_4307_);
                        lean_dec(v_fst_4305_);
                        v___x_4309_ = lean_box(0);
                        v_isShared_4310_ = v_isSharedCheck_4314_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4316_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4316_, 0, v_e_4296_);
                    lean_ctor_set(v___x_4316_, 1, v_a_4299_);
                    return v___x_4316_;
                }
            }
            2 => {
                if v_isShared_4310_ == 0 {
                    lean_ctor_set(v___x_4309_, 1, v_snd_4306_);
                    v___x_4312_ = v___x_4309_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_fst_4307_);
                    lean_ctor_set(v_reuseFailAlloc_4313_, 1, v_snd_4306_);
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
    mut v_e_4322_: *mut LeanObject,
    mut v_subst_4323_: *mut LeanObject,
    mut v_a_4324_: *mut LeanObject,
    mut v_a_4325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_4326_: u8 = 0;
    let mut v_res_4327_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_4326_ = (lean_unbox(v_a_4324_) as u8);
    v_res_4327_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(
        v_e_4322_,
        v_subst_4323_,
        v_a_boxed_4326_,
        v_a_4325_,
    );
    lean_dec_ref(v_subst_4323_);
    return v_res_4327_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
    mut v_e_4328_: *mut LeanObject,
    mut v_subst_4329_: *mut LeanObject,
    mut v_a_4330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4332_: u8 = 0;
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: u8 = 0;
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4348_: u8 = 0;
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4351_: u8 = 0;
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4357_: u8 = 0;
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4371_: u8 = 0;
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4380_: u8 = 0;
    let mut v_unused_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4332_ = l_Lean_Expr_hasLooseBVars(v_e_4328_);
                if v___x_4332_ == 0 {
                    v___x_4333_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4333_, 0, v_e_4328_);
                    return v___x_4333_;
                } else {
                    v___x_4334_ = lean_array_get_size(v_subst_4329_);
                    v___x_4335_ = lean_unsigned_to_nat(0);
                    v___x_4336_ = lean_nat_dec_eq(v___x_4334_, v___x_4335_);
                    if v___x_4336_ == 0 {
                        v___x_4337_ = lean_st_ref_take(v_a_4330_);
                        v_share_4338_ = lean_ctor_get(v___x_4337_, 0);
                        v_maxFVar_4339_ = lean_ctor_get(v___x_4337_, 1);
                        v_proofInstInfo_4340_ = lean_ctor_get(v___x_4337_, 2);
                        v_inferType_4341_ = lean_ctor_get(v___x_4337_, 3);
                        v_getLevel_4342_ = lean_ctor_get(v___x_4337_, 4);
                        v_congrInfo_4343_ = lean_ctor_get(v___x_4337_, 5);
                        v_defEqI_4344_ = lean_ctor_get(v___x_4337_, 6);
                        v_extensions_4345_ = lean_ctor_get(v___x_4337_, 7);
                        v_issues_4346_ = lean_ctor_get(v___x_4337_, 8);
                        v_canon_4347_ = lean_ctor_get(v___x_4337_, 9);
                        v_debug_4348_ = lean_ctor_get_uint8(
                            v___x_4337_,
                            (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        );
                        v_isSharedCheck_4383_ = (!lean_is_exclusive(v___x_4337_)) as u8;
                        if v_isSharedCheck_4383_ == 0 {
                            v___x_4350_ = v___x_4337_;
                            v_isShared_4351_ = v_isSharedCheck_4383_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_canon_4347_);
                            lean_inc(v_issues_4346_);
                            lean_inc(v_extensions_4345_);
                            lean_inc(v_defEqI_4344_);
                            lean_inc(v_congrInfo_4343_);
                            lean_inc(v_getLevel_4342_);
                            lean_inc(v_inferType_4341_);
                            lean_inc(v_proofInstInfo_4340_);
                            lean_inc(v_maxFVar_4339_);
                            lean_inc(v_share_4338_);
                            lean_dec(v___x_4337_);
                            v___x_4350_ = lean_box(0);
                            v_isShared_4351_ = v_isSharedCheck_4383_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4384_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4384_, 0, v_e_4328_);
                        return v___x_4384_;
                    }
                }
            }
            1 => {
                v___x_4352_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once),
                    _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0,
                );
                if v_isShared_4351_ == 0 {
                    lean_ctor_set(v___x_4350_, 0, v___x_4352_);
                    v___x_4354_ = v___x_4350_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4352_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_maxFVar_4339_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 2, v_proofInstInfo_4340_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 3, v_inferType_4341_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 4, v_getLevel_4342_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 5, v_congrInfo_4343_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 6, v_defEqI_4344_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 7, v_extensions_4345_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 8, v_issues_4346_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 9, v_canon_4347_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4382_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
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
                v_debug_4357_ = lean_ctor_get_uint8(
                    v___x_4356_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_4356_);
                v___x_4358_ =
                    l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_instantiateRevBetaS_x27(
                        v_e_4328_,
                        v_subst_4329_,
                        v_debug_4357_,
                        v_share_4338_,
                    );
                v_fst_4359_ = lean_ctor_get(v___x_4358_, 0);
                lean_inc(v_fst_4359_);
                v_snd_4360_ = lean_ctor_get(v___x_4358_, 1);
                lean_inc(v_snd_4360_);
                lean_dec_ref(v___x_4358_);
                v___x_4361_ = lean_st_ref_take(v_a_4330_);
                v_maxFVar_4362_ = lean_ctor_get(v___x_4361_, 1);
                v_proofInstInfo_4363_ = lean_ctor_get(v___x_4361_, 2);
                v_inferType_4364_ = lean_ctor_get(v___x_4361_, 3);
                v_getLevel_4365_ = lean_ctor_get(v___x_4361_, 4);
                v_congrInfo_4366_ = lean_ctor_get(v___x_4361_, 5);
                v_defEqI_4367_ = lean_ctor_get(v___x_4361_, 6);
                v_extensions_4368_ = lean_ctor_get(v___x_4361_, 7);
                v_issues_4369_ = lean_ctor_get(v___x_4361_, 8);
                v_canon_4370_ = lean_ctor_get(v___x_4361_, 9);
                v_debug_4371_ = lean_ctor_get_uint8(
                    v___x_4361_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4380_ = (!lean_is_exclusive(v___x_4361_)) as u8;
                if v_isSharedCheck_4380_ == 0 {
                    v_unused_4381_ = lean_ctor_get(v___x_4361_, 0);
                    lean_dec(v_unused_4381_);
                    v___x_4373_ = v___x_4361_;
                    v_isShared_4374_ = v_isSharedCheck_4380_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_canon_4370_);
                    lean_inc(v_issues_4369_);
                    lean_inc(v_extensions_4368_);
                    lean_inc(v_defEqI_4367_);
                    lean_inc(v_congrInfo_4366_);
                    lean_inc(v_getLevel_4365_);
                    lean_inc(v_inferType_4364_);
                    lean_inc(v_proofInstInfo_4363_);
                    lean_inc(v_maxFVar_4362_);
                    lean_dec(v___x_4361_);
                    v___x_4373_ = lean_box(0);
                    v_isShared_4374_ = v_isSharedCheck_4380_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4374_ == 0 {
                    lean_ctor_set(v___x_4373_, 0, v_snd_4360_);
                    v___x_4376_ = v___x_4373_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_snd_4360_);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 1, v_maxFVar_4362_);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 2, v_proofInstInfo_4363_);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 3, v_inferType_4364_);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 4, v_getLevel_4365_);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 5, v_congrInfo_4366_);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 6, v_defEqI_4367_);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 7, v_extensions_4368_);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 8, v_issues_4369_);
                    lean_ctor_set(v_reuseFailAlloc_4379_, 9, v_canon_4370_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4379_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_4371_,
                    );
                    v___x_4376_ = v_reuseFailAlloc_4379_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4377_ = lean_st_ref_set(v_a_4330_, v___x_4376_);
                v___x_4378_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4378_, 0, v_fst_4359_);
                return v___x_4378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevBetaS___redArg___boxed(
    mut v_e_4385_: *mut LeanObject,
    mut v_subst_4386_: *mut LeanObject,
    mut v_a_4387_: *mut LeanObject,
    mut v_a_4388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4389_: *mut LeanObject = core::ptr::null_mut();
    v_res_4389_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_4385_, v_subst_4386_, v_a_4387_);
    lean_dec(v_a_4387_);
    lean_dec_ref(v_subst_4386_);
    return v_res_4389_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevBetaS(
    mut v_e_4390_: *mut LeanObject,
    mut v_subst_4391_: *mut LeanObject,
    mut v_a_4392_: *mut LeanObject,
    mut v_a_4393_: *mut LeanObject,
    mut v_a_4394_: *mut LeanObject,
    mut v_a_4395_: *mut LeanObject,
    mut v_a_4396_: *mut LeanObject,
    mut v_a_4397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    v___x_4399_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_4390_, v_subst_4391_, v_a_4393_);
    return v___x_4399_;
}
pub unsafe fn l_Lean_Meta_Sym_instantiateRevBetaS___boxed(
    mut v_e_4400_: *mut LeanObject,
    mut v_subst_4401_: *mut LeanObject,
    mut v_a_4402_: *mut LeanObject,
    mut v_a_4403_: *mut LeanObject,
    mut v_a_4404_: *mut LeanObject,
    mut v_a_4405_: *mut LeanObject,
    mut v_a_4406_: *mut LeanObject,
    mut v_a_4407_: *mut LeanObject,
    mut v_a_4408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4409_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4407_);
    lean_dec_ref(v_a_4406_);
    lean_dec(v_a_4405_);
    lean_dec_ref(v_a_4404_);
    lean_dec(v_a_4403_);
    lean_dec_ref(v_a_4402_);
    lean_dec_ref(v_subst_4401_);
    return v_res_4409_;
}
pub unsafe fn l_Lean_Meta_Sym_betaRevS___redArg(
    mut v_f_4410_: *mut LeanObject,
    mut v_revArgs_4411_: *mut LeanObject,
    mut v_a_4412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4425_: u8 = 0;
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4428_: u8 = 0;
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4434_: u8 = 0;
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_4448_: u8 = 0;
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4457_: u8 = 0;
    let mut v_unused_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4414_ = lean_st_ref_take(v_a_4412_);
                v_share_4415_ = lean_ctor_get(v___x_4414_, 0);
                v_maxFVar_4416_ = lean_ctor_get(v___x_4414_, 1);
                v_proofInstInfo_4417_ = lean_ctor_get(v___x_4414_, 2);
                v_inferType_4418_ = lean_ctor_get(v___x_4414_, 3);
                v_getLevel_4419_ = lean_ctor_get(v___x_4414_, 4);
                v_congrInfo_4420_ = lean_ctor_get(v___x_4414_, 5);
                v_defEqI_4421_ = lean_ctor_get(v___x_4414_, 6);
                v_extensions_4422_ = lean_ctor_get(v___x_4414_, 7);
                v_issues_4423_ = lean_ctor_get(v___x_4414_, 8);
                v_canon_4424_ = lean_ctor_get(v___x_4414_, 9);
                v_debug_4425_ = lean_ctor_get_uint8(
                    v___x_4414_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4460_ = (!lean_is_exclusive(v___x_4414_)) as u8;
                if v_isSharedCheck_4460_ == 0 {
                    v___x_4427_ = v___x_4414_;
                    v_isShared_4428_ = v_isSharedCheck_4460_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_4424_);
                    lean_inc(v_issues_4423_);
                    lean_inc(v_extensions_4422_);
                    lean_inc(v_defEqI_4421_);
                    lean_inc(v_congrInfo_4420_);
                    lean_inc(v_getLevel_4419_);
                    lean_inc(v_inferType_4418_);
                    lean_inc(v_proofInstInfo_4417_);
                    lean_inc(v_maxFVar_4416_);
                    lean_inc(v_share_4415_);
                    lean_dec(v___x_4414_);
                    v___x_4427_ = lean_box(0);
                    v_isShared_4428_ = v_isSharedCheck_4460_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4429_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Sym_instantiateRevRangeS___closed__0_once),
                    _init_l_Lean_Meta_Sym_instantiateRevRangeS___closed__0,
                );
                if v_isShared_4428_ == 0 {
                    lean_ctor_set(v___x_4427_, 0, v___x_4429_);
                    v___x_4431_ = v___x_4427_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4429_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 1, v_maxFVar_4416_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 2, v_proofInstInfo_4417_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 3, v_inferType_4418_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 4, v_getLevel_4419_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 5, v_congrInfo_4420_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 6, v_defEqI_4421_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 7, v_extensions_4422_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 8, v_issues_4423_);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 9, v_canon_4424_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4459_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
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
                v_debug_4434_ = lean_ctor_get_uint8(
                    v___x_4433_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_4433_);
                v___x_4435_ = l___private_Lean_Meta_Sym_InstantiateS_0__Lean_Meta_Sym_betaRevS_x27(
                    v_f_4410_,
                    v_revArgs_4411_,
                    v_debug_4434_,
                    v_share_4415_,
                );
                v_fst_4436_ = lean_ctor_get(v___x_4435_, 0);
                lean_inc(v_fst_4436_);
                v_snd_4437_ = lean_ctor_get(v___x_4435_, 1);
                lean_inc(v_snd_4437_);
                lean_dec_ref(v___x_4435_);
                v___x_4438_ = lean_st_ref_take(v_a_4412_);
                v_maxFVar_4439_ = lean_ctor_get(v___x_4438_, 1);
                v_proofInstInfo_4440_ = lean_ctor_get(v___x_4438_, 2);
                v_inferType_4441_ = lean_ctor_get(v___x_4438_, 3);
                v_getLevel_4442_ = lean_ctor_get(v___x_4438_, 4);
                v_congrInfo_4443_ = lean_ctor_get(v___x_4438_, 5);
                v_defEqI_4444_ = lean_ctor_get(v___x_4438_, 6);
                v_extensions_4445_ = lean_ctor_get(v___x_4438_, 7);
                v_issues_4446_ = lean_ctor_get(v___x_4438_, 8);
                v_canon_4447_ = lean_ctor_get(v___x_4438_, 9);
                v_debug_4448_ = lean_ctor_get_uint8(
                    v___x_4438_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_4457_ = (!lean_is_exclusive(v___x_4438_)) as u8;
                if v_isSharedCheck_4457_ == 0 {
                    v_unused_4458_ = lean_ctor_get(v___x_4438_, 0);
                    lean_dec(v_unused_4458_);
                    v___x_4450_ = v___x_4438_;
                    v_isShared_4451_ = v_isSharedCheck_4457_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_canon_4447_);
                    lean_inc(v_issues_4446_);
                    lean_inc(v_extensions_4445_);
                    lean_inc(v_defEqI_4444_);
                    lean_inc(v_congrInfo_4443_);
                    lean_inc(v_getLevel_4442_);
                    lean_inc(v_inferType_4441_);
                    lean_inc(v_proofInstInfo_4440_);
                    lean_inc(v_maxFVar_4439_);
                    lean_dec(v___x_4438_);
                    v___x_4450_ = lean_box(0);
                    v_isShared_4451_ = v_isSharedCheck_4457_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4451_ == 0 {
                    lean_ctor_set(v___x_4450_, 0, v_snd_4437_);
                    v___x_4453_ = v___x_4450_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_snd_4437_);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 1, v_maxFVar_4439_);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 2, v_proofInstInfo_4440_);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 3, v_inferType_4441_);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 4, v_getLevel_4442_);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 5, v_congrInfo_4443_);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 6, v_defEqI_4444_);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 7, v_extensions_4445_);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 8, v_issues_4446_);
                    lean_ctor_set(v_reuseFailAlloc_4456_, 9, v_canon_4447_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4456_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_4448_,
                    );
                    v___x_4453_ = v_reuseFailAlloc_4456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4454_ = lean_st_ref_set(v_a_4412_, v___x_4453_);
                v___x_4455_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4455_, 0, v_fst_4436_);
                return v___x_4455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_betaRevS___redArg___boxed(
    mut v_f_4461_: *mut LeanObject,
    mut v_revArgs_4462_: *mut LeanObject,
    mut v_a_4463_: *mut LeanObject,
    mut v_a_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4465_: *mut LeanObject = core::ptr::null_mut();
    v_res_4465_ = l_Lean_Meta_Sym_betaRevS___redArg(v_f_4461_, v_revArgs_4462_, v_a_4463_);
    lean_dec(v_a_4463_);
    lean_dec_ref(v_revArgs_4462_);
    return v_res_4465_;
}
pub unsafe fn l_Lean_Meta_Sym_betaRevS(
    mut v_f_4466_: *mut LeanObject,
    mut v_revArgs_4467_: *mut LeanObject,
    mut v_a_4468_: *mut LeanObject,
    mut v_a_4469_: *mut LeanObject,
    mut v_a_4470_: *mut LeanObject,
    mut v_a_4471_: *mut LeanObject,
    mut v_a_4472_: *mut LeanObject,
    mut v_a_4473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    v___x_4475_ = l_Lean_Meta_Sym_betaRevS___redArg(v_f_4466_, v_revArgs_4467_, v_a_4469_);
    return v___x_4475_;
}
pub unsafe fn l_Lean_Meta_Sym_betaRevS___boxed(
    mut v_f_4476_: *mut LeanObject,
    mut v_revArgs_4477_: *mut LeanObject,
    mut v_a_4478_: *mut LeanObject,
    mut v_a_4479_: *mut LeanObject,
    mut v_a_4480_: *mut LeanObject,
    mut v_a_4481_: *mut LeanObject,
    mut v_a_4482_: *mut LeanObject,
    mut v_a_4483_: *mut LeanObject,
    mut v_a_4484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4485_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4483_);
    lean_dec_ref(v_a_4482_);
    lean_dec(v_a_4481_);
    lean_dec_ref(v_a_4480_);
    lean_dec(v_a_4479_);
    lean_dec_ref(v_a_4478_);
    lean_dec_ref(v_revArgs_4477_);
    return v_res_4485_;
}
pub unsafe fn l_Lean_Meta_Sym_betaS___redArg(
    mut v_f_4486_: *mut LeanObject,
    mut v_args_4487_: *mut LeanObject,
    mut v_a_4488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    v___x_4490_ = l_Array_reverse___redArg(v_args_4487_);
    v___x_4491_ = l_Lean_Meta_Sym_betaRevS___redArg(v_f_4486_, v___x_4490_, v_a_4488_);
    lean_dec_ref(v___x_4490_);
    return v___x_4491_;
}
pub unsafe fn l_Lean_Meta_Sym_betaS___redArg___boxed(
    mut v_f_4492_: *mut LeanObject,
    mut v_args_4493_: *mut LeanObject,
    mut v_a_4494_: *mut LeanObject,
    mut v_a_4495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4496_: *mut LeanObject = core::ptr::null_mut();
    v_res_4496_ = l_Lean_Meta_Sym_betaS___redArg(v_f_4492_, v_args_4493_, v_a_4494_);
    lean_dec(v_a_4494_);
    return v_res_4496_;
}
pub unsafe fn l_Lean_Meta_Sym_betaS(
    mut v_f_4497_: *mut LeanObject,
    mut v_args_4498_: *mut LeanObject,
    mut v_a_4499_: *mut LeanObject,
    mut v_a_4500_: *mut LeanObject,
    mut v_a_4501_: *mut LeanObject,
    mut v_a_4502_: *mut LeanObject,
    mut v_a_4503_: *mut LeanObject,
    mut v_a_4504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    v___x_4506_ = l_Lean_Meta_Sym_betaS___redArg(v_f_4497_, v_args_4498_, v_a_4500_);
    return v___x_4506_;
}
pub unsafe fn l_Lean_Meta_Sym_betaS___boxed(
    mut v_f_4507_: *mut LeanObject,
    mut v_args_4508_: *mut LeanObject,
    mut v_a_4509_: *mut LeanObject,
    mut v_a_4510_: *mut LeanObject,
    mut v_a_4511_: *mut LeanObject,
    mut v_a_4512_: *mut LeanObject,
    mut v_a_4513_: *mut LeanObject,
    mut v_a_4514_: *mut LeanObject,
    mut v_a_4515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4516_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4514_);
    lean_dec_ref(v_a_4513_);
    lean_dec(v_a_4512_);
    lean_dec_ref(v_a_4511_);
    lean_dec(v_a_4510_);
    lean_dec_ref(v_a_4509_);
    return v_res_4516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_InstantiateS(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_InstantiateS(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_InstantiateS(builtin);
}
