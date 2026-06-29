// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Anchor
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.MarkNestedSubsingletons Init.Omega
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop;
use crate::r#gen::Init::Data::Hashable::l_instHashableUInt64___lam__0___boxed;
use crate::r#gen::Init::Meta::Defs::lean_is_inaccessible_user_name;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_hasMacroScopes, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node2, l_Lean_mkAtom,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqUInt64___boxed,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isImplementationDetail, l_Lean_Name_isInternal};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasLooseBVars, l_Lean_Expr_sort___override,
    l_Lean_Literal_hash, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_userName;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_FVarId_getDecl___redArg, l_Lean_Meta_ParamInfo_isImplicit,
};
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfo;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::lean_is_matcher;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MarkNestedSubsingletons::{
    initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons,
    l_Lean_Meta_Grind_isMarkedSubsingletonConst,
    runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_SplitInfo_getExpr,
    l_Lean_Meta_Grind_anchorPrefixToString, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::PrivateName::{l_Lean_isPrivateName, l_Lean_privateToUserName};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_mk_array};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_sub, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_uint64_dec_eq,
    lean_uint64_mix_hash,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0: u64 =
    0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_getAnchor___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_getAnchor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instHashableUInt64___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instHasAnchorExprWithAnchor: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [104, 101, 120, 110, 117, 109, 0],
};
static mut l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11510626477845773464 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [97, 110, 99, 104, 111, 114, 0],
};
static mut l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        12570470872972041128 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [35, 0],
};
static mut l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0()
-> u64 {
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u64 = 0;
    v___x_947_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_948_ = lean_uint64_of_nat(v___x_947_);
    return v___x_948_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(
    mut v_n_949_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___y_951_: u8 = 0;
    let mut v___x_952_: u8 = 0;
    let mut v___x_953_: u8 = 0;
    let mut v___x_954_: u8 = 0;
    let mut v___x_955_: u64 = 0;
    let mut v_hash_956_: u64 = 0;
    let mut v___x_957_: u64 = 0;
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: u64 = 0;
    let mut v_hash_960_: u64 = 0;
    let mut v___x_961_: u64 = 0;
    let mut v___x_962_: u64 = 0;
    let mut v___x_963_: u8 = 0;
    let mut v___x_964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_963_ = l_Lean_Name_hasMacroScopes(v_n_949_);
                if v___x_963_ == 0 {
                    crate::leanh::lean_inc(v_n_949_);
                    v___x_964_ = lean_is_inaccessible_user_name(v_n_949_);
                    v___y_951_ = v___x_964_;
                    state = 1;
                    continue;
                } else {
                    v___y_951_ = v___x_963_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_951_ == 0 {
                    v___x_952_ = l_Lean_Name_isImplementationDetail(v_n_949_);
                    if v___x_952_ == 0 {
                        v___x_953_ = l_Lean_isPrivateName(v_n_949_);
                        if v___x_953_ == 0 {
                            v___x_954_ = l_Lean_Name_isInternal(v_n_949_);
                            if v___x_954_ == 0 {
                                if crate::leanh::lean_obj_tag(v_n_949_) == 0 {
                                    v___x_955_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0);
                                    return v___x_955_;
                                } else {
                                    v_hash_956_ = crate::leanh::lean_ctor_get_uint64(
                                        v_n_949_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                                            as u32,
                                    );
                                    crate::leanh::lean_dec(v_n_949_);
                                    return v_hash_956_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_n_949_);
                                v___x_957_ = 0u64;
                                return v___x_957_;
                            }
                        } else {
                            v___x_958_ = l_Lean_privateToUserName(v_n_949_);
                            if crate::leanh::lean_obj_tag(v___x_958_) == 0 {
                                v___x_959_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0);
                                return v___x_959_;
                            } else {
                                v_hash_960_ = crate::leanh::lean_ctor_get_uint64(
                                    v___x_958_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                                        as u32,
                                );
                                crate::leanh::lean_dec(v___x_958_);
                                return v_hash_960_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_n_949_);
                        v___x_961_ = 0u64;
                        return v___x_961_;
                    }
                } else {
                    crate::leanh::lean_dec(v_n_949_);
                    v___x_962_ = 0u64;
                    return v___x_962_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___boxed(
    mut v_n_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_966_: u64 = 0;
    let mut v_r_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_966_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_965_);
    v_r_967_ = crate::leanh::lean_box_uint64(v_res_966_);
    return v_r_967_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(
    mut v_a_968_: u64,
    mut v_b_969_: u64,
) -> u64 {
    let mut v___x_970_: u64 = 0;
    let mut v___x_971_: u8 = 0;
    v___x_970_ = 0u64;
    v___x_971_ = lean_uint64_dec_eq(v_a_968_, v___x_970_);
    if v___x_971_ == 0 {
        let mut v___x_972_: u8 = 0;
        v___x_972_ = lean_uint64_dec_eq(v_b_969_, v___x_970_);
        if v___x_972_ == 0 {
            let mut v___x_973_: u64 = 0;
            v___x_973_ = lean_uint64_mix_hash(v_a_968_, v_b_969_);
            return v___x_973_;
        } else {
            return v_a_968_;
        }
    } else {
        return v_b_969_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix___boxed(
    mut v_a_974_: *mut crate::leanh::LeanObject,
    mut v_b_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_976_: u64 = 0;
    let mut v_b_boxed_977_: u64 = 0;
    let mut v_res_978_: u64 = 0;
    let mut v_r_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_976_ = crate::leanh::lean_unbox_uint64(v_a_974_);
    crate::leanh::lean_dec_ref(v_a_974_);
    v_b_boxed_977_ = crate::leanh::lean_unbox_uint64(v_b_975_);
    crate::leanh::lean_dec_ref(v_b_975_);
    v_res_978_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(
        v_a_boxed_976_,
        v_b_boxed_977_,
    );
    v_r_979_ = crate::leanh::lean_box_uint64(v_res_978_);
    return v_r_979_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(
    mut v_declName_980_: *mut crate::leanh::LeanObject,
    mut v___y_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: u8 = 0;
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = lean_st_ref_get(v___y_981_);
    v_env_984_ = crate::leanh::lean_ctor_get(v___x_983_, 0);
    crate::leanh::lean_inc_ref(v_env_984_);
    crate::leanh::lean_dec(v___x_983_);
    v___x_985_ = lean_is_matcher(v_env_984_, v_declName_980_);
    v___x_986_ = crate::leanh::lean_box((v___x_985_) as usize);
    v___x_987_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_987_, 0, v___x_986_);
    return v___x_987_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg___boxed(
    mut v_declName_988_: *mut crate::leanh::LeanObject,
    mut v___y_989_: *mut crate::leanh::LeanObject,
    mut v___y_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_991_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(
        v_declName_988_,
        v___y_989_,
    );
    crate::leanh::lean_dec(v___y_989_);
    return v_res_991_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(
    mut v_declName_992_: *mut crate::leanh::LeanObject,
    mut v___y_993_: *mut crate::leanh::LeanObject,
    mut v___y_994_: *mut crate::leanh::LeanObject,
    mut v___y_995_: *mut crate::leanh::LeanObject,
    mut v___y_996_: *mut crate::leanh::LeanObject,
    mut v___y_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
    mut v___y_1000_: *mut crate::leanh::LeanObject,
    mut v___y_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(
        v_declName_992_,
        v___y_1001_,
    );
    return v___x_1003_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___boxed(
    mut v_declName_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
    mut v___y_1008_: *mut crate::leanh::LeanObject,
    mut v___y_1009_: *mut crate::leanh::LeanObject,
    mut v___y_1010_: *mut crate::leanh::LeanObject,
    mut v___y_1011_: *mut crate::leanh::LeanObject,
    mut v___y_1012_: *mut crate::leanh::LeanObject,
    mut v___y_1013_: *mut crate::leanh::LeanObject,
    mut v___y_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1015_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(
        v_declName_1004_,
        v___y_1005_,
        v___y_1006_,
        v___y_1007_,
        v___y_1008_,
        v___y_1009_,
        v___y_1010_,
        v___y_1011_,
        v___y_1012_,
        v___y_1013_,
    );
    crate::leanh::lean_dec(v___y_1013_);
    crate::leanh::lean_dec_ref(v___y_1012_);
    crate::leanh::lean_dec(v___y_1011_);
    crate::leanh::lean_dec_ref(v___y_1010_);
    crate::leanh::lean_dec(v___y_1009_);
    crate::leanh::lean_dec_ref(v___y_1008_);
    crate::leanh::lean_dec(v___y_1007_);
    crate::leanh::lean_dec_ref(v___y_1006_);
    crate::leanh::lean_dec(v___y_1005_);
    return v_res_1015_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(
    mut v_x_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
    mut v_x_1018_: *mut crate::leanh::LeanObject,
    mut v_x_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1024_: u8 = 0;
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1020_ = crate::leanh::lean_ctor_get(v_x_1016_, 0);
                v_vs_1021_ = crate::leanh::lean_ctor_get(v_x_1016_, 1);
                v_isSharedCheck_1045_ = (!crate::leanh::lean_is_exclusive(v_x_1016_)) as u8;
                if v_isSharedCheck_1045_ == 0 {
                    v___x_1023_ = v_x_1016_;
                    v_isShared_1024_ = v_isSharedCheck_1045_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1021_);
                    crate::leanh::lean_inc(v_ks_1020_);
                    crate::leanh::lean_dec(v_x_1016_);
                    v___x_1023_ = crate::leanh::lean_box(0);
                    v_isShared_1024_ = v_isSharedCheck_1045_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1025_ = lean_array_get_size(v_ks_1020_);
                v___x_1026_ = lean_nat_dec_lt(v_x_1017_, v___x_1025_);
                if v___x_1026_ == 0 {
                    crate::leanh::lean_dec(v_x_1017_);
                    v___x_1027_ = lean_array_push(v_ks_1020_, v_x_1018_);
                    v___x_1028_ = lean_array_push(v_vs_1021_, v_x_1019_);
                    if v_isShared_1024_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1023_, 1, v___x_1028_);
                        crate::leanh::lean_ctor_set(v___x_1023_, 0, v___x_1027_);
                        v___x_1030_ = v___x_1023_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1031_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1027_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___x_1028_);
                        v___x_1030_ = v_reuseFailAlloc_1031_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1032_ = lean_array_fget_borrowed(v_ks_1020_, v_x_1017_);
                    v___x_1033_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_1018_,
                            v_k_x27_1032_,
                        );
                    if v___x_1033_ == 0 {
                        if v_isShared_1024_ == 0 {
                            v___x_1035_ = v___x_1023_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1039_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_ks_1020_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_vs_1021_);
                            v___x_1035_ = v_reuseFailAlloc_1039_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1040_ = lean_array_fset(v_ks_1020_, v_x_1017_, v_x_1018_);
                        v___x_1041_ = lean_array_fset(v_vs_1021_, v_x_1017_, v_x_1019_);
                        crate::leanh::lean_dec(v_x_1017_);
                        if v_isShared_1024_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1023_, 1, v___x_1041_);
                            crate::leanh::lean_ctor_set(v___x_1023_, 0, v___x_1040_);
                            v___x_1043_ = v___x_1023_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1044_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1040_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1041_);
                            v___x_1043_ = v_reuseFailAlloc_1044_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1030_;
            }
            3 => {
                v___x_1036_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1037_ = lean_nat_add(v_x_1017_, v___x_1036_);
                crate::leanh::lean_dec(v_x_1017_);
                v_x_1016_ = v___x_1035_;
                v_x_1017_ = v___x_1037_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(
    mut v_n_1046_: *mut crate::leanh::LeanObject,
    mut v_k_1047_: *mut crate::leanh::LeanObject,
    mut v_v_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1049_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1050_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(v_n_1046_, v___x_1049_, v_k_1047_, v_v_1048_);
    return v___x_1050_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_1051_: usize = 0;
    let mut v___x_1052_: usize = 0;
    let mut v___x_1053_: usize = 0;
    v___x_1051_ = 5usize;
    v___x_1052_ = 1usize;
    v___x_1053_ = lean_usize_shift_left(v___x_1052_, v___x_1051_);
    return v___x_1053_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_1054_: usize = 0;
    let mut v___x_1055_: usize = 0;
    let mut v___x_1056_: usize = 0;
    v___x_1054_ = 1usize;
    v___x_1055_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0);
    v___x_1056_ = lean_usize_sub(v___x_1055_, v___x_1054_);
    return v___x_1056_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1057_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1057_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(
    mut v_x_1058_: *mut crate::leanh::LeanObject,
    mut v_x_1059_: usize,
    mut v_x_1060_: usize,
    mut v_x_1061_: *mut crate::leanh::LeanObject,
    mut v_x_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: usize = 0;
    let mut v___x_1065_: usize = 0;
    let mut v___x_1066_: usize = 0;
    let mut v___x_1067_: usize = 0;
    let mut v_j_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: u8 = 0;
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1073_: u8 = 0;
    let mut v_v_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1087_: u8 = 0;
    let mut v___x_1088_: u8 = 0;
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1094_: u8 = 0;
    let mut v_node_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1099_: usize = 0;
    let mut v___x_1100_: usize = 0;
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1105_: u8 = 0;
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut v_unused_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1113_: u8 = 0;
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1118_: u8 = 0;
    let mut v_ks_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: usize = 0;
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: u8 = 0;
    let mut v_reuseFailAlloc_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1058_) == 0 {
                    v_es_1063_ = crate::leanh::lean_ctor_get(v_x_1058_, 0);
                    v___x_1064_ = 5usize;
                    v___x_1065_ = 1usize;
                    v___x_1066_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1);
                    v___x_1067_ = lean_usize_land(v_x_1059_, v___x_1066_);
                    v_j_1068_ = lean_usize_to_nat(v___x_1067_);
                    v___x_1069_ = lean_array_get_size(v_es_1063_);
                    v___x_1070_ = lean_nat_dec_lt(v_j_1068_, v___x_1069_);
                    if v___x_1070_ == 0 {
                        crate::leanh::lean_dec(v_j_1068_);
                        crate::leanh::lean_dec(v_x_1062_);
                        crate::leanh::lean_dec_ref(v_x_1061_);
                        return v_x_1058_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1063_);
                        v_isSharedCheck_1107_ = (!crate::leanh::lean_is_exclusive(v_x_1058_)) as u8;
                        if v_isSharedCheck_1107_ == 0 {
                            v_unused_1108_ = crate::leanh::lean_ctor_get(v_x_1058_, 0);
                            crate::leanh::lean_dec(v_unused_1108_);
                            v___x_1072_ = v_x_1058_;
                            v_isShared_1073_ = v_isSharedCheck_1107_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1058_);
                            v___x_1072_ = crate::leanh::lean_box(0);
                            v_isShared_1073_ = v_isSharedCheck_1107_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1109_ = crate::leanh::lean_ctor_get(v_x_1058_, 0);
                    v_vs_1110_ = crate::leanh::lean_ctor_get(v_x_1058_, 1);
                    v_isSharedCheck_1130_ = (!crate::leanh::lean_is_exclusive(v_x_1058_)) as u8;
                    if v_isSharedCheck_1130_ == 0 {
                        v___x_1112_ = v_x_1058_;
                        v_isShared_1113_ = v_isSharedCheck_1130_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1110_);
                        crate::leanh::lean_inc(v_ks_1109_);
                        crate::leanh::lean_dec(v_x_1058_);
                        v___x_1112_ = crate::leanh::lean_box(0);
                        v_isShared_1113_ = v_isSharedCheck_1130_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1074_ = lean_array_fget(v_es_1063_, v_j_1068_);
                v___x_1075_ = crate::leanh::lean_box(0);
                v_xs_x27_1076_ = lean_array_fset(v_es_1063_, v_j_1068_, v___x_1075_);
                match crate::leanh::lean_obj_tag(v_v_1074_) {
                    0 => {
                        v_key_1083_ = crate::leanh::lean_ctor_get(v_v_1074_, 0);
                        v_val_1084_ = crate::leanh::lean_ctor_get(v_v_1074_, 1);
                        v_isSharedCheck_1094_ = (!crate::leanh::lean_is_exclusive(v_v_1074_)) as u8;
                        if v_isSharedCheck_1094_ == 0 {
                            v___x_1086_ = v_v_1074_;
                            v_isShared_1087_ = v_isSharedCheck_1094_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1084_);
                            crate::leanh::lean_inc(v_key_1083_);
                            crate::leanh::lean_dec(v_v_1074_);
                            v___x_1086_ = crate::leanh::lean_box(0);
                            v_isShared_1087_ = v_isSharedCheck_1094_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1095_ = crate::leanh::lean_ctor_get(v_v_1074_, 0);
                        v_isSharedCheck_1105_ = (!crate::leanh::lean_is_exclusive(v_v_1074_)) as u8;
                        if v_isSharedCheck_1105_ == 0 {
                            v___x_1097_ = v_v_1074_;
                            v_isShared_1098_ = v_isSharedCheck_1105_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1095_);
                            crate::leanh::lean_dec(v_v_1074_);
                            v___x_1097_ = crate::leanh::lean_box(0);
                            v_isShared_1098_ = v_isSharedCheck_1105_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1106_, 0, v_x_1061_);
                        crate::leanh::lean_ctor_set(v___x_1106_, 1, v_x_1062_);
                        v___y_1078_ = v___x_1106_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1079_ = lean_array_fset(v_xs_x27_1076_, v_j_1068_, v___y_1078_);
                crate::leanh::lean_dec(v_j_1068_);
                if v_isShared_1073_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1079_);
                    v___x_1081_ = v___x_1072_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
                    v___x_1081_ = v_reuseFailAlloc_1082_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1081_;
            }
            4 => {
                v___x_1088_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_1061_,
                        v_key_1083_,
                    );
                if v___x_1088_ == 0 {
                    crate::leanh::lean_del_object(v___x_1086_);
                    v___x_1089_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1083_,
                        v_val_1084_,
                        v_x_1061_,
                        v_x_1062_,
                    );
                    v___x_1090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1090_, 0, v___x_1089_);
                    v___y_1078_ = v___x_1090_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1084_);
                    crate::leanh::lean_dec(v_key_1083_);
                    if v_isShared_1087_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1086_, 1, v_x_1062_);
                        crate::leanh::lean_ctor_set(v___x_1086_, 0, v_x_1061_);
                        v___x_1092_ = v___x_1086_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1093_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_x_1061_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_x_1062_);
                        v___x_1092_ = v_reuseFailAlloc_1093_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1078_ = v___x_1092_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1099_ = lean_usize_shift_right(v_x_1059_, v___x_1064_);
                v___x_1100_ = lean_usize_add(v_x_1060_, v___x_1065_);
                v___x_1101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_node_1095_, v___x_1099_, v___x_1100_, v_x_1061_, v_x_1062_);
                if v_isShared_1098_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1097_, 0, v___x_1101_);
                    v___x_1103_ = v___x_1097_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
                    v___x_1103_ = v_reuseFailAlloc_1104_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1078_ = v___x_1103_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1113_ == 0 {
                    v___x_1115_ = v___x_1112_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1129_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_ks_1109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_vs_1110_);
                    v___x_1115_ = v_reuseFailAlloc_1129_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1116_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v___x_1115_, v_x_1061_, v_x_1062_);
                v___x_1124_ = 7usize;
                v___x_1125_ = lean_usize_dec_le(v___x_1124_, v_x_1060_);
                if v___x_1125_ == 0 {
                    v___x_1126_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1116_);
                    v___x_1127_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1128_ = lean_nat_dec_lt(v___x_1126_, v___x_1127_);
                    crate::leanh::lean_dec(v___x_1126_);
                    v___y_1118_ = v___x_1128_;
                    state = 10;
                    continue;
                } else {
                    v___y_1118_ = v___x_1125_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1118_ == 0 {
                    v_ks_1119_ = crate::leanh::lean_ctor_get(v_newNode_1116_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1119_);
                    v_vs_1120_ = crate::leanh::lean_ctor_get(v_newNode_1116_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1120_);
                    crate::leanh::lean_dec_ref(v_newNode_1116_);
                    v___x_1121_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1122_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2);
                    v___x_1123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_x_1060_, v_ks_1119_, v_vs_1120_, v___x_1121_, v___x_1122_);
                    crate::leanh::lean_dec_ref(v_vs_1120_);
                    crate::leanh::lean_dec_ref(v_ks_1119_);
                    return v___x_1123_;
                } else {
                    return v_newNode_1116_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(
    mut v_depth_1131_: usize,
    mut v_keys_1132_: *mut crate::leanh::LeanObject,
    mut v_vals_1133_: *mut crate::leanh::LeanObject,
    mut v_i_1134_: *mut crate::leanh::LeanObject,
    mut v_entries_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    let mut v_k_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: u64 = 0;
    let mut v_h_1141_: usize = 0;
    let mut v___x_1142_: usize = 0;
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: usize = 0;
    let mut v___x_1145_: usize = 0;
    let mut v___x_1146_: usize = 0;
    let mut v_h_1147_: usize = 0;
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1136_ = lean_array_get_size(v_keys_1132_);
                v___x_1137_ = lean_nat_dec_lt(v_i_1134_, v___x_1136_);
                if v___x_1137_ == 0 {
                    crate::leanh::lean_dec(v_i_1134_);
                    return v_entries_1135_;
                } else {
                    v_k_1138_ = lean_array_fget_borrowed(v_keys_1132_, v_i_1134_);
                    v_v_1139_ = lean_array_fget_borrowed(v_vals_1133_, v_i_1134_);
                    v___x_1140_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1138_);
                    v_h_1141_ = lean_uint64_to_usize(v___x_1140_);
                    v___x_1142_ = 5usize;
                    v___x_1143_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1144_ = 1usize;
                    v___x_1145_ = lean_usize_sub(v_depth_1131_, v___x_1144_);
                    v___x_1146_ = lean_usize_mul(v___x_1142_, v___x_1145_);
                    v_h_1147_ = lean_usize_shift_right(v_h_1141_, v___x_1146_);
                    v___x_1148_ = lean_nat_add(v_i_1134_, v___x_1143_);
                    crate::leanh::lean_dec(v_i_1134_);
                    crate::leanh::lean_inc(v_v_1139_);
                    crate::leanh::lean_inc(v_k_1138_);
                    v___x_1149_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_entries_1135_, v_h_1147_, v_depth_1131_, v_k_1138_, v_v_1139_);
                    v_i_1134_ = v___x_1148_;
                    v_entries_1135_ = v___x_1149_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_depth_1151_: *mut crate::leanh::LeanObject,
    mut v_keys_1152_: *mut crate::leanh::LeanObject,
    mut v_vals_1153_: *mut crate::leanh::LeanObject,
    mut v_i_1154_: *mut crate::leanh::LeanObject,
    mut v_entries_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1156_: usize = 0;
    let mut v_res_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1156_ = crate::leanh::lean_unbox_usize(v_depth_1151_);
    crate::leanh::lean_dec(v_depth_1151_);
    v_res_1157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_boxed_1156_, v_keys_1152_, v_vals_1153_, v_i_1154_, v_entries_1155_);
    crate::leanh::lean_dec_ref(v_vals_1153_);
    crate::leanh::lean_dec_ref(v_keys_1152_);
    return v_res_1157_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___boxed(
    mut v_x_1158_: *mut crate::leanh::LeanObject,
    mut v_x_1159_: *mut crate::leanh::LeanObject,
    mut v_x_1160_: *mut crate::leanh::LeanObject,
    mut v_x_1161_: *mut crate::leanh::LeanObject,
    mut v_x_1162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_32485__boxed_1163_: usize = 0;
    let mut v_x_32486__boxed_1164_: usize = 0;
    let mut v_res_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_32485__boxed_1163_ = crate::leanh::lean_unbox_usize(v_x_1159_);
    crate::leanh::lean_dec(v_x_1159_);
    v_x_32486__boxed_1164_ = crate::leanh::lean_unbox_usize(v_x_1160_);
    crate::leanh::lean_dec(v_x_1160_);
    v_res_1165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_1158_, v_x_32485__boxed_1163_, v_x_32486__boxed_1164_, v_x_1161_, v_x_1162_);
    return v_res_1165_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(
    mut v_x_1166_: *mut crate::leanh::LeanObject,
    mut v_x_1167_: *mut crate::leanh::LeanObject,
    mut v_x_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1169_: u64 = 0;
    let mut v___x_1170_: usize = 0;
    let mut v___x_1171_: usize = 0;
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1167_);
    v___x_1170_ = lean_uint64_to_usize(v___x_1169_);
    v___x_1171_ = 1usize;
    v___x_1172_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_1166_, v___x_1170_, v___x_1171_, v_x_1167_, v_x_1168_);
    return v___x_1172_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(
    mut v_keys_1173_: *mut crate::leanh::LeanObject,
    mut v_vals_1174_: *mut crate::leanh::LeanObject,
    mut v_i_1175_: *mut crate::leanh::LeanObject,
    mut v_k_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: u8 = 0;
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1177_ = lean_array_get_size(v_keys_1173_);
                v___x_1178_ = lean_nat_dec_lt(v_i_1175_, v___x_1177_);
                if v___x_1178_ == 0 {
                    crate::leanh::lean_dec(v_i_1175_);
                    v___x_1179_ = crate::leanh::lean_box(0);
                    return v___x_1179_;
                } else {
                    v_k_x27_1180_ = lean_array_fget_borrowed(v_keys_1173_, v_i_1175_);
                    v___x_1181_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1176_,
                            v_k_x27_1180_,
                        );
                    if v___x_1181_ == 0 {
                        v___x_1182_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1183_ = lean_nat_add(v_i_1175_, v___x_1182_);
                        crate::leanh::lean_dec(v_i_1175_);
                        v_i_1175_ = v___x_1183_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1185_ = lean_array_fget_borrowed(v_vals_1174_, v_i_1175_);
                        crate::leanh::lean_dec(v_i_1175_);
                        crate::leanh::lean_inc(v___x_1185_);
                        v___x_1186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1186_, 0, v___x_1185_);
                        return v___x_1186_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg___boxed(
    mut v_keys_1187_: *mut crate::leanh::LeanObject,
    mut v_vals_1188_: *mut crate::leanh::LeanObject,
    mut v_i_1189_: *mut crate::leanh::LeanObject,
    mut v_k_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1191_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_1187_, v_vals_1188_, v_i_1189_, v_k_1190_);
    crate::leanh::lean_dec_ref(v_k_1190_);
    crate::leanh::lean_dec_ref(v_vals_1188_);
    crate::leanh::lean_dec_ref(v_keys_1187_);
    return v_res_1191_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(
    mut v_x_1192_: *mut crate::leanh::LeanObject,
    mut v_x_1193_: usize,
    mut v_x_1194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut v_j_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: usize = 0;
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1192_) == 0 {
                    v_es_1195_ = crate::leanh::lean_ctor_get(v_x_1192_, 0);
                    v___x_1196_ = crate::leanh::lean_box(2);
                    v___x_1197_ = 5usize;
                    v___x_1198_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1);
                    v___x_1199_ = lean_usize_land(v_x_1193_, v___x_1198_);
                    v_j_1200_ = lean_usize_to_nat(v___x_1199_);
                    v___x_1201_ = lean_array_get_borrowed(v___x_1196_, v_es_1195_, v_j_1200_);
                    crate::leanh::lean_dec(v_j_1200_);
                    match crate::leanh::lean_obj_tag(v___x_1201_) {
                        0 => {
                            v_key_1202_ = crate::leanh::lean_ctor_get(v___x_1201_, 0);
                            v_val_1203_ = crate::leanh::lean_ctor_get(v___x_1201_, 1);
                            v___x_1204_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1194_, v_key_1202_);
                            if v___x_1204_ == 0 {
                                v___x_1205_ = crate::leanh::lean_box(0);
                                return v___x_1205_;
                            } else {
                                crate::leanh::lean_inc(v_val_1203_);
                                v___x_1206_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1206_, 0, v_val_1203_);
                                return v___x_1206_;
                            }
                        }
                        1 => {
                            v_node_1207_ = crate::leanh::lean_ctor_get(v___x_1201_, 0);
                            v___x_1208_ = lean_usize_shift_right(v_x_1193_, v___x_1197_);
                            v_x_1192_ = v_node_1207_;
                            v_x_1193_ = v___x_1208_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1210_ = crate::leanh::lean_box(0);
                            return v___x_1210_;
                        }
                    }
                } else {
                    v_ks_1211_ = crate::leanh::lean_ctor_get(v_x_1192_, 0);
                    v_vs_1212_ = crate::leanh::lean_ctor_get(v_x_1192_, 1);
                    v___x_1213_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1214_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_ks_1211_, v_vs_1212_, v___x_1213_, v_x_1194_);
                    return v___x_1214_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(
    mut v_x_1215_: *mut crate::leanh::LeanObject,
    mut v_x_1216_: *mut crate::leanh::LeanObject,
    mut v_x_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_32685__boxed_1218_: usize = 0;
    let mut v_res_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_32685__boxed_1218_ = crate::leanh::lean_unbox_usize(v_x_1216_);
    crate::leanh::lean_dec(v_x_1216_);
    v_res_1219_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_1215_, v_x_32685__boxed_1218_, v_x_1217_);
    crate::leanh::lean_dec_ref(v_x_1217_);
    crate::leanh::lean_dec_ref(v_x_1215_);
    return v_res_1219_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(
    mut v_x_1220_: *mut crate::leanh::LeanObject,
    mut v_x_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1222_: u64 = 0;
    let mut v___x_1223_: usize = 0;
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1222_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1221_);
    v___x_1223_ = lean_uint64_to_usize(v___x_1222_);
    v___x_1224_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_1220_, v___x_1223_, v_x_1221_);
    return v___x_1224_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(
    mut v_x_1225_: *mut crate::leanh::LeanObject,
    mut v_x_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1227_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(
            v_x_1225_, v_x_1226_,
        );
    crate::leanh::lean_dec_ref(v_x_1226_);
    crate::leanh::lean_dec_ref(v_x_1225_);
    return v_res_1227_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getAnchor___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1228_ = crate::leanh::lean_box(0);
    v_dummy_1229_ = l_Lean_Expr_sort___override(v___x_1228_);
    return v_dummy_1229_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(
    mut v_x_1232_: *mut crate::leanh::LeanObject,
    mut v_x_1233_: *mut crate::leanh::LeanObject,
    mut v_x_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
    mut v___y_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
    mut v___y_1238_: *mut crate::leanh::LeanObject,
    mut v___y_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pinfos_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: u64 = 0;
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1263_: u8 = 0;
    let mut v___x_1264_: u8 = 0;
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1232_) == 5 {
                    v_fn_1282_ = crate::leanh::lean_ctor_get(v_x_1232_, 0);
                    crate::leanh::lean_inc_ref(v_fn_1282_);
                    v_arg_1283_ = crate::leanh::lean_ctor_get(v_x_1232_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1283_);
                    crate::leanh::lean_dec_ref_known(v_x_1232_, 2);
                    v___x_1284_ = lean_array_set(v_x_1233_, v_x_1234_, v_arg_1283_);
                    v___x_1285_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1286_ = lean_nat_sub(v_x_1234_, v___x_1285_);
                    crate::leanh::lean_dec(v_x_1234_);
                    v_x_1232_ = v_fn_1282_;
                    v_x_1233_ = v___x_1284_;
                    v_x_1234_ = v___x_1286_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_1234_);
                    v___x_1288_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_x_1232_);
                    if v___x_1288_ == 0 {
                        v___y_1263_ = v___x_1288_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1289_ = lean_array_get_size(v_x_1233_);
                        v___x_1290_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1291_ = lean_nat_dec_eq(v___x_1289_, v___x_1290_);
                        v___y_1263_ = v___x_1291_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1256_ = l_Lean_Meta_Grind_getAnchor(
                    v_x_1232_,
                    v___y_1247_,
                    v___y_1248_,
                    v___y_1249_,
                    v___y_1250_,
                    v___y_1251_,
                    v___y_1252_,
                    v___y_1253_,
                    v___y_1254_,
                    v___y_1255_,
                );
                if crate::leanh::lean_obj_tag(v___x_1256_) == 0 {
                    v_a_1257_ = crate::leanh::lean_ctor_get(v___x_1256_, 0);
                    crate::leanh::lean_inc(v_a_1257_);
                    crate::leanh::lean_dec_ref_known(v___x_1256_, 1);
                    v___x_1258_ = lean_array_get_size(v_x_1233_);
                    v___x_1259_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1260_ = crate::leanh::lean_unbox_uint64(v_a_1257_);
                    crate::leanh::lean_dec(v_a_1257_);
                    v___x_1261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v___x_1258_, v_x_1233_, v_pinfos_1246_, v___x_1259_, v___x_1260_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
                    crate::leanh::lean_dec_ref(v_pinfos_1246_);
                    crate::leanh::lean_dec_ref(v_x_1233_);
                    return v___x_1261_;
                } else {
                    crate::leanh::lean_dec_ref(v_pinfos_1246_);
                    crate::leanh::lean_dec_ref(v_x_1233_);
                    return v___x_1256_;
                }
            }
            2 => {
                if v___y_1263_ == 0 {
                    v___x_1264_ = l_Lean_Expr_hasLooseBVars(v_x_1232_);
                    if v___x_1264_ == 0 {
                        v___x_1265_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc_ref(v_x_1232_);
                        v___x_1266_ = l_Lean_Meta_getFunInfo(
                            v_x_1232_,
                            v___x_1265_,
                            v___y_1240_,
                            v___y_1241_,
                            v___y_1242_,
                            v___y_1243_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1266_) == 0 {
                            v_a_1267_ = crate::leanh::lean_ctor_get(v___x_1266_, 0);
                            crate::leanh::lean_inc(v_a_1267_);
                            crate::leanh::lean_dec_ref_known(v___x_1266_, 1);
                            v_paramInfo_1268_ = crate::leanh::lean_ctor_get(v_a_1267_, 0);
                            crate::leanh::lean_inc_ref(v_paramInfo_1268_);
                            crate::leanh::lean_dec(v_a_1267_);
                            v_pinfos_1246_ = v_paramInfo_1268_;
                            v___y_1247_ = v___y_1235_;
                            v___y_1248_ = v___y_1236_;
                            v___y_1249_ = v___y_1237_;
                            v___y_1250_ = v___y_1238_;
                            v___y_1251_ = v___y_1239_;
                            v___y_1252_ = v___y_1240_;
                            v___y_1253_ = v___y_1241_;
                            v___y_1254_ = v___y_1242_;
                            v___y_1255_ = v___y_1243_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_x_1233_);
                            crate::leanh::lean_dec_ref(v_x_1232_);
                            v_a_1269_ = crate::leanh::lean_ctor_get(v___x_1266_, 0);
                            v_isSharedCheck_1276_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1266_)) as u8;
                            if v_isSharedCheck_1276_ == 0 {
                                v___x_1271_ = v___x_1266_;
                                v_isShared_1272_ = v_isSharedCheck_1276_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1269_);
                                crate::leanh::lean_dec(v___x_1266_);
                                v___x_1271_ = crate::leanh::lean_box(0);
                                v_isShared_1272_ = v_isSharedCheck_1276_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_1277_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0;
                        v_pinfos_1246_ = v___x_1277_;
                        v___y_1247_ = v___y_1235_;
                        v___y_1248_ = v___y_1236_;
                        v___y_1249_ = v___y_1237_;
                        v___y_1250_ = v___y_1238_;
                        v___y_1251_ = v___y_1239_;
                        v___y_1252_ = v___y_1240_;
                        v___y_1253_ = v___y_1241_;
                        v___y_1254_ = v___y_1242_;
                        v___y_1255_ = v___y_1243_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_1232_);
                    v___x_1278_ = l_Lean_instInhabitedExpr;
                    v___x_1279_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1280_ = lean_array_get(v___x_1278_, v_x_1233_, v___x_1279_);
                    crate::leanh::lean_dec_ref(v_x_1233_);
                    v___x_1281_ = l_Lean_Meta_Grind_getAnchor(
                        v___x_1280_,
                        v___y_1235_,
                        v___y_1236_,
                        v___y_1237_,
                        v___y_1238_,
                        v___y_1239_,
                        v___y_1240_,
                        v___y_1241_,
                        v___y_1242_,
                        v___y_1243_,
                    );
                    return v___x_1281_;
                }
            }
            3 => {
                if v_isShared_1272_ == 0 {
                    v___x_1274_ = v___x_1271_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
                    v___x_1274_ = v_reuseFailAlloc_1275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getAnchor(
    mut v_e_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_a_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
    mut v_a_1296_: *mut crate::leanh::LeanObject,
    mut v_a_1297_: *mut crate::leanh::LeanObject,
    mut v_a_1298_: *mut crate::leanh::LeanObject,
    mut v_a_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
    mut v_a_1301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1304_: u64 = 0;
    let mut v___y_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrThms_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastTag_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counters_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitDiags_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematchDiags_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulEqCmpMap_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reflCmpMap_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instanceMap_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut v_n_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: u64 = 0;
    let mut v___x_1347_: u64 = 0;
    let mut v___x_1348_: u64 = 0;
    let mut v___x_1349_: u64 = 0;
    let mut v___x_1350_: u64 = 0;
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut v_deBruijnIndex_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: u64 = 0;
    let mut v_fvarId_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u64 = 0;
    let mut v_a_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1376_: u8 = 0;
    let mut v_declName_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: u64 = 0;
    let mut v___x_1382_: u64 = 0;
    let mut v_a_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut v_dummy_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: u64 = 0;
    let mut v_binderName_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u64 = 0;
    let mut v___x_1416_: u64 = 0;
    let mut v___x_1417_: u64 = 0;
    let mut v___x_1418_: u64 = 0;
    let mut v___x_1419_: u64 = 0;
    let mut v___x_1420_: u64 = 0;
    let mut v___x_1421_: u64 = 0;
    let mut v_a_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: u64 = 0;
    let mut v_expr_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: u64 = 0;
    let mut v_idx_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u64 = 0;
    let mut v___x_1433_: u64 = 0;
    let mut v___x_1434_: u64 = 0;
    let mut v___x_1435_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1351_ = lean_st_ref_get(v_a_1295_);
                v_anchors_1352_ = crate::leanh::lean_ctor_get(v___x_1351_, 8);
                crate::leanh::lean_inc_ref(v_anchors_1352_);
                crate::leanh::lean_dec(v___x_1351_);
                v___x_1353_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_anchors_1352_, v_e_1292_);
                crate::leanh::lean_dec_ref(v_anchors_1352_);
                if crate::leanh::lean_obj_tag(v___x_1353_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_1292_);
                    v_val_1354_ = crate::leanh::lean_ctor_get(v___x_1353_, 0);
                    v_isSharedCheck_1361_ = (!crate::leanh::lean_is_exclusive(v___x_1353_)) as u8;
                    if v_isSharedCheck_1361_ == 0 {
                        v___x_1356_ = v___x_1353_;
                        v_isShared_1357_ = v_isSharedCheck_1361_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1354_);
                        crate::leanh::lean_dec(v___x_1353_);
                        v___x_1356_ = crate::leanh::lean_box(0);
                        v_isShared_1357_ = v_isSharedCheck_1361_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1353_);
                    match crate::leanh::lean_obj_tag(v_e_1292_) {
                        0 => {
                            v_deBruijnIndex_1362_ = crate::leanh::lean_ctor_get(v_e_1292_, 0);
                            v___x_1363_ = lean_uint64_of_nat(v_deBruijnIndex_1362_);
                            v_a_1304_ = v___x_1363_;
                            v___y_1305_ = v_a_1295_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_fvarId_1364_ = crate::leanh::lean_ctor_get(v_e_1292_, 0);
                            crate::leanh::lean_inc(v_fvarId_1364_);
                            v___x_1365_ = l_Lean_FVarId_getDecl___redArg(
                                v_fvarId_1364_,
                                v_a_1298_,
                                v_a_1300_,
                                v_a_1301_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1365_) == 0 {
                                v_a_1366_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                                crate::leanh::lean_inc(v_a_1366_);
                                crate::leanh::lean_dec_ref_known(v___x_1365_, 1);
                                v___x_1367_ = l_Lean_LocalDecl_userName(v_a_1366_);
                                crate::leanh::lean_dec(v_a_1366_);
                                v___x_1368_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v___x_1367_);
                                v_a_1304_ = v___x_1368_;
                                v___y_1305_ = v_a_1295_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_1292_, 1);
                                v_a_1369_ = crate::leanh::lean_ctor_get(v___x_1365_, 0);
                                v_isSharedCheck_1376_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1365_)) as u8;
                                if v_isSharedCheck_1376_ == 0 {
                                    v___x_1371_ = v___x_1365_;
                                    v_isShared_1372_ = v_isSharedCheck_1376_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1369_);
                                    crate::leanh::lean_dec(v___x_1365_);
                                    v___x_1371_ = crate::leanh::lean_box(0);
                                    v_isShared_1372_ = v_isSharedCheck_1376_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                        4 => {
                            v_declName_1377_ = crate::leanh::lean_ctor_get(v_e_1292_, 0);
                            crate::leanh::lean_inc(v_declName_1377_);
                            v___x_1378_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_1377_, v_a_1301_);
                            if crate::leanh::lean_obj_tag(v___x_1378_) == 0 {
                                v_a_1379_ = crate::leanh::lean_ctor_get(v___x_1378_, 0);
                                crate::leanh::lean_inc(v_a_1379_);
                                crate::leanh::lean_dec_ref_known(v___x_1378_, 1);
                                v___x_1380_ = (crate::leanh::lean_unbox(v_a_1379_) as u8);
                                crate::leanh::lean_dec(v_a_1379_);
                                if v___x_1380_ == 0 {
                                    crate::leanh::lean_inc(v_declName_1377_);
                                    v___x_1381_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_1377_);
                                    v_a_1304_ = v___x_1381_;
                                    v___y_1305_ = v_a_1295_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1382_ = 0u64;
                                    v_a_1304_ = v___x_1382_;
                                    v___y_1305_ = v_a_1295_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_1292_, 2);
                                v_a_1383_ = crate::leanh::lean_ctor_get(v___x_1378_, 0);
                                v_isSharedCheck_1390_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1378_)) as u8;
                                if v_isSharedCheck_1390_ == 0 {
                                    v___x_1385_ = v___x_1378_;
                                    v_isShared_1386_ = v_isSharedCheck_1390_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1383_);
                                    crate::leanh::lean_dec(v___x_1378_);
                                    v___x_1385_ = crate::leanh::lean_box(0);
                                    v_isShared_1386_ = v_isSharedCheck_1390_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                        5 => {
                            v_dummy_1391_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getAnchor___closed__0),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_getAnchor___closed__0_once
                                ),
                                _init_l_Lean_Meta_Grind_getAnchor___closed__0,
                            );
                            v_nargs_1392_ = l_Lean_Expr_getAppNumArgs(v_e_1292_);
                            crate::leanh::lean_inc(v_nargs_1392_);
                            v___x_1393_ = lean_mk_array(v_nargs_1392_, v_dummy_1391_);
                            v___x_1394_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1395_ = lean_nat_sub(v_nargs_1392_, v___x_1394_);
                            crate::leanh::lean_dec(v_nargs_1392_);
                            crate::leanh::lean_inc_ref(v_e_1292_);
                            v___x_1396_ =
                                l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(
                                    v_e_1292_,
                                    v___x_1393_,
                                    v___x_1395_,
                                    v_a_1293_,
                                    v_a_1294_,
                                    v_a_1295_,
                                    v_a_1296_,
                                    v_a_1297_,
                                    v_a_1298_,
                                    v_a_1299_,
                                    v_a_1300_,
                                    v_a_1301_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_1396_) == 0 {
                                v_a_1397_ = crate::leanh::lean_ctor_get(v___x_1396_, 0);
                                crate::leanh::lean_inc(v_a_1397_);
                                crate::leanh::lean_dec_ref_known(v___x_1396_, 1);
                                v___x_1398_ = crate::leanh::lean_unbox_uint64(v_a_1397_);
                                crate::leanh::lean_dec(v_a_1397_);
                                v_a_1304_ = v___x_1398_;
                                v___y_1305_ = v_a_1295_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_1292_, 2);
                                return v___x_1396_;
                            }
                        }
                        6 => {
                            v_binderName_1399_ = crate::leanh::lean_ctor_get(v_e_1292_, 0);
                            v_binderType_1400_ = crate::leanh::lean_ctor_get(v_e_1292_, 1);
                            v_body_1401_ = crate::leanh::lean_ctor_get(v_e_1292_, 2);
                            crate::leanh::lean_inc_ref(v_body_1401_);
                            crate::leanh::lean_inc_ref(v_binderType_1400_);
                            crate::leanh::lean_inc(v_binderName_1399_);
                            v_n_1330_ = v_binderName_1399_;
                            v_d_1331_ = v_binderType_1400_;
                            v_b_1332_ = v_body_1401_;
                            v___y_1333_ = v_a_1293_;
                            v___y_1334_ = v_a_1294_;
                            v___y_1335_ = v_a_1295_;
                            v___y_1336_ = v_a_1296_;
                            v___y_1337_ = v_a_1297_;
                            v___y_1338_ = v_a_1298_;
                            v___y_1339_ = v_a_1299_;
                            v___y_1340_ = v_a_1300_;
                            v___y_1341_ = v_a_1301_;
                            state = 4;
                            continue;
                        }
                        7 => {
                            v_binderName_1402_ = crate::leanh::lean_ctor_get(v_e_1292_, 0);
                            v_binderType_1403_ = crate::leanh::lean_ctor_get(v_e_1292_, 1);
                            v_body_1404_ = crate::leanh::lean_ctor_get(v_e_1292_, 2);
                            crate::leanh::lean_inc_ref(v_body_1404_);
                            crate::leanh::lean_inc_ref(v_binderType_1403_);
                            crate::leanh::lean_inc(v_binderName_1402_);
                            v_n_1330_ = v_binderName_1402_;
                            v_d_1331_ = v_binderType_1403_;
                            v_b_1332_ = v_body_1404_;
                            v___y_1333_ = v_a_1293_;
                            v___y_1334_ = v_a_1294_;
                            v___y_1335_ = v_a_1295_;
                            v___y_1336_ = v_a_1296_;
                            v___y_1337_ = v_a_1297_;
                            v___y_1338_ = v_a_1298_;
                            v___y_1339_ = v_a_1299_;
                            v___y_1340_ = v_a_1300_;
                            v___y_1341_ = v_a_1301_;
                            state = 4;
                            continue;
                        }
                        8 => {
                            v_declName_1405_ = crate::leanh::lean_ctor_get(v_e_1292_, 0);
                            v_type_1406_ = crate::leanh::lean_ctor_get(v_e_1292_, 1);
                            v_value_1407_ = crate::leanh::lean_ctor_get(v_e_1292_, 2);
                            v_body_1408_ = crate::leanh::lean_ctor_get(v_e_1292_, 3);
                            crate::leanh::lean_inc_ref(v_value_1407_);
                            v___x_1409_ = l_Lean_Meta_Grind_getAnchor(
                                v_value_1407_,
                                v_a_1293_,
                                v_a_1294_,
                                v_a_1295_,
                                v_a_1296_,
                                v_a_1297_,
                                v_a_1298_,
                                v_a_1299_,
                                v_a_1300_,
                                v_a_1301_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1409_) == 0 {
                                v_a_1410_ = crate::leanh::lean_ctor_get(v___x_1409_, 0);
                                crate::leanh::lean_inc(v_a_1410_);
                                crate::leanh::lean_dec_ref_known(v___x_1409_, 1);
                                crate::leanh::lean_inc_ref(v_type_1406_);
                                v___x_1411_ = l_Lean_Meta_Grind_getAnchor(
                                    v_type_1406_,
                                    v_a_1293_,
                                    v_a_1294_,
                                    v_a_1295_,
                                    v_a_1296_,
                                    v_a_1297_,
                                    v_a_1298_,
                                    v_a_1299_,
                                    v_a_1300_,
                                    v_a_1301_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1411_) == 0 {
                                    v_a_1412_ = crate::leanh::lean_ctor_get(v___x_1411_, 0);
                                    crate::leanh::lean_inc(v_a_1412_);
                                    crate::leanh::lean_dec_ref_known(v___x_1411_, 1);
                                    crate::leanh::lean_inc_ref(v_body_1408_);
                                    v___x_1413_ = l_Lean_Meta_Grind_getAnchor(
                                        v_body_1408_,
                                        v_a_1293_,
                                        v_a_1294_,
                                        v_a_1295_,
                                        v_a_1296_,
                                        v_a_1297_,
                                        v_a_1298_,
                                        v_a_1299_,
                                        v_a_1300_,
                                        v_a_1301_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_1413_) == 0 {
                                        v_a_1414_ = crate::leanh::lean_ctor_get(v___x_1413_, 0);
                                        crate::leanh::lean_inc(v_a_1414_);
                                        crate::leanh::lean_dec_ref_known(v___x_1413_, 1);
                                        crate::leanh::lean_inc(v_declName_1405_);
                                        v___x_1415_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_1405_);
                                        v___x_1416_ = crate::leanh::lean_unbox_uint64(v_a_1412_);
                                        crate::leanh::lean_dec(v_a_1412_);
                                        v___x_1417_ = crate::leanh::lean_unbox_uint64(v_a_1414_);
                                        crate::leanh::lean_dec(v_a_1414_);
                                        v___x_1418_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_1416_, v___x_1417_);
                                        v___x_1419_ = crate::leanh::lean_unbox_uint64(v_a_1410_);
                                        crate::leanh::lean_dec(v_a_1410_);
                                        v___x_1420_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_1419_, v___x_1418_);
                                        v___x_1421_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_1415_, v___x_1420_);
                                        v_a_1304_ = v___x_1421_;
                                        v___y_1305_ = v_a_1295_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_1412_);
                                        crate::leanh::lean_dec(v_a_1410_);
                                        crate::leanh::lean_dec_ref_known(v_e_1292_, 4);
                                        return v___x_1413_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1410_);
                                    crate::leanh::lean_dec_ref_known(v_e_1292_, 4);
                                    return v___x_1411_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_1292_, 4);
                                return v___x_1409_;
                            }
                        }
                        9 => {
                            v_a_1422_ = crate::leanh::lean_ctor_get(v_e_1292_, 0);
                            v___x_1423_ = l_Lean_Literal_hash(v_a_1422_);
                            v_a_1304_ = v___x_1423_;
                            v___y_1305_ = v_a_1295_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_expr_1424_ = crate::leanh::lean_ctor_get(v_e_1292_, 1);
                            crate::leanh::lean_inc_ref(v_expr_1424_);
                            v___x_1425_ = l_Lean_Meta_Grind_getAnchor(
                                v_expr_1424_,
                                v_a_1293_,
                                v_a_1294_,
                                v_a_1295_,
                                v_a_1296_,
                                v_a_1297_,
                                v_a_1298_,
                                v_a_1299_,
                                v_a_1300_,
                                v_a_1301_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1425_) == 0 {
                                v_a_1426_ = crate::leanh::lean_ctor_get(v___x_1425_, 0);
                                crate::leanh::lean_inc(v_a_1426_);
                                crate::leanh::lean_dec_ref_known(v___x_1425_, 1);
                                v___x_1427_ = crate::leanh::lean_unbox_uint64(v_a_1426_);
                                crate::leanh::lean_dec(v_a_1426_);
                                v_a_1304_ = v___x_1427_;
                                v___y_1305_ = v_a_1295_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_1292_, 2);
                                return v___x_1425_;
                            }
                        }
                        11 => {
                            v_idx_1428_ = crate::leanh::lean_ctor_get(v_e_1292_, 1);
                            v_struct_1429_ = crate::leanh::lean_ctor_get(v_e_1292_, 2);
                            crate::leanh::lean_inc_ref(v_struct_1429_);
                            v___x_1430_ = l_Lean_Meta_Grind_getAnchor(
                                v_struct_1429_,
                                v_a_1293_,
                                v_a_1294_,
                                v_a_1295_,
                                v_a_1296_,
                                v_a_1297_,
                                v_a_1298_,
                                v_a_1299_,
                                v_a_1300_,
                                v_a_1301_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1430_) == 0 {
                                v_a_1431_ = crate::leanh::lean_ctor_get(v___x_1430_, 0);
                                crate::leanh::lean_inc(v_a_1431_);
                                crate::leanh::lean_dec_ref_known(v___x_1430_, 1);
                                v___x_1432_ = lean_uint64_of_nat(v_idx_1428_);
                                v___x_1433_ = crate::leanh::lean_unbox_uint64(v_a_1431_);
                                crate::leanh::lean_dec(v_a_1431_);
                                v___x_1434_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_1432_, v___x_1433_);
                                v_a_1304_ = v___x_1434_;
                                v___y_1305_ = v_a_1295_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_1292_, 3);
                                return v___x_1430_;
                            }
                        }
                        _ => {
                            v___x_1435_ = 0u64;
                            v_a_1304_ = v___x_1435_;
                            v___y_1305_ = v_a_1295_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1306_ = lean_st_ref_take(v___y_1305_);
                v_congrThms_1307_ = crate::leanh::lean_ctor_get(v___x_1306_, 0);
                v_simp_1308_ = crate::leanh::lean_ctor_get(v___x_1306_, 1);
                v_lastTag_1309_ = crate::leanh::lean_ctor_get(v___x_1306_, 2);
                v_counters_1310_ = crate::leanh::lean_ctor_get(v___x_1306_, 3);
                v_splitDiags_1311_ = crate::leanh::lean_ctor_get(v___x_1306_, 4);
                v_ematchDiags_1312_ = crate::leanh::lean_ctor_get(v___x_1306_, 5);
                v_lawfulEqCmpMap_1313_ = crate::leanh::lean_ctor_get(v___x_1306_, 6);
                v_reflCmpMap_1314_ = crate::leanh::lean_ctor_get(v___x_1306_, 7);
                v_anchors_1315_ = crate::leanh::lean_ctor_get(v___x_1306_, 8);
                v_instanceMap_1316_ = crate::leanh::lean_ctor_get(v___x_1306_, 9);
                v_isSharedCheck_1328_ = (!crate::leanh::lean_is_exclusive(v___x_1306_)) as u8;
                if v_isSharedCheck_1328_ == 0 {
                    v___x_1318_ = v___x_1306_;
                    v_isShared_1319_ = v_isSharedCheck_1328_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_instanceMap_1316_);
                    crate::leanh::lean_inc(v_anchors_1315_);
                    crate::leanh::lean_inc(v_reflCmpMap_1314_);
                    crate::leanh::lean_inc(v_lawfulEqCmpMap_1313_);
                    crate::leanh::lean_inc(v_ematchDiags_1312_);
                    crate::leanh::lean_inc(v_splitDiags_1311_);
                    crate::leanh::lean_inc(v_counters_1310_);
                    crate::leanh::lean_inc(v_lastTag_1309_);
                    crate::leanh::lean_inc(v_simp_1308_);
                    crate::leanh::lean_inc(v_congrThms_1307_);
                    crate::leanh::lean_dec(v___x_1306_);
                    v___x_1318_ = crate::leanh::lean_box(0);
                    v_isShared_1319_ = v_isSharedCheck_1328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1320_ = crate::leanh::lean_box_uint64(v_a_1304_);
                v___x_1321_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_anchors_1315_, v_e_1292_, v___x_1320_);
                if v_isShared_1319_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1318_, 8, v___x_1321_);
                    v___x_1323_ = v___x_1318_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_congrThms_1307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_simp_1308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_lastTag_1309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_counters_1310_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 4, v_splitDiags_1311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 5, v_ematchDiags_1312_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 6, v_lawfulEqCmpMap_1313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 7, v_reflCmpMap_1314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 8, v___x_1321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 9, v_instanceMap_1316_);
                    v___x_1323_ = v_reuseFailAlloc_1327_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1324_ = lean_st_ref_set(v___y_1305_, v___x_1323_);
                v___x_1325_ = crate::leanh::lean_box_uint64(v_a_1304_);
                v___x_1326_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1326_, 0, v___x_1325_);
                return v___x_1326_;
            }
            4 => {
                v___x_1342_ = l_Lean_Meta_Grind_getAnchor(
                    v_d_1331_,
                    v___y_1333_,
                    v___y_1334_,
                    v___y_1335_,
                    v___y_1336_,
                    v___y_1337_,
                    v___y_1338_,
                    v___y_1339_,
                    v___y_1340_,
                    v___y_1341_,
                );
                if crate::leanh::lean_obj_tag(v___x_1342_) == 0 {
                    v_a_1343_ = crate::leanh::lean_ctor_get(v___x_1342_, 0);
                    crate::leanh::lean_inc(v_a_1343_);
                    crate::leanh::lean_dec_ref_known(v___x_1342_, 1);
                    v___x_1344_ = l_Lean_Meta_Grind_getAnchor(
                        v_b_1332_,
                        v___y_1333_,
                        v___y_1334_,
                        v___y_1335_,
                        v___y_1336_,
                        v___y_1337_,
                        v___y_1338_,
                        v___y_1339_,
                        v___y_1340_,
                        v___y_1341_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1344_) == 0 {
                        v_a_1345_ = crate::leanh::lean_ctor_get(v___x_1344_, 0);
                        crate::leanh::lean_inc(v_a_1345_);
                        crate::leanh::lean_dec_ref_known(v___x_1344_, 1);
                        v___x_1346_ =
                            l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(
                                v_n_1330_,
                            );
                        v___x_1347_ = crate::leanh::lean_unbox_uint64(v_a_1343_);
                        crate::leanh::lean_dec(v_a_1343_);
                        v___x_1348_ = crate::leanh::lean_unbox_uint64(v_a_1345_);
                        crate::leanh::lean_dec(v_a_1345_);
                        v___x_1349_ =
                            l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(
                                v___x_1347_,
                                v___x_1348_,
                            );
                        v___x_1350_ =
                            l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(
                                v___x_1346_,
                                v___x_1349_,
                            );
                        v_a_1304_ = v___x_1350_;
                        v___y_1305_ = v___y_1335_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_1343_);
                        crate::leanh::lean_dec(v_n_1330_);
                        crate::leanh::lean_dec_ref(v_e_1292_);
                        return v___x_1344_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_1332_);
                    crate::leanh::lean_dec(v_n_1330_);
                    crate::leanh::lean_dec_ref(v_e_1292_);
                    return v___x_1342_;
                }
            }
            5 => {
                if v_isShared_1357_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1356_, 0);
                    v___x_1359_ = v___x_1356_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_val_1354_);
                    v___x_1359_ = v_reuseFailAlloc_1360_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1359_;
            }
            7 => {
                if v_isShared_1372_ == 0 {
                    v___x_1374_ = v___x_1371_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
                    v___x_1374_ = v_reuseFailAlloc_1375_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1374_;
            }
            9 => {
                if v_isShared_1386_ == 0 {
                    v___x_1388_ = v___x_1385_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
                    v___x_1388_ = v_reuseFailAlloc_1389_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(
    mut v_upperBound_1436_: *mut crate::leanh::LeanObject,
    mut v_args_1437_: *mut crate::leanh::LeanObject,
    mut v_pinfos_1438_: *mut crate::leanh::LeanObject,
    mut v_a_1439_: *mut crate::leanh::LeanObject,
    mut v_b_1440_: u64,
    mut v___y_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
    mut v___y_1447_: *mut crate::leanh::LeanObject,
    mut v___y_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1452_: u64 = 0;
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u64 = 0;
    let mut v___x_1465_: u64 = 0;
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: u8 = 0;
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: u64 = 0;
    let mut v___x_1471_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1456_ = lean_nat_dec_lt(v_a_1439_, v_upperBound_1436_);
                if v___x_1456_ == 0 {
                    crate::leanh::lean_dec(v_a_1439_);
                    v___x_1457_ = crate::leanh::lean_box_uint64(v_b_1440_);
                    v___x_1458_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
                    return v___x_1458_;
                } else {
                    v___x_1459_ = lean_array_fget_borrowed(v_args_1437_, v_a_1439_);
                    v___x_1460_ = lean_array_get_size(v_pinfos_1438_);
                    v___x_1461_ = lean_nat_dec_lt(v_a_1439_, v___x_1460_);
                    if v___x_1461_ == 0 {
                        crate::leanh::lean_inc(v___x_1459_);
                        v___x_1462_ = l_Lean_Meta_Grind_getAnchor(
                            v___x_1459_,
                            v___y_1441_,
                            v___y_1442_,
                            v___y_1443_,
                            v___y_1444_,
                            v___y_1445_,
                            v___y_1446_,
                            v___y_1447_,
                            v___y_1448_,
                            v___y_1449_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1462_) == 0 {
                            v_a_1463_ = crate::leanh::lean_ctor_get(v___x_1462_, 0);
                            crate::leanh::lean_inc(v_a_1463_);
                            crate::leanh::lean_dec_ref_known(v___x_1462_, 1);
                            v___x_1464_ = crate::leanh::lean_unbox_uint64(v_a_1463_);
                            crate::leanh::lean_dec(v_a_1463_);
                            v___x_1465_ =
                                l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(
                                    v_b_1440_,
                                    v___x_1464_,
                                );
                            v_a_1452_ = v___x_1465_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_1439_);
                            return v___x_1462_;
                        }
                    } else {
                        v___x_1466_ = lean_array_fget_borrowed(v_pinfos_1438_, v_a_1439_);
                        v___x_1467_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_1466_);
                        if v___x_1467_ == 0 {
                            crate::leanh::lean_inc(v___x_1459_);
                            v___x_1468_ = l_Lean_Meta_Grind_getAnchor(
                                v___x_1459_,
                                v___y_1441_,
                                v___y_1442_,
                                v___y_1443_,
                                v___y_1444_,
                                v___y_1445_,
                                v___y_1446_,
                                v___y_1447_,
                                v___y_1448_,
                                v___y_1449_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1468_) == 0 {
                                v_a_1469_ = crate::leanh::lean_ctor_get(v___x_1468_, 0);
                                crate::leanh::lean_inc(v_a_1469_);
                                crate::leanh::lean_dec_ref_known(v___x_1468_, 1);
                                v___x_1470_ = crate::leanh::lean_unbox_uint64(v_a_1469_);
                                crate::leanh::lean_dec(v_a_1469_);
                                v___x_1471_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_1440_, v___x_1470_);
                                v_a_1452_ = v___x_1471_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_1439_);
                                return v___x_1468_;
                            }
                        } else {
                            v_a_1452_ = v_b_1440_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1453_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1454_ = lean_nat_add(v_a_1439_, v___x_1453_);
                crate::leanh::lean_dec(v_a_1439_);
                v_a_1439_ = v___x_1454_;
                v_b_1440_ = v_a_1452_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg___boxed(
    mut v_upperBound_1472_: *mut crate::leanh::LeanObject,
    mut v_args_1473_: *mut crate::leanh::LeanObject,
    mut v_pinfos_1474_: *mut crate::leanh::LeanObject,
    mut v_a_1475_: *mut crate::leanh::LeanObject,
    mut v_b_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
    mut v___y_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
    mut v___y_1480_: *mut crate::leanh::LeanObject,
    mut v___y_1481_: *mut crate::leanh::LeanObject,
    mut v___y_1482_: *mut crate::leanh::LeanObject,
    mut v___y_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
    mut v___y_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_1487_: u64 = 0;
    let mut v_res_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1487_ = crate::leanh::lean_unbox_uint64(v_b_1476_);
    crate::leanh::lean_dec_ref(v_b_1476_);
    v_res_1488_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(
        v_upperBound_1472_,
        v_args_1473_,
        v_pinfos_1474_,
        v_a_1475_,
        v_b_boxed_1487_,
        v___y_1477_,
        v___y_1478_,
        v___y_1479_,
        v___y_1480_,
        v___y_1481_,
        v___y_1482_,
        v___y_1483_,
        v___y_1484_,
        v___y_1485_,
    );
    crate::leanh::lean_dec(v___y_1485_);
    crate::leanh::lean_dec_ref(v___y_1484_);
    crate::leanh::lean_dec(v___y_1483_);
    crate::leanh::lean_dec_ref(v___y_1482_);
    crate::leanh::lean_dec(v___y_1481_);
    crate::leanh::lean_dec_ref(v___y_1480_);
    crate::leanh::lean_dec(v___y_1479_);
    crate::leanh::lean_dec_ref(v___y_1478_);
    crate::leanh::lean_dec(v___y_1477_);
    crate::leanh::lean_dec_ref(v_pinfos_1474_);
    crate::leanh::lean_dec_ref(v_args_1473_);
    crate::leanh::lean_dec(v_upperBound_1472_);
    return v_res_1488_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(
    mut v_x_1489_: *mut crate::leanh::LeanObject,
    mut v_x_1490_: *mut crate::leanh::LeanObject,
    mut v_x_1491_: *mut crate::leanh::LeanObject,
    mut v___y_1492_: *mut crate::leanh::LeanObject,
    mut v___y_1493_: *mut crate::leanh::LeanObject,
    mut v___y_1494_: *mut crate::leanh::LeanObject,
    mut v___y_1495_: *mut crate::leanh::LeanObject,
    mut v___y_1496_: *mut crate::leanh::LeanObject,
    mut v___y_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
    mut v___y_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(
        v_x_1489_,
        v_x_1490_,
        v_x_1491_,
        v___y_1492_,
        v___y_1493_,
        v___y_1494_,
        v___y_1495_,
        v___y_1496_,
        v___y_1497_,
        v___y_1498_,
        v___y_1499_,
        v___y_1500_,
    );
    crate::leanh::lean_dec(v___y_1500_);
    crate::leanh::lean_dec_ref(v___y_1499_);
    crate::leanh::lean_dec(v___y_1498_);
    crate::leanh::lean_dec_ref(v___y_1497_);
    crate::leanh::lean_dec(v___y_1496_);
    crate::leanh::lean_dec_ref(v___y_1495_);
    crate::leanh::lean_dec(v___y_1494_);
    crate::leanh::lean_dec_ref(v___y_1493_);
    crate::leanh::lean_dec(v___y_1492_);
    return v_res_1502_;
}
pub unsafe fn l_Lean_Meta_Grind_getAnchor___boxed(
    mut v_e_1503_: *mut crate::leanh::LeanObject,
    mut v_a_1504_: *mut crate::leanh::LeanObject,
    mut v_a_1505_: *mut crate::leanh::LeanObject,
    mut v_a_1506_: *mut crate::leanh::LeanObject,
    mut v_a_1507_: *mut crate::leanh::LeanObject,
    mut v_a_1508_: *mut crate::leanh::LeanObject,
    mut v_a_1509_: *mut crate::leanh::LeanObject,
    mut v_a_1510_: *mut crate::leanh::LeanObject,
    mut v_a_1511_: *mut crate::leanh::LeanObject,
    mut v_a_1512_: *mut crate::leanh::LeanObject,
    mut v_a_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1514_ = l_Lean_Meta_Grind_getAnchor(
        v_e_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_,
        v_a_1511_, v_a_1512_,
    );
    crate::leanh::lean_dec(v_a_1512_);
    crate::leanh::lean_dec_ref(v_a_1511_);
    crate::leanh::lean_dec(v_a_1510_);
    crate::leanh::lean_dec_ref(v_a_1509_);
    crate::leanh::lean_dec(v_a_1508_);
    crate::leanh::lean_dec_ref(v_a_1507_);
    crate::leanh::lean_dec(v_a_1506_);
    crate::leanh::lean_dec_ref(v_a_1505_);
    crate::leanh::lean_dec(v_a_1504_);
    return v_res_1514_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(
    mut v_upperBound_1515_: *mut crate::leanh::LeanObject,
    mut v_args_1516_: *mut crate::leanh::LeanObject,
    mut v_pinfos_1517_: *mut crate::leanh::LeanObject,
    mut v_inst_1518_: *mut crate::leanh::LeanObject,
    mut v_R_1519_: *mut crate::leanh::LeanObject,
    mut v_a_1520_: *mut crate::leanh::LeanObject,
    mut v_b_1521_: u64,
    mut v_c_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
    mut v___y_1525_: *mut crate::leanh::LeanObject,
    mut v___y_1526_: *mut crate::leanh::LeanObject,
    mut v___y_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
    mut v___y_1531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1533_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(
        v_upperBound_1515_,
        v_args_1516_,
        v_pinfos_1517_,
        v_a_1520_,
        v_b_1521_,
        v___y_1523_,
        v___y_1524_,
        v___y_1525_,
        v___y_1526_,
        v___y_1527_,
        v___y_1528_,
        v___y_1529_,
        v___y_1530_,
        v___y_1531_,
    );
    return v___x_1533_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_1534_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_args_1535_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_pinfos_1536_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_inst_1537_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_R_1538_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_1539_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_b_1540_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_c_1541_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_1542_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_1543_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_1544_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_1545_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_1546_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_1547_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_1548_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_1549_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1550_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_1551_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_b_boxed_1552_: u64 = 0;
    let mut v_res_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1552_ = crate::leanh::lean_unbox_uint64(v_b_1540_);
    crate::leanh::lean_dec_ref(v_b_1540_);
    v_res_1553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(
        v_upperBound_1534_,
        v_args_1535_,
        v_pinfos_1536_,
        v_inst_1537_,
        v_R_1538_,
        v_a_1539_,
        v_b_boxed_1552_,
        v_c_1541_,
        v___y_1542_,
        v___y_1543_,
        v___y_1544_,
        v___y_1545_,
        v___y_1546_,
        v___y_1547_,
        v___y_1548_,
        v___y_1549_,
        v___y_1550_,
    );
    crate::leanh::lean_dec(v___y_1550_);
    crate::leanh::lean_dec_ref(v___y_1549_);
    crate::leanh::lean_dec(v___y_1548_);
    crate::leanh::lean_dec_ref(v___y_1547_);
    crate::leanh::lean_dec(v___y_1546_);
    crate::leanh::lean_dec_ref(v___y_1545_);
    crate::leanh::lean_dec(v___y_1544_);
    crate::leanh::lean_dec_ref(v___y_1543_);
    crate::leanh::lean_dec(v___y_1542_);
    crate::leanh::lean_dec_ref(v_pinfos_1536_);
    crate::leanh::lean_dec_ref(v_args_1535_);
    crate::leanh::lean_dec(v_upperBound_1534_);
    return v_res_1553_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1(
    mut v_00_u03b2_1554_: *mut crate::leanh::LeanObject,
    mut v_x_1555_: *mut crate::leanh::LeanObject,
    mut v_x_1556_: *mut crate::leanh::LeanObject,
    mut v_x_1557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(
            v_x_1555_, v_x_1556_, v_x_1557_,
        );
    return v___x_1558_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(
    mut v_00_u03b2_1559_: *mut crate::leanh::LeanObject,
    mut v_x_1560_: *mut crate::leanh::LeanObject,
    mut v_x_1561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(
            v_x_1560_, v_x_1561_,
        );
    return v___x_1562_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(
    mut v_00_u03b2_1563_: *mut crate::leanh::LeanObject,
    mut v_x_1564_: *mut crate::leanh::LeanObject,
    mut v_x_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1566_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(
        v_00_u03b2_1563_,
        v_x_1564_,
        v_x_1565_,
    );
    crate::leanh::lean_dec_ref(v_x_1565_);
    crate::leanh::lean_dec_ref(v_x_1564_);
    return v_res_1566_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(
    mut v_00_u03b2_1567_: *mut crate::leanh::LeanObject,
    mut v_x_1568_: *mut crate::leanh::LeanObject,
    mut v_x_1569_: usize,
    mut v_x_1570_: usize,
    mut v_x_1571_: *mut crate::leanh::LeanObject,
    mut v_x_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_1568_, v_x_1569_, v_x_1570_, v_x_1571_, v_x_1572_);
    return v___x_1573_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___boxed(
    mut v_00_u03b2_1574_: *mut crate::leanh::LeanObject,
    mut v_x_1575_: *mut crate::leanh::LeanObject,
    mut v_x_1576_: *mut crate::leanh::LeanObject,
    mut v_x_1577_: *mut crate::leanh::LeanObject,
    mut v_x_1578_: *mut crate::leanh::LeanObject,
    mut v_x_1579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33267__boxed_1580_: usize = 0;
    let mut v_x_33268__boxed_1581_: usize = 0;
    let mut v_res_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33267__boxed_1580_ = crate::leanh::lean_unbox_usize(v_x_1576_);
    crate::leanh::lean_dec(v_x_1576_);
    v_x_33268__boxed_1581_ = crate::leanh::lean_unbox_usize(v_x_1577_);
    crate::leanh::lean_dec(v_x_1577_);
    v_res_1582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(v_00_u03b2_1574_, v_x_1575_, v_x_33267__boxed_1580_, v_x_33268__boxed_1581_, v_x_1578_, v_x_1579_);
    return v_res_1582_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(
    mut v_00_u03b2_1583_: *mut crate::leanh::LeanObject,
    mut v_x_1584_: *mut crate::leanh::LeanObject,
    mut v_x_1585_: usize,
    mut v_x_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_1584_, v_x_1585_, v_x_1586_);
    return v___x_1587_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(
    mut v_00_u03b2_1588_: *mut crate::leanh::LeanObject,
    mut v_x_1589_: *mut crate::leanh::LeanObject,
    mut v_x_1590_: *mut crate::leanh::LeanObject,
    mut v_x_1591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33284__boxed_1592_: usize = 0;
    let mut v_res_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33284__boxed_1592_ = crate::leanh::lean_unbox_usize(v_x_1590_);
    crate::leanh::lean_dec(v_x_1590_);
    v_res_1593_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(v_00_u03b2_1588_, v_x_1589_, v_x_33284__boxed_1592_, v_x_1591_);
    crate::leanh::lean_dec_ref(v_x_1591_);
    crate::leanh::lean_dec_ref(v_x_1589_);
    return v_res_1593_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3(
    mut v_00_u03b2_1594_: *mut crate::leanh::LeanObject,
    mut v_n_1595_: *mut crate::leanh::LeanObject,
    mut v_k_1596_: *mut crate::leanh::LeanObject,
    mut v_v_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v_n_1595_, v_k_1596_, v_v_1597_);
    return v___x_1598_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(
    mut v_00_u03b2_1599_: *mut crate::leanh::LeanObject,
    mut v_depth_1600_: usize,
    mut v_keys_1601_: *mut crate::leanh::LeanObject,
    mut v_vals_1602_: *mut crate::leanh::LeanObject,
    mut v_heq_1603_: *mut crate::leanh::LeanObject,
    mut v_i_1604_: *mut crate::leanh::LeanObject,
    mut v_entries_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_1600_, v_keys_1601_, v_vals_1602_, v_i_1604_, v_entries_1605_);
    return v___x_1606_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___boxed(
    mut v_00_u03b2_1607_: *mut crate::leanh::LeanObject,
    mut v_depth_1608_: *mut crate::leanh::LeanObject,
    mut v_keys_1609_: *mut crate::leanh::LeanObject,
    mut v_vals_1610_: *mut crate::leanh::LeanObject,
    mut v_heq_1611_: *mut crate::leanh::LeanObject,
    mut v_i_1612_: *mut crate::leanh::LeanObject,
    mut v_entries_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1614_: usize = 0;
    let mut v_res_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1614_ = crate::leanh::lean_unbox_usize(v_depth_1608_);
    crate::leanh::lean_dec(v_depth_1608_);
    v_res_1615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(v_00_u03b2_1607_, v_depth_boxed_1614_, v_keys_1609_, v_vals_1610_, v_heq_1611_, v_i_1612_, v_entries_1613_);
    crate::leanh::lean_dec_ref(v_vals_1610_);
    crate::leanh::lean_dec_ref(v_keys_1609_);
    return v_res_1615_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(
    mut v_00_u03b2_1616_: *mut crate::leanh::LeanObject,
    mut v_keys_1617_: *mut crate::leanh::LeanObject,
    mut v_vals_1618_: *mut crate::leanh::LeanObject,
    mut v_heq_1619_: *mut crate::leanh::LeanObject,
    mut v_i_1620_: *mut crate::leanh::LeanObject,
    mut v_k_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_1617_, v_vals_1618_, v_i_1620_, v_k_1621_);
    return v___x_1622_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(
    mut v_00_u03b2_1623_: *mut crate::leanh::LeanObject,
    mut v_keys_1624_: *mut crate::leanh::LeanObject,
    mut v_vals_1625_: *mut crate::leanh::LeanObject,
    mut v_heq_1626_: *mut crate::leanh::LeanObject,
    mut v_i_1627_: *mut crate::leanh::LeanObject,
    mut v_k_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1629_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(v_00_u03b2_1623_, v_keys_1624_, v_vals_1625_, v_heq_1626_, v_i_1627_, v_k_1628_);
    crate::leanh::lean_dec_ref(v_k_1628_);
    crate::leanh::lean_dec_ref(v_vals_1625_);
    crate::leanh::lean_dec_ref(v_keys_1624_);
    return v_res_1629_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6(
    mut v_00_u03b2_1630_: *mut crate::leanh::LeanObject,
    mut v_x_1631_: *mut crate::leanh::LeanObject,
    mut v_x_1632_: *mut crate::leanh::LeanObject,
    mut v_x_1633_: *mut crate::leanh::LeanObject,
    mut v_x_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(v_x_1631_, v_x_1632_, v_x_1633_, v_x_1634_);
    return v___x_1635_;
}
pub unsafe fn l_Lean_Meta_Grind_AnchorRef_matches(
    mut v_anchorRef_1636_: *mut crate::leanh::LeanObject,
    mut v_anchor_1637_: u64,
) -> u8 {
    let mut v_numDigits_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchorPrefix_1639_: u64 = 0;
    let mut v___x_1640_: u64 = 0;
    let mut v___x_1641_: u64 = 0;
    let mut v___x_1642_: u64 = 0;
    let mut v___x_1643_: u64 = 0;
    let mut v_shift_1644_: u64 = 0;
    let mut v___x_1645_: u64 = 0;
    let mut v___x_1646_: u8 = 0;
    v_numDigits_1638_ = crate::leanh::lean_ctor_get(v_anchorRef_1636_, 0);
    v_anchorPrefix_1639_ = crate::leanh::lean_ctor_get_uint64(
        v_anchorRef_1636_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v___x_1640_ = 64u64;
    v___x_1641_ = lean_uint64_of_nat(v_numDigits_1638_);
    v___x_1642_ = 2u64;
    v___x_1643_ = lean_uint64_shift_left(v___x_1641_, v___x_1642_);
    v_shift_1644_ = lean_uint64_sub(v___x_1640_, v___x_1643_);
    v___x_1645_ = lean_uint64_shift_right(v_anchor_1637_, v_shift_1644_);
    v___x_1646_ = lean_uint64_dec_eq(v_anchorPrefix_1639_, v___x_1645_);
    return v___x_1646_;
}
pub unsafe fn l_Lean_Meta_Grind_AnchorRef_matches___boxed(
    mut v_anchorRef_1647_: *mut crate::leanh::LeanObject,
    mut v_anchor_1648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anchor_boxed_1649_: u64 = 0;
    let mut v_res_1650_: u8 = 0;
    let mut v_r_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anchor_boxed_1649_ = crate::leanh::lean_unbox_uint64(v_anchor_1648_);
    crate::leanh::lean_dec_ref(v_anchor_1648_);
    v_res_1650_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_1647_, v_anchor_boxed_1649_);
    crate::leanh::lean_dec_ref(v_anchorRef_1647_);
    v_r_1651_ = crate::leanh::lean_box((v_res_1650_) as usize);
    return v_r_1651_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqUInt64___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_1653_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1653_, 0, v___x_1652_);
    return v___f_1653_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(
    mut v_inst_1674_: *mut crate::leanh::LeanObject,
    mut v_shift_1675_: *mut crate::leanh::LeanObject,
    mut v___f_1676_: *mut crate::leanh::LeanObject,
    mut v___f_1677_: *mut crate::leanh::LeanObject,
    mut v___x_1678_: *mut crate::leanh::LeanObject,
    mut v_numDigits_1679_: *mut crate::leanh::LeanObject,
    mut v_es_1680_: *mut crate::leanh::LeanObject,
    mut v_a_1681_: *mut crate::leanh::LeanObject,
    mut v_x_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1684_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_1674_, v_shift_1675_, v___f_1676_, v___f_1677_, v___x_1678_, v_numDigits_1679_, v_es_1680_, v_a_1681_, v_x_1682_, v___y_1683_);
    crate::leanh::lean_dec(v_numDigits_1679_);
    crate::leanh::lean_dec(v_shift_1675_);
    return v_res_1684_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = crate::leanh::lean_box(0);
    v___x_1686_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1687_ = lean_mk_array(v___x_1686_, v___x_1685_);
    return v___x_1687_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2);
    v___x_1689_ = crate::leanh::lean_unsigned_to_nat(0);
    v_found_1690_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_found_1690_, 0, v___x_1689_);
    crate::leanh::lean_ctor_set(v_found_1690_, 1, v___x_1688_);
    return v_found_1690_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v_found_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_found_1691_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3);
    v___x_1692_ = crate::leanh::lean_box(0);
    v___x_1693_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1693_, 0, v___x_1692_);
    crate::leanh::lean_ctor_set(v___x_1693_, 1, v_found_1691_);
    return v___x_1693_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(
    mut v_inst_1694_: *mut crate::leanh::LeanObject,
    mut v_es_1695_: *mut crate::leanh::LeanObject,
    mut v_numDigits_1696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: u8 = 0;
    v___x_1697_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1698_ = lean_nat_mul(v___x_1697_, v_numDigits_1696_);
    v___x_1699_ = crate::leanh::lean_unsigned_to_nat(64);
    v___x_1700_ = lean_nat_dec_lt(v___x_1698_, v___x_1699_);
    if v___x_1700_ == 0 {
        crate::leanh::lean_dec(v___x_1698_);
        crate::leanh::lean_dec_ref(v_es_1695_);
        crate::leanh::lean_dec_ref(v_inst_1694_);
        return v_numDigits_1696_;
    } else {
        let mut v_shift_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1708_: usize = 0;
        let mut v___x_1709_: usize = 0;
        let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_shift_1701_ = lean_nat_sub(v___x_1699_, v___x_1698_);
        crate::leanh::lean_dec(v___x_1698_);
        v___f_1702_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0);
        v___f_1703_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1;
        v___x_1704_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13;
        v___x_1705_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc_ref(v_es_1695_);
        crate::leanh::lean_inc(v_numDigits_1696_);
        v___f_1706_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 7);
        crate::leanh::lean_closure_set(v___f_1706_, 0, v_inst_1694_);
        crate::leanh::lean_closure_set(v___f_1706_, 1, v_shift_1701_);
        crate::leanh::lean_closure_set(v___f_1706_, 2, v___f_1702_);
        crate::leanh::lean_closure_set(v___f_1706_, 3, v___f_1703_);
        crate::leanh::lean_closure_set(v___f_1706_, 4, v___x_1705_);
        crate::leanh::lean_closure_set(v___f_1706_, 5, v_numDigits_1696_);
        crate::leanh::lean_closure_set(v___f_1706_, 6, v_es_1695_);
        v___x_1707_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
        v_sz_1708_ = lean_array_size(v_es_1695_);
        v___x_1709_ = 0usize;
        v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1704_,
            v_es_1695_,
            v___f_1706_,
            v_sz_1708_,
            v___x_1709_,
            v___x_1707_,
        );
        v_fst_1711_ = crate::leanh::lean_ctor_get(v___x_1710_, 0);
        crate::leanh::lean_inc(v_fst_1711_);
        crate::leanh::lean_dec(v___x_1710_);
        if crate::leanh::lean_obj_tag(v_fst_1711_) == 0 {
            return v_numDigits_1696_;
        } else {
            let mut v_val_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_numDigits_1696_);
            v_val_1712_ = crate::leanh::lean_ctor_get(v_fst_1711_, 0);
            crate::leanh::lean_inc(v_val_1712_);
            crate::leanh::lean_dec_ref_known(v_fst_1711_, 1);
            return v_val_1712_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(
    mut v_inst_1713_: *mut crate::leanh::LeanObject,
    mut v_shift_1714_: *mut crate::leanh::LeanObject,
    mut v___f_1715_: *mut crate::leanh::LeanObject,
    mut v___f_1716_: *mut crate::leanh::LeanObject,
    mut v___x_1717_: *mut crate::leanh::LeanObject,
    mut v_numDigits_1718_: *mut crate::leanh::LeanObject,
    mut v_es_1719_: *mut crate::leanh::LeanObject,
    mut v_a_1720_: *mut crate::leanh::LeanObject,
    mut v_x_1721_: *mut crate::leanh::LeanObject,
    mut v___y_1722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: u64 = 0;
    let mut v___x_1729_: u64 = 0;
    let mut v___x_1730_: u64 = 0;
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1748_: u8 = 0;
    let mut v_unused_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1723_ = crate::leanh::lean_ctor_get(v___y_1722_, 1);
                v_isSharedCheck_1748_ = (!crate::leanh::lean_is_exclusive(v___y_1722_)) as u8;
                if v_isSharedCheck_1748_ == 0 {
                    v_unused_1749_ = crate::leanh::lean_ctor_get(v___y_1722_, 0);
                    crate::leanh::lean_dec(v_unused_1749_);
                    v___x_1725_ = v___y_1722_;
                    v_isShared_1726_ = v_isSharedCheck_1748_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1723_);
                    crate::leanh::lean_dec(v___y_1722_);
                    v___x_1725_ = crate::leanh::lean_box(0);
                    v_isShared_1726_ = v_isSharedCheck_1748_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_1713_);
                v___x_1727_ = crate::leanh::lean_apply_1(v_inst_1713_, v_a_1720_);
                v___x_1728_ = lean_uint64_of_nat(v_shift_1714_);
                v___x_1729_ = crate::leanh::lean_unbox_uint64(v___x_1727_);
                crate::leanh::lean_dec_ref(v___x_1727_);
                v___x_1730_ = lean_uint64_shift_right(v___x_1729_, v___x_1728_);
                v___x_1731_ = crate::leanh::lean_box_uint64(v___x_1730_);
                crate::leanh::lean_inc_ref(v___f_1716_);
                crate::leanh::lean_inc_ref(v___f_1715_);
                v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
                    v___f_1715_,
                    v___f_1716_,
                    v_snd_1723_,
                    v___x_1731_,
                );
                if v___x_1732_ == 0 {
                    crate::leanh::lean_dec_ref(v_es_1719_);
                    crate::leanh::lean_dec_ref(v_inst_1713_);
                    v___x_1733_ = crate::leanh::lean_box(0);
                    v___x_1734_ = crate::leanh::lean_box_uint64(v___x_1730_);
                    v___x_1735_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                        v___f_1715_,
                        v___f_1716_,
                        v_snd_1723_,
                        v___x_1734_,
                        v___x_1733_,
                    );
                    if v_isShared_1726_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1725_, 1, v___x_1735_);
                        crate::leanh::lean_ctor_set(v___x_1725_, 0, v___x_1717_);
                        v___x_1737_ = v___x_1725_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1739_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1717_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1735_);
                        v___x_1737_ = v_reuseFailAlloc_1739_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1717_);
                    crate::leanh::lean_dec_ref(v___f_1716_);
                    crate::leanh::lean_dec_ref(v___f_1715_);
                    v___x_1740_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1741_ = lean_nat_add(v_numDigits_1718_, v___x_1740_);
                    v___x_1742_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_1713_, v_es_1719_, v___x_1741_);
                    v___x_1743_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1742_);
                    if v_isShared_1726_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1725_, 0, v___x_1743_);
                        v___x_1745_ = v___x_1725_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1747_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1743_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_snd_1723_);
                        v___x_1745_ = v_reuseFailAlloc_1747_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1738_, 0, v___x_1737_);
                return v___x_1738_;
            }
            3 => {
                v___x_1746_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1746_, 0, v___x_1745_);
                return v___x_1746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(
    mut v_00_u03b1_1750_: *mut crate::leanh::LeanObject,
    mut v_inst_1751_: *mut crate::leanh::LeanObject,
    mut v_es_1752_: *mut crate::leanh::LeanObject,
    mut v_numDigits_1753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_1751_, v_es_1752_, v_numDigits_1753_);
    return v___x_1754_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(
    mut v_x_1755_: *mut crate::leanh::LeanObject,
    mut v_h__1_1756_: *mut crate::leanh::LeanObject,
    mut v_h__2_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1755_) == 0 {
        let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1756_);
        v___x_1758_ = crate::leanh::lean_box(0);
        v___x_1759_ = crate::leanh::lean_apply_1(v_h__2_1757_, v___x_1758_);
        return v___x_1759_;
    } else {
        let mut v_val_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1757_);
        v_val_1760_ = crate::leanh::lean_ctor_get(v_x_1755_, 0);
        crate::leanh::lean_inc(v_val_1760_);
        crate::leanh::lean_dec_ref_known(v_x_1755_, 1);
        v___x_1761_ = crate::leanh::lean_apply_1(v_h__1_1756_, v_val_1760_);
        return v___x_1761_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_1762_: *mut crate::leanh::LeanObject,
    mut v_motive_1763_: *mut crate::leanh::LeanObject,
    mut v_x_1764_: *mut crate::leanh::LeanObject,
    mut v_h__1_1765_: *mut crate::leanh::LeanObject,
    mut v_h__2_1766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1764_) == 0 {
        let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1765_);
        v___x_1767_ = crate::leanh::lean_box(0);
        v___x_1768_ = crate::leanh::lean_apply_1(v_h__2_1766_, v___x_1767_);
        return v___x_1768_;
    } else {
        let mut v_val_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1766_);
        v_val_1769_ = crate::leanh::lean_ctor_get(v_x_1764_, 0);
        crate::leanh::lean_inc(v_val_1769_);
        crate::leanh::lean_dec_ref_known(v_x_1764_, 1);
        v___x_1770_ = crate::leanh::lean_apply_1(v_h__1_1765_, v_val_1769_);
        return v___x_1770_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(
    mut v_inst_1771_: *mut crate::leanh::LeanObject,
    mut v_es_1772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1773_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1774_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_1771_, v_es_1772_, v___x_1773_);
    return v___x_1774_;
}
pub unsafe fn l_Lean_Meta_Grind_getNumDigitsForAnchors(
    mut v_00_u03b1_1775_: *mut crate::leanh::LeanObject,
    mut v_inst_1776_: *mut crate::leanh::LeanObject,
    mut v_es_1777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1778_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_1776_, v_es_1777_);
    return v___x_1778_;
}
pub unsafe fn l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(
    mut v_e_1779_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_anchor_1780_: u64 = 0;
    v_anchor_1780_ = crate::leanh::lean_ctor_get_uint64(
        v_e_1779_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    return v_anchor_1780_;
}
pub unsafe fn l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(
    mut v_e_1781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1782_: u64 = 0;
    let mut v_r_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_1781_);
    crate::leanh::lean_dec_ref(v_e_1781_);
    v_r_1783_ = crate::leanh::lean_box_uint64(v_res_1782_);
    return v_r_1783_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(
    mut v_numDigits_1799_: *mut crate::leanh::LeanObject,
    mut v_anchorPrefix_1800_: u64,
    mut v_a_1801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1803_ = crate::leanh::lean_ctor_get(v_a_1801_, 5);
    v___x_1804_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1;
    v___x_1805_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_1799_, v_anchorPrefix_1800_);
    v___x_1806_ = l_Lean_mkAtom(v___x_1805_);
    v___x_1807_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1808_ = lean_mk_empty_array_with_capacity(v___x_1807_);
    v___x_1809_ = lean_array_push(v___x_1808_, v___x_1806_);
    v___x_1810_ = crate::leanh::lean_box(2);
    v___x_1811_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1811_, 0, v___x_1810_);
    crate::leanh::lean_ctor_set(v___x_1811_, 1, v___x_1804_);
    crate::leanh::lean_ctor_set(v___x_1811_, 2, v___x_1809_);
    v___x_1812_ = 0;
    v___x_1813_ = l_Lean_SourceInfo_fromRef(v_ref_1803_, v___x_1812_);
    v___x_1814_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6;
    v___x_1815_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7;
    crate::leanh::lean_inc(v___x_1813_);
    v___x_1816_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1816_, 0, v___x_1813_);
    crate::leanh::lean_ctor_set(v___x_1816_, 1, v___x_1815_);
    v___x_1817_ = l_Lean_Syntax_node2(v___x_1813_, v___x_1814_, v___x_1816_, v___x_1811_);
    v___x_1818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1818_, 0, v___x_1817_);
    return v___x_1818_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(
    mut v_numDigits_1819_: *mut crate::leanh::LeanObject,
    mut v_anchorPrefix_1820_: *mut crate::leanh::LeanObject,
    mut v_a_1821_: *mut crate::leanh::LeanObject,
    mut v_a_1822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anchorPrefix_boxed_1823_: u64 = 0;
    let mut v_res_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anchorPrefix_boxed_1823_ = crate::leanh::lean_unbox_uint64(v_anchorPrefix_1820_);
    crate::leanh::lean_dec_ref(v_anchorPrefix_1820_);
    v_res_1824_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(
        v_numDigits_1819_,
        v_anchorPrefix_boxed_1823_,
        v_a_1821_,
    );
    crate::leanh::lean_dec_ref(v_a_1821_);
    crate::leanh::lean_dec(v_numDigits_1819_);
    return v_res_1824_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(
    mut v_numDigits_1825_: *mut crate::leanh::LeanObject,
    mut v_anchorPrefix_1826_: u64,
    mut v_a_1827_: *mut crate::leanh::LeanObject,
    mut v_a_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(
        v_numDigits_1825_,
        v_anchorPrefix_1826_,
        v_a_1827_,
    );
    return v___x_1830_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(
    mut v_numDigits_1831_: *mut crate::leanh::LeanObject,
    mut v_anchorPrefix_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anchorPrefix_boxed_1836_: u64 = 0;
    let mut v_res_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anchorPrefix_boxed_1836_ = crate::leanh::lean_unbox_uint64(v_anchorPrefix_1832_);
    crate::leanh::lean_dec_ref(v_anchorPrefix_1832_);
    v_res_1837_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(
        v_numDigits_1831_,
        v_anchorPrefix_boxed_1836_,
        v_a_1833_,
        v_a_1834_,
    );
    crate::leanh::lean_dec(v_a_1834_);
    crate::leanh::lean_dec_ref(v_a_1833_);
    crate::leanh::lean_dec(v_numDigits_1831_);
    return v_res_1837_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntax___redArg(
    mut v_numDigits_1838_: *mut crate::leanh::LeanObject,
    mut v_anchor_1839_: u64,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1842_: u64 = 0;
    let mut v___x_1843_: u64 = 0;
    let mut v___x_1844_: u64 = 0;
    let mut v___x_1845_: u64 = 0;
    let mut v___x_1846_: u64 = 0;
    let mut v_anchorPrefix_1847_: u64 = 0;
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = 64u64;
    v___x_1843_ = lean_uint64_of_nat(v_numDigits_1838_);
    v___x_1844_ = 2u64;
    v___x_1845_ = lean_uint64_shift_left(v___x_1843_, v___x_1844_);
    v___x_1846_ = lean_uint64_sub(v___x_1842_, v___x_1845_);
    v_anchorPrefix_1847_ = lean_uint64_shift_right(v_anchor_1839_, v___x_1846_);
    v___x_1848_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(
        v_numDigits_1838_,
        v_anchorPrefix_1847_,
        v_a_1840_,
    );
    return v___x_1848_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntax___redArg___boxed(
    mut v_numDigits_1849_: *mut crate::leanh::LeanObject,
    mut v_anchor_1850_: *mut crate::leanh::LeanObject,
    mut v_a_1851_: *mut crate::leanh::LeanObject,
    mut v_a_1852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anchor_boxed_1853_: u64 = 0;
    let mut v_res_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anchor_boxed_1853_ = crate::leanh::lean_unbox_uint64(v_anchor_1850_);
    crate::leanh::lean_dec_ref(v_anchor_1850_);
    v_res_1854_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(
        v_numDigits_1849_,
        v_anchor_boxed_1853_,
        v_a_1851_,
    );
    crate::leanh::lean_dec_ref(v_a_1851_);
    crate::leanh::lean_dec(v_numDigits_1849_);
    return v_res_1854_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntax(
    mut v_numDigits_1855_: *mut crate::leanh::LeanObject,
    mut v_anchor_1856_: u64,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
    mut v_a_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1860_ =
        l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_1855_, v_anchor_1856_, v_a_1857_);
    return v___x_1860_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntax___boxed(
    mut v_numDigits_1861_: *mut crate::leanh::LeanObject,
    mut v_anchor_1862_: *mut crate::leanh::LeanObject,
    mut v_a_1863_: *mut crate::leanh::LeanObject,
    mut v_a_1864_: *mut crate::leanh::LeanObject,
    mut v_a_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anchor_boxed_1866_: u64 = 0;
    let mut v_res_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anchor_boxed_1866_ = crate::leanh::lean_unbox_uint64(v_anchor_1862_);
    crate::leanh::lean_dec_ref(v_anchor_1862_);
    v_res_1867_ = l_Lean_Meta_Grind_mkAnchorSyntax(
        v_numDigits_1861_,
        v_anchor_boxed_1866_,
        v_a_1863_,
        v_a_1864_,
    );
    crate::leanh::lean_dec(v_a_1864_);
    crate::leanh::lean_dec_ref(v_a_1863_);
    crate::leanh::lean_dec(v_numDigits_1861_);
    return v_res_1867_;
}
pub unsafe fn l_Lean_Meta_Grind_SplitInfo_getAnchor(
    mut v_s_1868_: *mut crate::leanh::LeanObject,
    mut v_a_1869_: *mut crate::leanh::LeanObject,
    mut v_a_1870_: *mut crate::leanh::LeanObject,
    mut v_a_1871_: *mut crate::leanh::LeanObject,
    mut v_a_1872_: *mut crate::leanh::LeanObject,
    mut v_a_1873_: *mut crate::leanh::LeanObject,
    mut v_a_1874_: *mut crate::leanh::LeanObject,
    mut v_a_1875_: *mut crate::leanh::LeanObject,
    mut v_a_1876_: *mut crate::leanh::LeanObject,
    mut v_a_1877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ = l_Lean_Meta_Grind_SplitInfo_getExpr(v_s_1868_);
    v___x_1880_ = l_Lean_Meta_Grind_getAnchor(
        v___x_1879_,
        v_a_1869_,
        v_a_1870_,
        v_a_1871_,
        v_a_1872_,
        v_a_1873_,
        v_a_1874_,
        v_a_1875_,
        v_a_1876_,
        v_a_1877_,
    );
    return v___x_1880_;
}
pub unsafe fn l_Lean_Meta_Grind_SplitInfo_getAnchor___boxed(
    mut v_s_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
    mut v_a_1884_: *mut crate::leanh::LeanObject,
    mut v_a_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
    mut v_a_1889_: *mut crate::leanh::LeanObject,
    mut v_a_1890_: *mut crate::leanh::LeanObject,
    mut v_a_1891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1892_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(
        v_s_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_,
        v_a_1889_, v_a_1890_,
    );
    crate::leanh::lean_dec(v_a_1890_);
    crate::leanh::lean_dec_ref(v_a_1889_);
    crate::leanh::lean_dec(v_a_1888_);
    crate::leanh::lean_dec_ref(v_a_1887_);
    crate::leanh::lean_dec(v_a_1886_);
    crate::leanh::lean_dec_ref(v_a_1885_);
    crate::leanh::lean_dec(v_a_1884_);
    crate::leanh::lean_dec_ref(v_a_1883_);
    crate::leanh::lean_dec(v_a_1882_);
    crate::leanh::lean_dec_ref(v_s_1881_);
    return v_res_1892_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Anchor(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Anchor(
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
    res = initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
}
