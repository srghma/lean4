// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Anchor
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.MarkNestedSubsingletons Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_mk_array, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_dec_eq, lean_uint64_mix_hash, lean_uint64_of_nat,
    lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_sub, lean_uint64_to_usize,
    lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
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
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0: u64 =
    0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_getAnchor___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_getAnchor___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_instHashableUInt64___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__4_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__6_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__9_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__12_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__10_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instHasAnchorExprWithAnchor: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11510626477845773464 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__5_value)
            as *mut leanh::LeanObject,
        12570470872972041128 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0()
-> u64 {
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u64 = 0;
    v___x_947_ = leanh::lean_unsigned_to_nat(1723);
    v___x_948_ = lean_uint64_of_nat(v___x_947_);
    return v___x_948_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(
    mut v_n_949_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___y_951_: u8 = 0;
    let mut v___x_952_: u8 = 0;
    let mut v___x_953_: u8 = 0;
    let mut v___x_954_: u8 = 0;
    let mut v___x_955_: u64 = 0;
    let mut v_hash_956_: u64 = 0;
    let mut v___x_957_: u64 = 0;
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_inc(v_n_949_);
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
                                if leanh::lean_obj_tag(v_n_949_) == 0 {
                                    v___x_955_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0);
                                    return v___x_955_;
                                } else {
                                    v_hash_956_ = leanh::lean_ctor_get_uint64(
                                        v_n_949_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                                            as u32,
                                    );
                                    leanh::lean_dec(v_n_949_);
                                    return v_hash_956_;
                                }
                            } else {
                                leanh::lean_dec(v_n_949_);
                                v___x_957_ = 0u64;
                                return v___x_957_;
                            }
                        } else {
                            v___x_958_ = l_Lean_privateToUserName(v_n_949_);
                            if leanh::lean_obj_tag(v___x_958_) == 0 {
                                v___x_959_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___closed__0);
                                return v___x_959_;
                            } else {
                                v_hash_960_ = leanh::lean_ctor_get_uint64(
                                    v___x_958_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                                        as u32,
                                );
                                leanh::lean_dec(v___x_958_);
                                return v_hash_960_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_n_949_);
                        v___x_961_ = 0u64;
                        return v___x_961_;
                    }
                } else {
                    leanh::lean_dec(v_n_949_);
                    v___x_962_ = 0u64;
                    return v___x_962_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName___boxed(
    mut v_n_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_966_: u64 = 0;
    let mut v_r_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_966_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_n_965_);
    v_r_967_ = leanh::lean_box_uint64(v_res_966_);
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
    mut v_a_974_: *mut leanh::LeanObject,
    mut v_b_975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_976_: u64 = 0;
    let mut v_b_boxed_977_: u64 = 0;
    let mut v_res_978_: u64 = 0;
    let mut v_r_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_976_ = leanh::lean_unbox_uint64(v_a_974_);
    leanh::lean_dec_ref(v_a_974_);
    v_b_boxed_977_ = leanh::lean_unbox_uint64(v_b_975_);
    leanh::lean_dec_ref(v_b_975_);
    v_res_978_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(
        v_a_boxed_976_,
        v_b_boxed_977_,
    );
    v_r_979_ = leanh::lean_box_uint64(v_res_978_);
    return v_r_979_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(
    mut v_declName_980_: *mut leanh::LeanObject,
    mut v___y_981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: u8 = 0;
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = lean_st_ref_get(v___y_981_);
    v_env_984_ = leanh::lean_ctor_get(v___x_983_, 0);
    leanh::lean_inc_ref(v_env_984_);
    leanh::lean_dec(v___x_983_);
    v___x_985_ = lean_is_matcher(v_env_984_, v_declName_980_);
    v___x_986_ = leanh::lean_box((v___x_985_) as usize);
    v___x_987_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_987_, 0, v___x_986_);
    return v___x_987_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg___boxed(
    mut v_declName_988_: *mut leanh::LeanObject,
    mut v___y_989_: *mut leanh::LeanObject,
    mut v___y_990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_991_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(
        v_declName_988_,
        v___y_989_,
    );
    leanh::lean_dec(v___y_989_);
    return v_res_991_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3(
    mut v_declName_992_: *mut leanh::LeanObject,
    mut v___y_993_: *mut leanh::LeanObject,
    mut v___y_994_: *mut leanh::LeanObject,
    mut v___y_995_: *mut leanh::LeanObject,
    mut v___y_996_: *mut leanh::LeanObject,
    mut v___y_997_: *mut leanh::LeanObject,
    mut v___y_998_: *mut leanh::LeanObject,
    mut v___y_999_: *mut leanh::LeanObject,
    mut v___y_1000_: *mut leanh::LeanObject,
    mut v___y_1001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(
        v_declName_992_,
        v___y_1001_,
    );
    return v___x_1003_;
}
pub unsafe fn l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___boxed(
    mut v_declName_1004_: *mut leanh::LeanObject,
    mut v___y_1005_: *mut leanh::LeanObject,
    mut v___y_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
    mut v___y_1009_: *mut leanh::LeanObject,
    mut v___y_1010_: *mut leanh::LeanObject,
    mut v___y_1011_: *mut leanh::LeanObject,
    mut v___y_1012_: *mut leanh::LeanObject,
    mut v___y_1013_: *mut leanh::LeanObject,
    mut v___y_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1013_);
    leanh::lean_dec_ref(v___y_1012_);
    leanh::lean_dec(v___y_1011_);
    leanh::lean_dec_ref(v___y_1010_);
    leanh::lean_dec(v___y_1009_);
    leanh::lean_dec_ref(v___y_1008_);
    leanh::lean_dec(v___y_1007_);
    leanh::lean_dec_ref(v___y_1006_);
    leanh::lean_dec(v___y_1005_);
    return v_res_1015_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(
    mut v_x_1016_: *mut leanh::LeanObject,
    mut v_x_1017_: *mut leanh::LeanObject,
    mut v_x_1018_: *mut leanh::LeanObject,
    mut v_x_1019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1024_: u8 = 0;
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1020_ = leanh::lean_ctor_get(v_x_1016_, 0);
                v_vs_1021_ = leanh::lean_ctor_get(v_x_1016_, 1);
                v_isSharedCheck_1045_ = (!leanh::lean_is_exclusive(v_x_1016_)) as u8;
                if v_isSharedCheck_1045_ == 0 {
                    v___x_1023_ = v_x_1016_;
                    v_isShared_1024_ = v_isSharedCheck_1045_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1021_);
                    leanh::lean_inc(v_ks_1020_);
                    leanh::lean_dec(v_x_1016_);
                    v___x_1023_ = leanh::lean_box(0);
                    v_isShared_1024_ = v_isSharedCheck_1045_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1025_ = lean_array_get_size(v_ks_1020_);
                v___x_1026_ = lean_nat_dec_lt(v_x_1017_, v___x_1025_);
                if v___x_1026_ == 0 {
                    leanh::lean_dec(v_x_1017_);
                    v___x_1027_ = lean_array_push(v_ks_1020_, v_x_1018_);
                    v___x_1028_ = lean_array_push(v_vs_1021_, v_x_1019_);
                    if v_isShared_1024_ == 0 {
                        leanh::lean_ctor_set(v___x_1023_, 1, v___x_1028_);
                        leanh::lean_ctor_set(v___x_1023_, 0, v___x_1027_);
                        v___x_1030_ = v___x_1023_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1031_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1027_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___x_1028_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_ks_1020_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_vs_1021_);
                            v___x_1035_ = v_reuseFailAlloc_1039_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1040_ = lean_array_fset(v_ks_1020_, v_x_1017_, v_x_1018_);
                        v___x_1041_ = lean_array_fset(v_vs_1021_, v_x_1017_, v_x_1019_);
                        leanh::lean_dec(v_x_1017_);
                        if v_isShared_1024_ == 0 {
                            leanh::lean_ctor_set(v___x_1023_, 1, v___x_1041_);
                            leanh::lean_ctor_set(v___x_1023_, 0, v___x_1040_);
                            v___x_1043_ = v___x_1023_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1044_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1040_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1041_);
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
                v___x_1036_ = leanh::lean_unsigned_to_nat(1);
                v___x_1037_ = lean_nat_add(v_x_1017_, v___x_1036_);
                leanh::lean_dec(v_x_1017_);
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
    mut v_n_1046_: *mut leanh::LeanObject,
    mut v_k_1047_: *mut leanh::LeanObject,
    mut v_v_1048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1049_ = leanh::lean_unsigned_to_nat(0);
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
    v___x_1055_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__0);
    v___x_1056_ = lean_usize_sub(v___x_1055_, v___x_1054_);
    return v___x_1056_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1057_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1057_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(
    mut v_x_1058_: *mut leanh::LeanObject,
    mut v_x_1059_: usize,
    mut v_x_1060_: usize,
    mut v_x_1061_: *mut leanh::LeanObject,
    mut v_x_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: usize = 0;
    let mut v___x_1065_: usize = 0;
    let mut v___x_1066_: usize = 0;
    let mut v___x_1067_: usize = 0;
    let mut v_j_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: u8 = 0;
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1073_: u8 = 0;
    let mut v_v_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1087_: u8 = 0;
    let mut v___x_1088_: u8 = 0;
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1094_: u8 = 0;
    let mut v_node_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1098_: u8 = 0;
    let mut v___x_1099_: usize = 0;
    let mut v___x_1100_: usize = 0;
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1105_: u8 = 0;
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut v_unused_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1113_: u8 = 0;
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1118_: u8 = 0;
    let mut v_ks_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: usize = 0;
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: u8 = 0;
    let mut v_reuseFailAlloc_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1130_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1058_) == 0 {
                    v_es_1063_ = leanh::lean_ctor_get(v_x_1058_, 0);
                    v___x_1064_ = 5usize;
                    v___x_1065_ = 1usize;
                    v___x_1066_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1);
                    v___x_1067_ = lean_usize_land(v_x_1059_, v___x_1066_);
                    v_j_1068_ = lean_usize_to_nat(v___x_1067_);
                    v___x_1069_ = lean_array_get_size(v_es_1063_);
                    v___x_1070_ = lean_nat_dec_lt(v_j_1068_, v___x_1069_);
                    if v___x_1070_ == 0 {
                        leanh::lean_dec(v_j_1068_);
                        leanh::lean_dec(v_x_1062_);
                        leanh::lean_dec_ref(v_x_1061_);
                        return v_x_1058_;
                    } else {
                        leanh::lean_inc_ref(v_es_1063_);
                        v_isSharedCheck_1107_ = (!leanh::lean_is_exclusive(v_x_1058_)) as u8;
                        if v_isSharedCheck_1107_ == 0 {
                            v_unused_1108_ = leanh::lean_ctor_get(v_x_1058_, 0);
                            leanh::lean_dec(v_unused_1108_);
                            v___x_1072_ = v_x_1058_;
                            v_isShared_1073_ = v_isSharedCheck_1107_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1058_);
                            v___x_1072_ = leanh::lean_box(0);
                            v_isShared_1073_ = v_isSharedCheck_1107_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1109_ = leanh::lean_ctor_get(v_x_1058_, 0);
                    v_vs_1110_ = leanh::lean_ctor_get(v_x_1058_, 1);
                    v_isSharedCheck_1130_ = (!leanh::lean_is_exclusive(v_x_1058_)) as u8;
                    if v_isSharedCheck_1130_ == 0 {
                        v___x_1112_ = v_x_1058_;
                        v_isShared_1113_ = v_isSharedCheck_1130_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1110_);
                        leanh::lean_inc(v_ks_1109_);
                        leanh::lean_dec(v_x_1058_);
                        v___x_1112_ = leanh::lean_box(0);
                        v_isShared_1113_ = v_isSharedCheck_1130_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1074_ = lean_array_fget(v_es_1063_, v_j_1068_);
                v___x_1075_ = leanh::lean_box(0);
                v_xs_x27_1076_ = lean_array_fset(v_es_1063_, v_j_1068_, v___x_1075_);
                match leanh::lean_obj_tag(v_v_1074_) {
                    0 => {
                        v_key_1083_ = leanh::lean_ctor_get(v_v_1074_, 0);
                        v_val_1084_ = leanh::lean_ctor_get(v_v_1074_, 1);
                        v_isSharedCheck_1094_ = (!leanh::lean_is_exclusive(v_v_1074_)) as u8;
                        if v_isSharedCheck_1094_ == 0 {
                            v___x_1086_ = v_v_1074_;
                            v_isShared_1087_ = v_isSharedCheck_1094_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1084_);
                            leanh::lean_inc(v_key_1083_);
                            leanh::lean_dec(v_v_1074_);
                            v___x_1086_ = leanh::lean_box(0);
                            v_isShared_1087_ = v_isSharedCheck_1094_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1095_ = leanh::lean_ctor_get(v_v_1074_, 0);
                        v_isSharedCheck_1105_ = (!leanh::lean_is_exclusive(v_v_1074_)) as u8;
                        if v_isSharedCheck_1105_ == 0 {
                            v___x_1097_ = v_v_1074_;
                            v_isShared_1098_ = v_isSharedCheck_1105_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1095_);
                            leanh::lean_dec(v_v_1074_);
                            v___x_1097_ = leanh::lean_box(0);
                            v_isShared_1098_ = v_isSharedCheck_1105_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1106_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1106_, 0, v_x_1061_);
                        leanh::lean_ctor_set(v___x_1106_, 1, v_x_1062_);
                        v___y_1078_ = v___x_1106_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1079_ = lean_array_fset(v_xs_x27_1076_, v_j_1068_, v___y_1078_);
                leanh::lean_dec(v_j_1068_);
                if v_isShared_1073_ == 0 {
                    leanh::lean_ctor_set(v___x_1072_, 0, v___x_1079_);
                    v___x_1081_ = v___x_1072_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1082_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
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
                    leanh::lean_del_object(v___x_1086_);
                    v___x_1089_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1083_,
                        v_val_1084_,
                        v_x_1061_,
                        v_x_1062_,
                    );
                    v___x_1090_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1090_, 0, v___x_1089_);
                    v___y_1078_ = v___x_1090_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1084_);
                    leanh::lean_dec(v_key_1083_);
                    if v_isShared_1087_ == 0 {
                        leanh::lean_ctor_set(v___x_1086_, 1, v_x_1062_);
                        leanh::lean_ctor_set(v___x_1086_, 0, v_x_1061_);
                        v___x_1092_ = v___x_1086_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1093_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_x_1061_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_x_1062_);
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
                    leanh::lean_ctor_set(v___x_1097_, 0, v___x_1101_);
                    v___x_1103_ = v___x_1097_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1104_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
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
                    v_reuseFailAlloc_1129_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_ks_1109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_vs_1110_);
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
                    v___x_1127_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1128_ = lean_nat_dec_lt(v___x_1126_, v___x_1127_);
                    leanh::lean_dec(v___x_1126_);
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
                    v_ks_1119_ = leanh::lean_ctor_get(v_newNode_1116_, 0);
                    leanh::lean_inc_ref(v_ks_1119_);
                    v_vs_1120_ = leanh::lean_ctor_get(v_newNode_1116_, 1);
                    leanh::lean_inc_ref(v_vs_1120_);
                    leanh::lean_dec_ref(v_newNode_1116_);
                    v___x_1121_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1122_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__2);
                    v___x_1123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_x_1060_, v_ks_1119_, v_vs_1120_, v___x_1121_, v___x_1122_);
                    leanh::lean_dec_ref(v_vs_1120_);
                    leanh::lean_dec_ref(v_ks_1119_);
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
    mut v_keys_1132_: *mut leanh::LeanObject,
    mut v_vals_1133_: *mut leanh::LeanObject,
    mut v_i_1134_: *mut leanh::LeanObject,
    mut v_entries_1135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    let mut v_k_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: u64 = 0;
    let mut v_h_1141_: usize = 0;
    let mut v___x_1142_: usize = 0;
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: usize = 0;
    let mut v___x_1145_: usize = 0;
    let mut v___x_1146_: usize = 0;
    let mut v_h_1147_: usize = 0;
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1136_ = lean_array_get_size(v_keys_1132_);
                v___x_1137_ = lean_nat_dec_lt(v_i_1134_, v___x_1136_);
                if v___x_1137_ == 0 {
                    leanh::lean_dec(v_i_1134_);
                    return v_entries_1135_;
                } else {
                    v_k_1138_ = lean_array_fget_borrowed(v_keys_1132_, v_i_1134_);
                    v_v_1139_ = lean_array_fget_borrowed(v_vals_1133_, v_i_1134_);
                    v___x_1140_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1138_);
                    v_h_1141_ = lean_uint64_to_usize(v___x_1140_);
                    v___x_1142_ = 5usize;
                    v___x_1143_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1144_ = 1usize;
                    v___x_1145_ = lean_usize_sub(v_depth_1131_, v___x_1144_);
                    v___x_1146_ = lean_usize_mul(v___x_1142_, v___x_1145_);
                    v_h_1147_ = lean_usize_shift_right(v_h_1141_, v___x_1146_);
                    v___x_1148_ = lean_nat_add(v_i_1134_, v___x_1143_);
                    leanh::lean_dec(v_i_1134_);
                    leanh::lean_inc(v_v_1139_);
                    leanh::lean_inc(v_k_1138_);
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
    mut v_depth_1151_: *mut leanh::LeanObject,
    mut v_keys_1152_: *mut leanh::LeanObject,
    mut v_vals_1153_: *mut leanh::LeanObject,
    mut v_i_1154_: *mut leanh::LeanObject,
    mut v_entries_1155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1156_: usize = 0;
    let mut v_res_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1156_ = leanh::lean_unbox_usize(v_depth_1151_);
    leanh::lean_dec(v_depth_1151_);
    v_res_1157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_boxed_1156_, v_keys_1152_, v_vals_1153_, v_i_1154_, v_entries_1155_);
    leanh::lean_dec_ref(v_vals_1153_);
    leanh::lean_dec_ref(v_keys_1152_);
    return v_res_1157_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___boxed(
    mut v_x_1158_: *mut leanh::LeanObject,
    mut v_x_1159_: *mut leanh::LeanObject,
    mut v_x_1160_: *mut leanh::LeanObject,
    mut v_x_1161_: *mut leanh::LeanObject,
    mut v_x_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_32485__boxed_1163_: usize = 0;
    let mut v_x_32486__boxed_1164_: usize = 0;
    let mut v_res_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_32485__boxed_1163_ = leanh::lean_unbox_usize(v_x_1159_);
    leanh::lean_dec(v_x_1159_);
    v_x_32486__boxed_1164_ = leanh::lean_unbox_usize(v_x_1160_);
    leanh::lean_dec(v_x_1160_);
    v_res_1165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_1158_, v_x_32485__boxed_1163_, v_x_32486__boxed_1164_, v_x_1161_, v_x_1162_);
    return v_res_1165_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(
    mut v_x_1166_: *mut leanh::LeanObject,
    mut v_x_1167_: *mut leanh::LeanObject,
    mut v_x_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1169_: u64 = 0;
    let mut v___x_1170_: usize = 0;
    let mut v___x_1171_: usize = 0;
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1167_);
    v___x_1170_ = lean_uint64_to_usize(v___x_1169_);
    v___x_1171_ = 1usize;
    v___x_1172_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_1166_, v___x_1170_, v___x_1171_, v_x_1167_, v_x_1168_);
    return v___x_1172_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(
    mut v_keys_1173_: *mut leanh::LeanObject,
    mut v_vals_1174_: *mut leanh::LeanObject,
    mut v_i_1175_: *mut leanh::LeanObject,
    mut v_k_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: u8 = 0;
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: u8 = 0;
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1177_ = lean_array_get_size(v_keys_1173_);
                v___x_1178_ = lean_nat_dec_lt(v_i_1175_, v___x_1177_);
                if v___x_1178_ == 0 {
                    leanh::lean_dec(v_i_1175_);
                    v___x_1179_ = leanh::lean_box(0);
                    return v___x_1179_;
                } else {
                    v_k_x27_1180_ = lean_array_fget_borrowed(v_keys_1173_, v_i_1175_);
                    v___x_1181_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1176_,
                            v_k_x27_1180_,
                        );
                    if v___x_1181_ == 0 {
                        v___x_1182_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1183_ = lean_nat_add(v_i_1175_, v___x_1182_);
                        leanh::lean_dec(v_i_1175_);
                        v_i_1175_ = v___x_1183_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1185_ = lean_array_fget_borrowed(v_vals_1174_, v_i_1175_);
                        leanh::lean_dec(v_i_1175_);
                        leanh::lean_inc(v___x_1185_);
                        v___x_1186_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1186_, 0, v___x_1185_);
                        return v___x_1186_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg___boxed(
    mut v_keys_1187_: *mut leanh::LeanObject,
    mut v_vals_1188_: *mut leanh::LeanObject,
    mut v_i_1189_: *mut leanh::LeanObject,
    mut v_k_1190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1191_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_1187_, v_vals_1188_, v_i_1189_, v_k_1190_);
    leanh::lean_dec_ref(v_k_1190_);
    leanh::lean_dec_ref(v_vals_1188_);
    leanh::lean_dec_ref(v_keys_1187_);
    return v_res_1191_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(
    mut v_x_1192_: *mut leanh::LeanObject,
    mut v_x_1193_: usize,
    mut v_x_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: usize = 0;
    let mut v___x_1199_: usize = 0;
    let mut v_j_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: usize = 0;
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1192_) == 0 {
                    v_es_1195_ = leanh::lean_ctor_get(v_x_1192_, 0);
                    v___x_1196_ = leanh::lean_box(2);
                    v___x_1197_ = 5usize;
                    v___x_1198_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg___closed__1);
                    v___x_1199_ = lean_usize_land(v_x_1193_, v___x_1198_);
                    v_j_1200_ = lean_usize_to_nat(v___x_1199_);
                    v___x_1201_ = lean_array_get_borrowed(v___x_1196_, v_es_1195_, v_j_1200_);
                    leanh::lean_dec(v_j_1200_);
                    match leanh::lean_obj_tag(v___x_1201_) {
                        0 => {
                            v_key_1202_ = leanh::lean_ctor_get(v___x_1201_, 0);
                            v_val_1203_ = leanh::lean_ctor_get(v___x_1201_, 1);
                            v___x_1204_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1194_, v_key_1202_);
                            if v___x_1204_ == 0 {
                                v___x_1205_ = leanh::lean_box(0);
                                return v___x_1205_;
                            } else {
                                leanh::lean_inc(v_val_1203_);
                                v___x_1206_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1206_, 0, v_val_1203_);
                                return v___x_1206_;
                            }
                        }
                        1 => {
                            v_node_1207_ = leanh::lean_ctor_get(v___x_1201_, 0);
                            v___x_1208_ = lean_usize_shift_right(v_x_1193_, v___x_1197_);
                            v_x_1192_ = v_node_1207_;
                            v_x_1193_ = v___x_1208_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1210_ = leanh::lean_box(0);
                            return v___x_1210_;
                        }
                    }
                } else {
                    v_ks_1211_ = leanh::lean_ctor_get(v_x_1192_, 0);
                    v_vs_1212_ = leanh::lean_ctor_get(v_x_1192_, 1);
                    v___x_1213_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1214_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_ks_1211_, v_vs_1212_, v___x_1213_, v_x_1194_);
                    return v___x_1214_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg___boxed(
    mut v_x_1215_: *mut leanh::LeanObject,
    mut v_x_1216_: *mut leanh::LeanObject,
    mut v_x_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_32685__boxed_1218_: usize = 0;
    let mut v_res_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_32685__boxed_1218_ = leanh::lean_unbox_usize(v_x_1216_);
    leanh::lean_dec(v_x_1216_);
    v_res_1219_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_1215_, v_x_32685__boxed_1218_, v_x_1217_);
    leanh::lean_dec_ref(v_x_1217_);
    leanh::lean_dec_ref(v_x_1215_);
    return v_res_1219_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(
    mut v_x_1220_: *mut leanh::LeanObject,
    mut v_x_1221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1222_: u64 = 0;
    let mut v___x_1223_: usize = 0;
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1222_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1221_);
    v___x_1223_ = lean_uint64_to_usize(v___x_1222_);
    v___x_1224_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_1220_, v___x_1223_, v_x_1221_);
    return v___x_1224_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg___boxed(
    mut v_x_1225_: *mut leanh::LeanObject,
    mut v_x_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1227_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(
            v_x_1225_, v_x_1226_,
        );
    leanh::lean_dec_ref(v_x_1226_);
    leanh::lean_dec_ref(v_x_1225_);
    return v_res_1227_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_getAnchor___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1228_ = leanh::lean_box(0);
    v_dummy_1229_ = l_Lean_Expr_sort___override(v___x_1228_);
    return v_dummy_1229_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4(
    mut v_x_1232_: *mut leanh::LeanObject,
    mut v_x_1233_: *mut leanh::LeanObject,
    mut v_x_1234_: *mut leanh::LeanObject,
    mut v___y_1235_: *mut leanh::LeanObject,
    mut v___y_1236_: *mut leanh::LeanObject,
    mut v___y_1237_: *mut leanh::LeanObject,
    mut v___y_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: *mut leanh::LeanObject,
    mut v___y_1240_: *mut leanh::LeanObject,
    mut v___y_1241_: *mut leanh::LeanObject,
    mut v___y_1242_: *mut leanh::LeanObject,
    mut v___y_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pinfos_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: u64 = 0;
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1263_: u8 = 0;
    let mut v___x_1264_: u8 = 0;
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u8 = 0;
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1232_) == 5 {
                    v_fn_1282_ = leanh::lean_ctor_get(v_x_1232_, 0);
                    leanh::lean_inc_ref(v_fn_1282_);
                    v_arg_1283_ = leanh::lean_ctor_get(v_x_1232_, 1);
                    leanh::lean_inc_ref(v_arg_1283_);
                    leanh::lean_dec_ref_known(v_x_1232_, 2);
                    v___x_1284_ = lean_array_set(v_x_1233_, v_x_1234_, v_arg_1283_);
                    v___x_1285_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1286_ = lean_nat_sub(v_x_1234_, v___x_1285_);
                    leanh::lean_dec(v_x_1234_);
                    v_x_1232_ = v_fn_1282_;
                    v_x_1233_ = v___x_1284_;
                    v_x_1234_ = v___x_1286_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_1234_);
                    v___x_1288_ = l_Lean_Meta_Grind_isMarkedSubsingletonConst(v_x_1232_);
                    if v___x_1288_ == 0 {
                        v___y_1263_ = v___x_1288_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1289_ = lean_array_get_size(v_x_1233_);
                        v___x_1290_ = leanh::lean_unsigned_to_nat(2);
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
                if leanh::lean_obj_tag(v___x_1256_) == 0 {
                    v_a_1257_ = leanh::lean_ctor_get(v___x_1256_, 0);
                    leanh::lean_inc(v_a_1257_);
                    leanh::lean_dec_ref_known(v___x_1256_, 1);
                    v___x_1258_ = lean_array_get_size(v_x_1233_);
                    v___x_1259_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1260_ = leanh::lean_unbox_uint64(v_a_1257_);
                    leanh::lean_dec(v_a_1257_);
                    v___x_1261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0___redArg(v___x_1258_, v_x_1233_, v_pinfos_1246_, v___x_1259_, v___x_1260_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
                    leanh::lean_dec_ref(v_pinfos_1246_);
                    leanh::lean_dec_ref(v_x_1233_);
                    return v___x_1261_;
                } else {
                    leanh::lean_dec_ref(v_pinfos_1246_);
                    leanh::lean_dec_ref(v_x_1233_);
                    return v___x_1256_;
                }
            }
            2 => {
                if v___y_1263_ == 0 {
                    v___x_1264_ = l_Lean_Expr_hasLooseBVars(v_x_1232_);
                    if v___x_1264_ == 0 {
                        v___x_1265_ = leanh::lean_box(0);
                        leanh::lean_inc_ref(v_x_1232_);
                        v___x_1266_ = l_Lean_Meta_getFunInfo(
                            v_x_1232_,
                            v___x_1265_,
                            v___y_1240_,
                            v___y_1241_,
                            v___y_1242_,
                            v___y_1243_,
                        );
                        if leanh::lean_obj_tag(v___x_1266_) == 0 {
                            v_a_1267_ = leanh::lean_ctor_get(v___x_1266_, 0);
                            leanh::lean_inc(v_a_1267_);
                            leanh::lean_dec_ref_known(v___x_1266_, 1);
                            v_paramInfo_1268_ = leanh::lean_ctor_get(v_a_1267_, 0);
                            leanh::lean_inc_ref(v_paramInfo_1268_);
                            leanh::lean_dec(v_a_1267_);
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
                            leanh::lean_dec_ref(v_x_1233_);
                            leanh::lean_dec_ref(v_x_1232_);
                            v_a_1269_ = leanh::lean_ctor_get(v___x_1266_, 0);
                            v_isSharedCheck_1276_ =
                                (!leanh::lean_is_exclusive(v___x_1266_)) as u8;
                            if v_isSharedCheck_1276_ == 0 {
                                v___x_1271_ = v___x_1266_;
                                v_isShared_1272_ = v_isSharedCheck_1276_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1269_);
                                leanh::lean_dec(v___x_1266_);
                                v___x_1271_ = leanh::lean_box(0);
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
                    leanh::lean_dec_ref(v_x_1232_);
                    v___x_1278_ = l_Lean_instInhabitedExpr;
                    v___x_1279_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1280_ = lean_array_get(v___x_1278_, v_x_1233_, v___x_1279_);
                    leanh::lean_dec_ref(v_x_1233_);
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
                    v_reuseFailAlloc_1275_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
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
    mut v_e_1292_: *mut leanh::LeanObject,
    mut v_a_1293_: *mut leanh::LeanObject,
    mut v_a_1294_: *mut leanh::LeanObject,
    mut v_a_1295_: *mut leanh::LeanObject,
    mut v_a_1296_: *mut leanh::LeanObject,
    mut v_a_1297_: *mut leanh::LeanObject,
    mut v_a_1298_: *mut leanh::LeanObject,
    mut v_a_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
    mut v_a_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1304_: u64 = 0;
    let mut v___y_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrThms_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastTag_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_counters_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitDiags_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematchDiags_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulEqCmpMap_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reflCmpMap_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instanceMap_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut v_n_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: u64 = 0;
    let mut v___x_1347_: u64 = 0;
    let mut v___x_1348_: u64 = 0;
    let mut v___x_1349_: u64 = 0;
    let mut v___x_1350_: u64 = 0;
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1357_: u8 = 0;
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1361_: u8 = 0;
    let mut v_deBruijnIndex_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: u64 = 0;
    let mut v_fvarId_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u64 = 0;
    let mut v_a_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1376_: u8 = 0;
    let mut v_declName_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: u64 = 0;
    let mut v___x_1382_: u64 = 0;
    let mut v_a_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut v_dummy_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: u64 = 0;
    let mut v_binderName_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u64 = 0;
    let mut v___x_1416_: u64 = 0;
    let mut v___x_1417_: u64 = 0;
    let mut v___x_1418_: u64 = 0;
    let mut v___x_1419_: u64 = 0;
    let mut v___x_1420_: u64 = 0;
    let mut v___x_1421_: u64 = 0;
    let mut v_a_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: u64 = 0;
    let mut v_expr_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: u64 = 0;
    let mut v_idx_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u64 = 0;
    let mut v___x_1433_: u64 = 0;
    let mut v___x_1434_: u64 = 0;
    let mut v___x_1435_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1351_ = lean_st_ref_get(v_a_1295_);
                v_anchors_1352_ = leanh::lean_ctor_get(v___x_1351_, 8);
                leanh::lean_inc_ref(v_anchors_1352_);
                leanh::lean_dec(v___x_1351_);
                v___x_1353_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(v_anchors_1352_, v_e_1292_);
                leanh::lean_dec_ref(v_anchors_1352_);
                if leanh::lean_obj_tag(v___x_1353_) == 1 {
                    leanh::lean_dec_ref(v_e_1292_);
                    v_val_1354_ = leanh::lean_ctor_get(v___x_1353_, 0);
                    v_isSharedCheck_1361_ = (!leanh::lean_is_exclusive(v___x_1353_)) as u8;
                    if v_isSharedCheck_1361_ == 0 {
                        v___x_1356_ = v___x_1353_;
                        v_isShared_1357_ = v_isSharedCheck_1361_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1354_);
                        leanh::lean_dec(v___x_1353_);
                        v___x_1356_ = leanh::lean_box(0);
                        v_isShared_1357_ = v_isSharedCheck_1361_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1353_);
                    match leanh::lean_obj_tag(v_e_1292_) {
                        0 => {
                            v_deBruijnIndex_1362_ = leanh::lean_ctor_get(v_e_1292_, 0);
                            v___x_1363_ = lean_uint64_of_nat(v_deBruijnIndex_1362_);
                            v_a_1304_ = v___x_1363_;
                            v___y_1305_ = v_a_1295_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_fvarId_1364_ = leanh::lean_ctor_get(v_e_1292_, 0);
                            leanh::lean_inc(v_fvarId_1364_);
                            v___x_1365_ = l_Lean_FVarId_getDecl___redArg(
                                v_fvarId_1364_,
                                v_a_1298_,
                                v_a_1300_,
                                v_a_1301_,
                            );
                            if leanh::lean_obj_tag(v___x_1365_) == 0 {
                                v_a_1366_ = leanh::lean_ctor_get(v___x_1365_, 0);
                                leanh::lean_inc(v_a_1366_);
                                leanh::lean_dec_ref_known(v___x_1365_, 1);
                                v___x_1367_ = l_Lean_LocalDecl_userName(v_a_1366_);
                                leanh::lean_dec(v_a_1366_);
                                v___x_1368_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v___x_1367_);
                                v_a_1304_ = v___x_1368_;
                                v___y_1305_ = v_a_1295_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_e_1292_, 1);
                                v_a_1369_ = leanh::lean_ctor_get(v___x_1365_, 0);
                                v_isSharedCheck_1376_ =
                                    (!leanh::lean_is_exclusive(v___x_1365_)) as u8;
                                if v_isSharedCheck_1376_ == 0 {
                                    v___x_1371_ = v___x_1365_;
                                    v_isShared_1372_ = v_isSharedCheck_1376_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1369_);
                                    leanh::lean_dec(v___x_1365_);
                                    v___x_1371_ = leanh::lean_box(0);
                                    v_isShared_1372_ = v_isSharedCheck_1376_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                        4 => {
                            v_declName_1377_ = leanh::lean_ctor_get(v_e_1292_, 0);
                            leanh::lean_inc(v_declName_1377_);
                            v___x_1378_ = l_Lean_Meta_isMatcher___at___00Lean_Meta_Grind_getAnchor_spec__3___redArg(v_declName_1377_, v_a_1301_);
                            if leanh::lean_obj_tag(v___x_1378_) == 0 {
                                v_a_1379_ = leanh::lean_ctor_get(v___x_1378_, 0);
                                leanh::lean_inc(v_a_1379_);
                                leanh::lean_dec_ref_known(v___x_1378_, 1);
                                v___x_1380_ = (leanh::lean_unbox(v_a_1379_) as u8);
                                leanh::lean_dec(v_a_1379_);
                                if v___x_1380_ == 0 {
                                    leanh::lean_inc(v_declName_1377_);
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
                                leanh::lean_dec_ref_known(v_e_1292_, 2);
                                v_a_1383_ = leanh::lean_ctor_get(v___x_1378_, 0);
                                v_isSharedCheck_1390_ =
                                    (!leanh::lean_is_exclusive(v___x_1378_)) as u8;
                                if v_isSharedCheck_1390_ == 0 {
                                    v___x_1385_ = v___x_1378_;
                                    v_isShared_1386_ = v_isSharedCheck_1390_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1383_);
                                    leanh::lean_dec(v___x_1378_);
                                    v___x_1385_ = leanh::lean_box(0);
                                    v_isShared_1386_ = v_isSharedCheck_1390_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                        5 => {
                            v_dummy_1391_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Grind_getAnchor___closed__0),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_getAnchor___closed__0_once
                                ),
                                _init_l_Lean_Meta_Grind_getAnchor___closed__0,
                            );
                            v_nargs_1392_ = l_Lean_Expr_getAppNumArgs(v_e_1292_);
                            leanh::lean_inc(v_nargs_1392_);
                            v___x_1393_ = lean_mk_array(v_nargs_1392_, v_dummy_1391_);
                            v___x_1394_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1395_ = lean_nat_sub(v_nargs_1392_, v___x_1394_);
                            leanh::lean_dec(v_nargs_1392_);
                            leanh::lean_inc_ref(v_e_1292_);
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
                            if leanh::lean_obj_tag(v___x_1396_) == 0 {
                                v_a_1397_ = leanh::lean_ctor_get(v___x_1396_, 0);
                                leanh::lean_inc(v_a_1397_);
                                leanh::lean_dec_ref_known(v___x_1396_, 1);
                                v___x_1398_ = leanh::lean_unbox_uint64(v_a_1397_);
                                leanh::lean_dec(v_a_1397_);
                                v_a_1304_ = v___x_1398_;
                                v___y_1305_ = v_a_1295_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_e_1292_, 2);
                                return v___x_1396_;
                            }
                        }
                        6 => {
                            v_binderName_1399_ = leanh::lean_ctor_get(v_e_1292_, 0);
                            v_binderType_1400_ = leanh::lean_ctor_get(v_e_1292_, 1);
                            v_body_1401_ = leanh::lean_ctor_get(v_e_1292_, 2);
                            leanh::lean_inc_ref(v_body_1401_);
                            leanh::lean_inc_ref(v_binderType_1400_);
                            leanh::lean_inc(v_binderName_1399_);
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
                            v_binderName_1402_ = leanh::lean_ctor_get(v_e_1292_, 0);
                            v_binderType_1403_ = leanh::lean_ctor_get(v_e_1292_, 1);
                            v_body_1404_ = leanh::lean_ctor_get(v_e_1292_, 2);
                            leanh::lean_inc_ref(v_body_1404_);
                            leanh::lean_inc_ref(v_binderType_1403_);
                            leanh::lean_inc(v_binderName_1402_);
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
                            v_declName_1405_ = leanh::lean_ctor_get(v_e_1292_, 0);
                            v_type_1406_ = leanh::lean_ctor_get(v_e_1292_, 1);
                            v_value_1407_ = leanh::lean_ctor_get(v_e_1292_, 2);
                            v_body_1408_ = leanh::lean_ctor_get(v_e_1292_, 3);
                            leanh::lean_inc_ref(v_value_1407_);
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
                            if leanh::lean_obj_tag(v___x_1409_) == 0 {
                                v_a_1410_ = leanh::lean_ctor_get(v___x_1409_, 0);
                                leanh::lean_inc(v_a_1410_);
                                leanh::lean_dec_ref_known(v___x_1409_, 1);
                                leanh::lean_inc_ref(v_type_1406_);
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
                                if leanh::lean_obj_tag(v___x_1411_) == 0 {
                                    v_a_1412_ = leanh::lean_ctor_get(v___x_1411_, 0);
                                    leanh::lean_inc(v_a_1412_);
                                    leanh::lean_dec_ref_known(v___x_1411_, 1);
                                    leanh::lean_inc_ref(v_body_1408_);
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
                                    if leanh::lean_obj_tag(v___x_1413_) == 0 {
                                        v_a_1414_ = leanh::lean_ctor_get(v___x_1413_, 0);
                                        leanh::lean_inc(v_a_1414_);
                                        leanh::lean_dec_ref_known(v___x_1413_, 1);
                                        leanh::lean_inc(v_declName_1405_);
                                        v___x_1415_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(v_declName_1405_);
                                        v___x_1416_ = leanh::lean_unbox_uint64(v_a_1412_);
                                        leanh::lean_dec(v_a_1412_);
                                        v___x_1417_ = leanh::lean_unbox_uint64(v_a_1414_);
                                        leanh::lean_dec(v_a_1414_);
                                        v___x_1418_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_1416_, v___x_1417_);
                                        v___x_1419_ = leanh::lean_unbox_uint64(v_a_1410_);
                                        leanh::lean_dec(v_a_1410_);
                                        v___x_1420_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_1419_, v___x_1418_);
                                        v___x_1421_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_1415_, v___x_1420_);
                                        v_a_1304_ = v___x_1421_;
                                        v___y_1305_ = v_a_1295_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_a_1412_);
                                        leanh::lean_dec(v_a_1410_);
                                        leanh::lean_dec_ref_known(v_e_1292_, 4);
                                        return v___x_1413_;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1410_);
                                    leanh::lean_dec_ref_known(v_e_1292_, 4);
                                    return v___x_1411_;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_e_1292_, 4);
                                return v___x_1409_;
                            }
                        }
                        9 => {
                            v_a_1422_ = leanh::lean_ctor_get(v_e_1292_, 0);
                            v___x_1423_ = l_Lean_Literal_hash(v_a_1422_);
                            v_a_1304_ = v___x_1423_;
                            v___y_1305_ = v_a_1295_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_expr_1424_ = leanh::lean_ctor_get(v_e_1292_, 1);
                            leanh::lean_inc_ref(v_expr_1424_);
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
                            if leanh::lean_obj_tag(v___x_1425_) == 0 {
                                v_a_1426_ = leanh::lean_ctor_get(v___x_1425_, 0);
                                leanh::lean_inc(v_a_1426_);
                                leanh::lean_dec_ref_known(v___x_1425_, 1);
                                v___x_1427_ = leanh::lean_unbox_uint64(v_a_1426_);
                                leanh::lean_dec(v_a_1426_);
                                v_a_1304_ = v___x_1427_;
                                v___y_1305_ = v_a_1295_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_e_1292_, 2);
                                return v___x_1425_;
                            }
                        }
                        11 => {
                            v_idx_1428_ = leanh::lean_ctor_get(v_e_1292_, 1);
                            v_struct_1429_ = leanh::lean_ctor_get(v_e_1292_, 2);
                            leanh::lean_inc_ref(v_struct_1429_);
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
                            if leanh::lean_obj_tag(v___x_1430_) == 0 {
                                v_a_1431_ = leanh::lean_ctor_get(v___x_1430_, 0);
                                leanh::lean_inc(v_a_1431_);
                                leanh::lean_dec_ref_known(v___x_1430_, 1);
                                v___x_1432_ = lean_uint64_of_nat(v_idx_1428_);
                                v___x_1433_ = leanh::lean_unbox_uint64(v_a_1431_);
                                leanh::lean_dec(v_a_1431_);
                                v___x_1434_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v___x_1432_, v___x_1433_);
                                v_a_1304_ = v___x_1434_;
                                v___y_1305_ = v_a_1295_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_e_1292_, 3);
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
                v_congrThms_1307_ = leanh::lean_ctor_get(v___x_1306_, 0);
                v_simp_1308_ = leanh::lean_ctor_get(v___x_1306_, 1);
                v_lastTag_1309_ = leanh::lean_ctor_get(v___x_1306_, 2);
                v_counters_1310_ = leanh::lean_ctor_get(v___x_1306_, 3);
                v_splitDiags_1311_ = leanh::lean_ctor_get(v___x_1306_, 4);
                v_ematchDiags_1312_ = leanh::lean_ctor_get(v___x_1306_, 5);
                v_lawfulEqCmpMap_1313_ = leanh::lean_ctor_get(v___x_1306_, 6);
                v_reflCmpMap_1314_ = leanh::lean_ctor_get(v___x_1306_, 7);
                v_anchors_1315_ = leanh::lean_ctor_get(v___x_1306_, 8);
                v_instanceMap_1316_ = leanh::lean_ctor_get(v___x_1306_, 9);
                v_isSharedCheck_1328_ = (!leanh::lean_is_exclusive(v___x_1306_)) as u8;
                if v_isSharedCheck_1328_ == 0 {
                    v___x_1318_ = v___x_1306_;
                    v_isShared_1319_ = v_isSharedCheck_1328_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_instanceMap_1316_);
                    leanh::lean_inc(v_anchors_1315_);
                    leanh::lean_inc(v_reflCmpMap_1314_);
                    leanh::lean_inc(v_lawfulEqCmpMap_1313_);
                    leanh::lean_inc(v_ematchDiags_1312_);
                    leanh::lean_inc(v_splitDiags_1311_);
                    leanh::lean_inc(v_counters_1310_);
                    leanh::lean_inc(v_lastTag_1309_);
                    leanh::lean_inc(v_simp_1308_);
                    leanh::lean_inc(v_congrThms_1307_);
                    leanh::lean_dec(v___x_1306_);
                    v___x_1318_ = leanh::lean_box(0);
                    v_isShared_1319_ = v_isSharedCheck_1328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1320_ = leanh::lean_box_uint64(v_a_1304_);
                v___x_1321_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(v_anchors_1315_, v_e_1292_, v___x_1320_);
                if v_isShared_1319_ == 0 {
                    leanh::lean_ctor_set(v___x_1318_, 8, v___x_1321_);
                    v___x_1323_ = v___x_1318_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_congrThms_1307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_simp_1308_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_lastTag_1309_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_counters_1310_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 4, v_splitDiags_1311_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 5, v_ematchDiags_1312_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 6, v_lawfulEqCmpMap_1313_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 7, v_reflCmpMap_1314_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 8, v___x_1321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 9, v_instanceMap_1316_);
                    v___x_1323_ = v_reuseFailAlloc_1327_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1324_ = lean_st_ref_set(v___y_1305_, v___x_1323_);
                v___x_1325_ = leanh::lean_box_uint64(v_a_1304_);
                v___x_1326_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1326_, 0, v___x_1325_);
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
                if leanh::lean_obj_tag(v___x_1342_) == 0 {
                    v_a_1343_ = leanh::lean_ctor_get(v___x_1342_, 0);
                    leanh::lean_inc(v_a_1343_);
                    leanh::lean_dec_ref_known(v___x_1342_, 1);
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
                    if leanh::lean_obj_tag(v___x_1344_) == 0 {
                        v_a_1345_ = leanh::lean_ctor_get(v___x_1344_, 0);
                        leanh::lean_inc(v_a_1345_);
                        leanh::lean_dec_ref_known(v___x_1344_, 1);
                        v___x_1346_ =
                            l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_hashName(
                                v_n_1330_,
                            );
                        v___x_1347_ = leanh::lean_unbox_uint64(v_a_1343_);
                        leanh::lean_dec(v_a_1343_);
                        v___x_1348_ = leanh::lean_unbox_uint64(v_a_1345_);
                        leanh::lean_dec(v_a_1345_);
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
                        leanh::lean_dec(v_a_1343_);
                        leanh::lean_dec(v_n_1330_);
                        leanh::lean_dec_ref(v_e_1292_);
                        return v___x_1344_;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_1332_);
                    leanh::lean_dec(v_n_1330_);
                    leanh::lean_dec_ref(v_e_1292_);
                    return v___x_1342_;
                }
            }
            5 => {
                if v_isShared_1357_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1356_, 0);
                    v___x_1359_ = v___x_1356_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1360_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_val_1354_);
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
                    v_reuseFailAlloc_1375_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
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
                    v_reuseFailAlloc_1389_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
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
    mut v_upperBound_1436_: *mut leanh::LeanObject,
    mut v_args_1437_: *mut leanh::LeanObject,
    mut v_pinfos_1438_: *mut leanh::LeanObject,
    mut v_a_1439_: *mut leanh::LeanObject,
    mut v_b_1440_: u64,
    mut v___y_1441_: *mut leanh::LeanObject,
    mut v___y_1442_: *mut leanh::LeanObject,
    mut v___y_1443_: *mut leanh::LeanObject,
    mut v___y_1444_: *mut leanh::LeanObject,
    mut v___y_1445_: *mut leanh::LeanObject,
    mut v___y_1446_: *mut leanh::LeanObject,
    mut v___y_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1452_: u64 = 0;
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u64 = 0;
    let mut v___x_1465_: u64 = 0;
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: u8 = 0;
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: u64 = 0;
    let mut v___x_1471_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1456_ = lean_nat_dec_lt(v_a_1439_, v_upperBound_1436_);
                if v___x_1456_ == 0 {
                    leanh::lean_dec(v_a_1439_);
                    v___x_1457_ = leanh::lean_box_uint64(v_b_1440_);
                    v___x_1458_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1458_, 0, v___x_1457_);
                    return v___x_1458_;
                } else {
                    v___x_1459_ = lean_array_fget_borrowed(v_args_1437_, v_a_1439_);
                    v___x_1460_ = lean_array_get_size(v_pinfos_1438_);
                    v___x_1461_ = lean_nat_dec_lt(v_a_1439_, v___x_1460_);
                    if v___x_1461_ == 0 {
                        leanh::lean_inc(v___x_1459_);
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
                        if leanh::lean_obj_tag(v___x_1462_) == 0 {
                            v_a_1463_ = leanh::lean_ctor_get(v___x_1462_, 0);
                            leanh::lean_inc(v_a_1463_);
                            leanh::lean_dec_ref_known(v___x_1462_, 1);
                            v___x_1464_ = leanh::lean_unbox_uint64(v_a_1463_);
                            leanh::lean_dec(v_a_1463_);
                            v___x_1465_ =
                                l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(
                                    v_b_1440_,
                                    v___x_1464_,
                                );
                            v_a_1452_ = v___x_1465_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_1439_);
                            return v___x_1462_;
                        }
                    } else {
                        v___x_1466_ = lean_array_fget_borrowed(v_pinfos_1438_, v_a_1439_);
                        v___x_1467_ = l_Lean_Meta_ParamInfo_isImplicit(v___x_1466_);
                        if v___x_1467_ == 0 {
                            leanh::lean_inc(v___x_1459_);
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
                            if leanh::lean_obj_tag(v___x_1468_) == 0 {
                                v_a_1469_ = leanh::lean_ctor_get(v___x_1468_, 0);
                                leanh::lean_inc(v_a_1469_);
                                leanh::lean_dec_ref_known(v___x_1468_, 1);
                                v___x_1470_ = leanh::lean_unbox_uint64(v_a_1469_);
                                leanh::lean_dec(v_a_1469_);
                                v___x_1471_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_mix(v_b_1440_, v___x_1470_);
                                v_a_1452_ = v___x_1471_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_1439_);
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
                v___x_1453_ = leanh::lean_unsigned_to_nat(1);
                v___x_1454_ = lean_nat_add(v_a_1439_, v___x_1453_);
                leanh::lean_dec(v_a_1439_);
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
    mut v_upperBound_1472_: *mut leanh::LeanObject,
    mut v_args_1473_: *mut leanh::LeanObject,
    mut v_pinfos_1474_: *mut leanh::LeanObject,
    mut v_a_1475_: *mut leanh::LeanObject,
    mut v_b_1476_: *mut leanh::LeanObject,
    mut v___y_1477_: *mut leanh::LeanObject,
    mut v___y_1478_: *mut leanh::LeanObject,
    mut v___y_1479_: *mut leanh::LeanObject,
    mut v___y_1480_: *mut leanh::LeanObject,
    mut v___y_1481_: *mut leanh::LeanObject,
    mut v___y_1482_: *mut leanh::LeanObject,
    mut v___y_1483_: *mut leanh::LeanObject,
    mut v___y_1484_: *mut leanh::LeanObject,
    mut v___y_1485_: *mut leanh::LeanObject,
    mut v___y_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1487_: u64 = 0;
    let mut v_res_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1487_ = leanh::lean_unbox_uint64(v_b_1476_);
    leanh::lean_dec_ref(v_b_1476_);
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
    leanh::lean_dec(v___y_1485_);
    leanh::lean_dec_ref(v___y_1484_);
    leanh::lean_dec(v___y_1483_);
    leanh::lean_dec_ref(v___y_1482_);
    leanh::lean_dec(v___y_1481_);
    leanh::lean_dec_ref(v___y_1480_);
    leanh::lean_dec(v___y_1479_);
    leanh::lean_dec_ref(v___y_1478_);
    leanh::lean_dec(v___y_1477_);
    leanh::lean_dec_ref(v_pinfos_1474_);
    leanh::lean_dec_ref(v_args_1473_);
    leanh::lean_dec(v_upperBound_1472_);
    return v_res_1488_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Grind_getAnchor_spec__4___boxed(
    mut v_x_1489_: *mut leanh::LeanObject,
    mut v_x_1490_: *mut leanh::LeanObject,
    mut v_x_1491_: *mut leanh::LeanObject,
    mut v___y_1492_: *mut leanh::LeanObject,
    mut v___y_1493_: *mut leanh::LeanObject,
    mut v___y_1494_: *mut leanh::LeanObject,
    mut v___y_1495_: *mut leanh::LeanObject,
    mut v___y_1496_: *mut leanh::LeanObject,
    mut v___y_1497_: *mut leanh::LeanObject,
    mut v___y_1498_: *mut leanh::LeanObject,
    mut v___y_1499_: *mut leanh::LeanObject,
    mut v___y_1500_: *mut leanh::LeanObject,
    mut v___y_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1500_);
    leanh::lean_dec_ref(v___y_1499_);
    leanh::lean_dec(v___y_1498_);
    leanh::lean_dec_ref(v___y_1497_);
    leanh::lean_dec(v___y_1496_);
    leanh::lean_dec_ref(v___y_1495_);
    leanh::lean_dec(v___y_1494_);
    leanh::lean_dec_ref(v___y_1493_);
    leanh::lean_dec(v___y_1492_);
    return v_res_1502_;
}
pub unsafe fn l_Lean_Meta_Grind_getAnchor___boxed(
    mut v_e_1503_: *mut leanh::LeanObject,
    mut v_a_1504_: *mut leanh::LeanObject,
    mut v_a_1505_: *mut leanh::LeanObject,
    mut v_a_1506_: *mut leanh::LeanObject,
    mut v_a_1507_: *mut leanh::LeanObject,
    mut v_a_1508_: *mut leanh::LeanObject,
    mut v_a_1509_: *mut leanh::LeanObject,
    mut v_a_1510_: *mut leanh::LeanObject,
    mut v_a_1511_: *mut leanh::LeanObject,
    mut v_a_1512_: *mut leanh::LeanObject,
    mut v_a_1513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1514_ = l_Lean_Meta_Grind_getAnchor(
        v_e_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_,
        v_a_1511_, v_a_1512_,
    );
    leanh::lean_dec(v_a_1512_);
    leanh::lean_dec_ref(v_a_1511_);
    leanh::lean_dec(v_a_1510_);
    leanh::lean_dec_ref(v_a_1509_);
    leanh::lean_dec(v_a_1508_);
    leanh::lean_dec_ref(v_a_1507_);
    leanh::lean_dec(v_a_1506_);
    leanh::lean_dec_ref(v_a_1505_);
    leanh::lean_dec(v_a_1504_);
    return v_res_1514_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_getAnchor_spec__0(
    mut v_upperBound_1515_: *mut leanh::LeanObject,
    mut v_args_1516_: *mut leanh::LeanObject,
    mut v_pinfos_1517_: *mut leanh::LeanObject,
    mut v_inst_1518_: *mut leanh::LeanObject,
    mut v_R_1519_: *mut leanh::LeanObject,
    mut v_a_1520_: *mut leanh::LeanObject,
    mut v_b_1521_: u64,
    mut v_c_1522_: *mut leanh::LeanObject,
    mut v___y_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
    mut v___y_1525_: *mut leanh::LeanObject,
    mut v___y_1526_: *mut leanh::LeanObject,
    mut v___y_1527_: *mut leanh::LeanObject,
    mut v___y_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
    mut v___y_1530_: *mut leanh::LeanObject,
    mut v___y_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_upperBound_1534_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_args_1535_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_pinfos_1536_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_1537_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_R_1538_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_a_1539_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_b_1540_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_c_1541_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_1542_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_1543_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_1544_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_1545_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_1546_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_1547_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_1548_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_1549_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_1550_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_1551_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_b_boxed_1552_: u64 = 0;
    let mut v_res_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1552_ = leanh::lean_unbox_uint64(v_b_1540_);
    leanh::lean_dec_ref(v_b_1540_);
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
    leanh::lean_dec(v___y_1550_);
    leanh::lean_dec_ref(v___y_1549_);
    leanh::lean_dec(v___y_1548_);
    leanh::lean_dec_ref(v___y_1547_);
    leanh::lean_dec(v___y_1546_);
    leanh::lean_dec_ref(v___y_1545_);
    leanh::lean_dec(v___y_1544_);
    leanh::lean_dec_ref(v___y_1543_);
    leanh::lean_dec(v___y_1542_);
    leanh::lean_dec_ref(v_pinfos_1536_);
    leanh::lean_dec_ref(v_args_1535_);
    leanh::lean_dec(v_upperBound_1534_);
    return v_res_1553_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1(
    mut v_00_u03b2_1554_: *mut leanh::LeanObject,
    mut v_x_1555_: *mut leanh::LeanObject,
    mut v_x_1556_: *mut leanh::LeanObject,
    mut v_x_1557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1___redArg(
            v_x_1555_, v_x_1556_, v_x_1557_,
        );
    return v___x_1558_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(
    mut v_00_u03b2_1559_: *mut leanh::LeanObject,
    mut v_x_1560_: *mut leanh::LeanObject,
    mut v_x_1561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1562_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___redArg(
            v_x_1560_, v_x_1561_,
        );
    return v___x_1562_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2___boxed(
    mut v_00_u03b2_1563_: *mut leanh::LeanObject,
    mut v_x_1564_: *mut leanh::LeanObject,
    mut v_x_1565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1566_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2(
        v_00_u03b2_1563_,
        v_x_1564_,
        v_x_1565_,
    );
    leanh::lean_dec_ref(v_x_1565_);
    leanh::lean_dec_ref(v_x_1564_);
    return v_res_1566_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(
    mut v_00_u03b2_1567_: *mut leanh::LeanObject,
    mut v_x_1568_: *mut leanh::LeanObject,
    mut v_x_1569_: usize,
    mut v_x_1570_: usize,
    mut v_x_1571_: *mut leanh::LeanObject,
    mut v_x_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___redArg(v_x_1568_, v_x_1569_, v_x_1570_, v_x_1571_, v_x_1572_);
    return v___x_1573_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1___boxed(
    mut v_00_u03b2_1574_: *mut leanh::LeanObject,
    mut v_x_1575_: *mut leanh::LeanObject,
    mut v_x_1576_: *mut leanh::LeanObject,
    mut v_x_1577_: *mut leanh::LeanObject,
    mut v_x_1578_: *mut leanh::LeanObject,
    mut v_x_1579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_33267__boxed_1580_: usize = 0;
    let mut v_x_33268__boxed_1581_: usize = 0;
    let mut v_res_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_33267__boxed_1580_ = leanh::lean_unbox_usize(v_x_1576_);
    leanh::lean_dec(v_x_1576_);
    v_x_33268__boxed_1581_ = leanh::lean_unbox_usize(v_x_1577_);
    leanh::lean_dec(v_x_1577_);
    v_res_1582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1(v_00_u03b2_1574_, v_x_1575_, v_x_33267__boxed_1580_, v_x_33268__boxed_1581_, v_x_1578_, v_x_1579_);
    return v_res_1582_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(
    mut v_00_u03b2_1583_: *mut leanh::LeanObject,
    mut v_x_1584_: *mut leanh::LeanObject,
    mut v_x_1585_: usize,
    mut v_x_1586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___redArg(v_x_1584_, v_x_1585_, v_x_1586_);
    return v___x_1587_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3___boxed(
    mut v_00_u03b2_1588_: *mut leanh::LeanObject,
    mut v_x_1589_: *mut leanh::LeanObject,
    mut v_x_1590_: *mut leanh::LeanObject,
    mut v_x_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_33284__boxed_1592_: usize = 0;
    let mut v_res_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_33284__boxed_1592_ = leanh::lean_unbox_usize(v_x_1590_);
    leanh::lean_dec(v_x_1590_);
    v_res_1593_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3(v_00_u03b2_1588_, v_x_1589_, v_x_33284__boxed_1592_, v_x_1591_);
    leanh::lean_dec_ref(v_x_1591_);
    leanh::lean_dec_ref(v_x_1589_);
    return v_res_1593_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3(
    mut v_00_u03b2_1594_: *mut leanh::LeanObject,
    mut v_n_1595_: *mut leanh::LeanObject,
    mut v_k_1596_: *mut leanh::LeanObject,
    mut v_v_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3___redArg(v_n_1595_, v_k_1596_, v_v_1597_);
    return v___x_1598_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(
    mut v_00_u03b2_1599_: *mut leanh::LeanObject,
    mut v_depth_1600_: usize,
    mut v_keys_1601_: *mut leanh::LeanObject,
    mut v_vals_1602_: *mut leanh::LeanObject,
    mut v_heq_1603_: *mut leanh::LeanObject,
    mut v_i_1604_: *mut leanh::LeanObject,
    mut v_entries_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___redArg(v_depth_1600_, v_keys_1601_, v_vals_1602_, v_i_1604_, v_entries_1605_);
    return v___x_1606_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4___boxed(
    mut v_00_u03b2_1607_: *mut leanh::LeanObject,
    mut v_depth_1608_: *mut leanh::LeanObject,
    mut v_keys_1609_: *mut leanh::LeanObject,
    mut v_vals_1610_: *mut leanh::LeanObject,
    mut v_heq_1611_: *mut leanh::LeanObject,
    mut v_i_1612_: *mut leanh::LeanObject,
    mut v_entries_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1614_: usize = 0;
    let mut v_res_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1614_ = leanh::lean_unbox_usize(v_depth_1608_);
    leanh::lean_dec(v_depth_1608_);
    v_res_1615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__4(v_00_u03b2_1607_, v_depth_boxed_1614_, v_keys_1609_, v_vals_1610_, v_heq_1611_, v_i_1612_, v_entries_1613_);
    leanh::lean_dec_ref(v_vals_1610_);
    leanh::lean_dec_ref(v_keys_1609_);
    return v_res_1615_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(
    mut v_00_u03b2_1616_: *mut leanh::LeanObject,
    mut v_keys_1617_: *mut leanh::LeanObject,
    mut v_vals_1618_: *mut leanh::LeanObject,
    mut v_heq_1619_: *mut leanh::LeanObject,
    mut v_i_1620_: *mut leanh::LeanObject,
    mut v_k_1621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___redArg(v_keys_1617_, v_vals_1618_, v_i_1620_, v_k_1621_);
    return v___x_1622_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7___boxed(
    mut v_00_u03b2_1623_: *mut leanh::LeanObject,
    mut v_keys_1624_: *mut leanh::LeanObject,
    mut v_vals_1625_: *mut leanh::LeanObject,
    mut v_heq_1626_: *mut leanh::LeanObject,
    mut v_i_1627_: *mut leanh::LeanObject,
    mut v_k_1628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1629_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getAnchor_spec__2_spec__3_spec__7(v_00_u03b2_1623_, v_keys_1624_, v_vals_1625_, v_heq_1626_, v_i_1627_, v_k_1628_);
    leanh::lean_dec_ref(v_k_1628_);
    leanh::lean_dec_ref(v_vals_1625_);
    leanh::lean_dec_ref(v_keys_1624_);
    return v_res_1629_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6(
    mut v_00_u03b2_1630_: *mut leanh::LeanObject,
    mut v_x_1631_: *mut leanh::LeanObject,
    mut v_x_1632_: *mut leanh::LeanObject,
    mut v_x_1633_: *mut leanh::LeanObject,
    mut v_x_1634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getAnchor_spec__1_spec__1_spec__3_spec__6___redArg(v_x_1631_, v_x_1632_, v_x_1633_, v_x_1634_);
    return v___x_1635_;
}
pub unsafe fn l_Lean_Meta_Grind_AnchorRef_matches(
    mut v_anchorRef_1636_: *mut leanh::LeanObject,
    mut v_anchor_1637_: u64,
) -> u8 {
    let mut v_numDigits_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchorPrefix_1639_: u64 = 0;
    let mut v___x_1640_: u64 = 0;
    let mut v___x_1641_: u64 = 0;
    let mut v___x_1642_: u64 = 0;
    let mut v___x_1643_: u64 = 0;
    let mut v_shift_1644_: u64 = 0;
    let mut v___x_1645_: u64 = 0;
    let mut v___x_1646_: u8 = 0;
    v_numDigits_1638_ = leanh::lean_ctor_get(v_anchorRef_1636_, 0);
    v_anchorPrefix_1639_ = leanh::lean_ctor_get_uint64(
        v_anchorRef_1636_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_anchorRef_1647_: *mut leanh::LeanObject,
    mut v_anchor_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_anchor_boxed_1649_: u64 = 0;
    let mut v_res_1650_: u8 = 0;
    let mut v_r_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_anchor_boxed_1649_ = leanh::lean_unbox_uint64(v_anchor_1648_);
    leanh::lean_dec_ref(v_anchor_1648_);
    v_res_1650_ = l_Lean_Meta_Grind_AnchorRef_matches(v_anchorRef_1647_, v_anchor_boxed_1649_);
    leanh::lean_dec_ref(v_anchorRef_1647_);
    v_r_1651_ = leanh::lean_box((v_res_1650_) as usize);
    return v_r_1651_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = leanh::lean_alloc_closure(
        l_instDecidableEqUInt64___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_1653_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1653_, 0, v___x_1652_);
    return v___f_1653_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed(
    mut v_inst_1674_: *mut leanh::LeanObject,
    mut v_shift_1675_: *mut leanh::LeanObject,
    mut v___f_1676_: *mut leanh::LeanObject,
    mut v___f_1677_: *mut leanh::LeanObject,
    mut v___x_1678_: *mut leanh::LeanObject,
    mut v_numDigits_1679_: *mut leanh::LeanObject,
    mut v_es_1680_: *mut leanh::LeanObject,
    mut v_a_1681_: *mut leanh::LeanObject,
    mut v_x_1682_: *mut leanh::LeanObject,
    mut v___y_1683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1684_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(v_inst_1674_, v_shift_1675_, v___f_1676_, v___f_1677_, v___x_1678_, v_numDigits_1679_, v_es_1680_, v_a_1681_, v_x_1682_, v___y_1683_);
    leanh::lean_dec(v_numDigits_1679_);
    leanh::lean_dec(v_shift_1675_);
    return v_res_1684_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = leanh::lean_box(0);
    v___x_1686_ = leanh::lean_unsigned_to_nat(16);
    v___x_1687_ = lean_mk_array(v___x_1686_, v___x_1685_);
    return v___x_1687_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__2);
    v___x_1689_ = leanh::lean_unsigned_to_nat(0);
    v_found_1690_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v_found_1690_, 0, v___x_1689_);
    leanh::lean_ctor_set(v_found_1690_, 1, v___x_1688_);
    return v_found_1690_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v_found_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_found_1691_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__3);
    v___x_1692_ = leanh::lean_box(0);
    v___x_1693_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1693_, 0, v___x_1692_);
    leanh::lean_ctor_set(v___x_1693_, 1, v_found_1691_);
    return v___x_1693_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(
    mut v_inst_1694_: *mut leanh::LeanObject,
    mut v_es_1695_: *mut leanh::LeanObject,
    mut v_numDigits_1696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: u8 = 0;
    v___x_1697_ = leanh::lean_unsigned_to_nat(4);
    v___x_1698_ = lean_nat_mul(v___x_1697_, v_numDigits_1696_);
    v___x_1699_ = leanh::lean_unsigned_to_nat(64);
    v___x_1700_ = lean_nat_dec_lt(v___x_1698_, v___x_1699_);
    if v___x_1700_ == 0 {
        leanh::lean_dec(v___x_1698_);
        leanh::lean_dec_ref(v_es_1695_);
        leanh::lean_dec_ref(v_inst_1694_);
        return v_numDigits_1696_;
    } else {
        let mut v_shift_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1708_: usize = 0;
        let mut v___x_1709_: usize = 0;
        let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_shift_1701_ = lean_nat_sub(v___x_1699_, v___x_1698_);
        leanh::lean_dec(v___x_1698_);
        v___f_1702_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__0);
        v___f_1703_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__1;
        v___x_1704_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__13;
        v___x_1705_ = leanh::lean_box(0);
        leanh::lean_inc_ref(v_es_1695_);
        leanh::lean_inc(v_numDigits_1696_);
        v___f_1706_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 7);
        leanh::lean_closure_set(v___f_1706_, 0, v_inst_1694_);
        leanh::lean_closure_set(v___f_1706_, 1, v_shift_1701_);
        leanh::lean_closure_set(v___f_1706_, 2, v___f_1702_);
        leanh::lean_closure_set(v___f_1706_, 3, v___f_1703_);
        leanh::lean_closure_set(v___f_1706_, 4, v___x_1705_);
        leanh::lean_closure_set(v___f_1706_, 5, v_numDigits_1696_);
        leanh::lean_closure_set(v___f_1706_, 6, v_es_1695_);
        v___x_1707_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___closed__14);
        v_sz_1708_ = lean_array_size(v_es_1695_);
        v___x_1709_ = 0usize;
        v___x_1710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1704_,
            v_es_1695_,
            v___f_1706_,
            v_sz_1708_,
            v___x_1709_,
            v___x_1707_,
        );
        v_fst_1711_ = leanh::lean_ctor_get(v___x_1710_, 0);
        leanh::lean_inc(v_fst_1711_);
        leanh::lean_dec(v___x_1710_);
        if leanh::lean_obj_tag(v_fst_1711_) == 0 {
            return v_numDigits_1696_;
        } else {
            let mut v_val_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_numDigits_1696_);
            v_val_1712_ = leanh::lean_ctor_get(v_fst_1711_, 0);
            leanh::lean_inc(v_val_1712_);
            leanh::lean_dec_ref_known(v_fst_1711_, 1);
            return v_val_1712_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg___lam__0(
    mut v_inst_1713_: *mut leanh::LeanObject,
    mut v_shift_1714_: *mut leanh::LeanObject,
    mut v___f_1715_: *mut leanh::LeanObject,
    mut v___f_1716_: *mut leanh::LeanObject,
    mut v___x_1717_: *mut leanh::LeanObject,
    mut v_numDigits_1718_: *mut leanh::LeanObject,
    mut v_es_1719_: *mut leanh::LeanObject,
    mut v_a_1720_: *mut leanh::LeanObject,
    mut v_x_1721_: *mut leanh::LeanObject,
    mut v___y_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: u64 = 0;
    let mut v___x_1729_: u64 = 0;
    let mut v___x_1730_: u64 = 0;
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1748_: u8 = 0;
    let mut v_unused_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1723_ = leanh::lean_ctor_get(v___y_1722_, 1);
                v_isSharedCheck_1748_ = (!leanh::lean_is_exclusive(v___y_1722_)) as u8;
                if v_isSharedCheck_1748_ == 0 {
                    v_unused_1749_ = leanh::lean_ctor_get(v___y_1722_, 0);
                    leanh::lean_dec(v_unused_1749_);
                    v___x_1725_ = v___y_1722_;
                    v_isShared_1726_ = v_isSharedCheck_1748_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1723_);
                    leanh::lean_dec(v___y_1722_);
                    v___x_1725_ = leanh::lean_box(0);
                    v_isShared_1726_ = v_isSharedCheck_1748_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_1713_);
                v___x_1727_ = leanh::lean_apply_1(v_inst_1713_, v_a_1720_);
                v___x_1728_ = lean_uint64_of_nat(v_shift_1714_);
                v___x_1729_ = leanh::lean_unbox_uint64(v___x_1727_);
                leanh::lean_dec_ref(v___x_1727_);
                v___x_1730_ = lean_uint64_shift_right(v___x_1729_, v___x_1728_);
                v___x_1731_ = leanh::lean_box_uint64(v___x_1730_);
                leanh::lean_inc_ref(v___f_1716_);
                leanh::lean_inc_ref(v___f_1715_);
                v___x_1732_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
                    v___f_1715_,
                    v___f_1716_,
                    v_snd_1723_,
                    v___x_1731_,
                );
                if v___x_1732_ == 0 {
                    leanh::lean_dec_ref(v_es_1719_);
                    leanh::lean_dec_ref(v_inst_1713_);
                    v___x_1733_ = leanh::lean_box(0);
                    v___x_1734_ = leanh::lean_box_uint64(v___x_1730_);
                    v___x_1735_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                        v___f_1715_,
                        v___f_1716_,
                        v_snd_1723_,
                        v___x_1734_,
                        v___x_1733_,
                    );
                    if v_isShared_1726_ == 0 {
                        leanh::lean_ctor_set(v___x_1725_, 1, v___x_1735_);
                        leanh::lean_ctor_set(v___x_1725_, 0, v___x_1717_);
                        v___x_1737_ = v___x_1725_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1739_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1717_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 1, v___x_1735_);
                        v___x_1737_ = v_reuseFailAlloc_1739_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1717_);
                    leanh::lean_dec_ref(v___f_1716_);
                    leanh::lean_dec_ref(v___f_1715_);
                    v___x_1740_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1741_ = lean_nat_add(v_numDigits_1718_, v___x_1740_);
                    v___x_1742_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_1713_, v_es_1719_, v___x_1741_);
                    v___x_1743_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1743_, 0, v___x_1742_);
                    if v_isShared_1726_ == 0 {
                        leanh::lean_ctor_set(v___x_1725_, 0, v___x_1743_);
                        v___x_1745_ = v___x_1725_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1747_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1743_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_snd_1723_);
                        v___x_1745_ = v_reuseFailAlloc_1747_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1738_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1738_, 0, v___x_1737_);
                return v___x_1738_;
            }
            3 => {
                v___x_1746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1746_, 0, v___x_1745_);
                return v___x_1746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go(
    mut v_00_u03b1_1750_: *mut leanh::LeanObject,
    mut v_inst_1751_: *mut leanh::LeanObject,
    mut v_es_1752_: *mut leanh::LeanObject,
    mut v_numDigits_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_1751_, v_es_1752_, v_numDigits_1753_);
    return v___x_1754_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter___redArg(
    mut v_x_1755_: *mut leanh::LeanObject,
    mut v_h__1_1756_: *mut leanh::LeanObject,
    mut v_h__2_1757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1755_) == 0 {
        let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1756_);
        v___x_1758_ = leanh::lean_box(0);
        v___x_1759_ = leanh::lean_apply_1(v_h__2_1757_, v___x_1758_);
        return v___x_1759_;
    } else {
        let mut v_val_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1757_);
        v_val_1760_ = leanh::lean_ctor_get(v_x_1755_, 0);
        leanh::lean_inc(v_val_1760_);
        leanh::lean_dec_ref_known(v_x_1755_, 1);
        v___x_1761_ = leanh::lean_apply_1(v_h__1_1756_, v_val_1760_);
        return v___x_1761_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_1762_: *mut leanh::LeanObject,
    mut v_motive_1763_: *mut leanh::LeanObject,
    mut v_x_1764_: *mut leanh::LeanObject,
    mut v_h__1_1765_: *mut leanh::LeanObject,
    mut v_h__2_1766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1764_) == 0 {
        let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1765_);
        v___x_1767_ = leanh::lean_box(0);
        v___x_1768_ = leanh::lean_apply_1(v_h__2_1766_, v___x_1767_);
        return v___x_1768_;
    } else {
        let mut v_val_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1766_);
        v_val_1769_ = leanh::lean_ctor_get(v_x_1764_, 0);
        leanh::lean_inc(v_val_1769_);
        leanh::lean_dec_ref_known(v_x_1764_, 1);
        v___x_1770_ = leanh::lean_apply_1(v_h__1_1765_, v_val_1769_);
        return v___x_1770_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(
    mut v_inst_1771_: *mut leanh::LeanObject,
    mut v_es_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1773_ = leanh::lean_unsigned_to_nat(4);
    v___x_1774_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___redArg(v_inst_1771_, v_es_1772_, v___x_1773_);
    return v___x_1774_;
}
pub unsafe fn l_Lean_Meta_Grind_getNumDigitsForAnchors(
    mut v_00_u03b1_1775_: *mut leanh::LeanObject,
    mut v_inst_1776_: *mut leanh::LeanObject,
    mut v_es_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1778_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___redArg(v_inst_1776_, v_es_1777_);
    return v___x_1778_;
}
pub unsafe fn l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(
    mut v_e_1779_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_anchor_1780_: u64 = 0;
    v_anchor_1780_ = leanh::lean_ctor_get_uint64(
        v_e_1779_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    return v_anchor_1780_;
}
pub unsafe fn l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0___boxed(
    mut v_e_1781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1782_: u64 = 0;
    let mut v_r_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1782_ = l_Lean_Meta_Grind_instHasAnchorExprWithAnchor___lam__0(v_e_1781_);
    leanh::lean_dec_ref(v_e_1781_);
    v_r_1783_ = leanh::lean_box_uint64(v_res_1782_);
    return v_r_1783_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(
    mut v_numDigits_1799_: *mut leanh::LeanObject,
    mut v_anchorPrefix_1800_: u64,
    mut v_a_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1803_ = leanh::lean_ctor_get(v_a_1801_, 5);
    v___x_1804_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__1;
    v___x_1805_ = l_Lean_Meta_Grind_anchorPrefixToString(v_numDigits_1799_, v_anchorPrefix_1800_);
    v___x_1806_ = l_Lean_mkAtom(v___x_1805_);
    v___x_1807_ = leanh::lean_unsigned_to_nat(1);
    v___x_1808_ = lean_mk_empty_array_with_capacity(v___x_1807_);
    v___x_1809_ = lean_array_push(v___x_1808_, v___x_1806_);
    v___x_1810_ = leanh::lean_box(2);
    v___x_1811_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1811_, 0, v___x_1810_);
    leanh::lean_ctor_set(v___x_1811_, 1, v___x_1804_);
    leanh::lean_ctor_set(v___x_1811_, 2, v___x_1809_);
    v___x_1812_ = 0;
    v___x_1813_ = l_Lean_SourceInfo_fromRef(v_ref_1803_, v___x_1812_);
    v___x_1814_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__6;
    v___x_1815_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___closed__7;
    leanh::lean_inc(v___x_1813_);
    v___x_1816_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1816_, 0, v___x_1813_);
    leanh::lean_ctor_set(v___x_1816_, 1, v___x_1815_);
    v___x_1817_ = l_Lean_Syntax_node2(v___x_1813_, v___x_1814_, v___x_1816_, v___x_1811_);
    v___x_1818_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1818_, 0, v___x_1817_);
    return v___x_1818_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg___boxed(
    mut v_numDigits_1819_: *mut leanh::LeanObject,
    mut v_anchorPrefix_1820_: *mut leanh::LeanObject,
    mut v_a_1821_: *mut leanh::LeanObject,
    mut v_a_1822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_anchorPrefix_boxed_1823_: u64 = 0;
    let mut v_res_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_anchorPrefix_boxed_1823_ = leanh::lean_unbox_uint64(v_anchorPrefix_1820_);
    leanh::lean_dec_ref(v_anchorPrefix_1820_);
    v_res_1824_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(
        v_numDigits_1819_,
        v_anchorPrefix_boxed_1823_,
        v_a_1821_,
    );
    leanh::lean_dec_ref(v_a_1821_);
    leanh::lean_dec(v_numDigits_1819_);
    return v_res_1824_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(
    mut v_numDigits_1825_: *mut leanh::LeanObject,
    mut v_anchorPrefix_1826_: u64,
    mut v_a_1827_: *mut leanh::LeanObject,
    mut v_a_1828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___redArg(
        v_numDigits_1825_,
        v_anchorPrefix_1826_,
        v_a_1827_,
    );
    return v___x_1830_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix___boxed(
    mut v_numDigits_1831_: *mut leanh::LeanObject,
    mut v_anchorPrefix_1832_: *mut leanh::LeanObject,
    mut v_a_1833_: *mut leanh::LeanObject,
    mut v_a_1834_: *mut leanh::LeanObject,
    mut v_a_1835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_anchorPrefix_boxed_1836_: u64 = 0;
    let mut v_res_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_anchorPrefix_boxed_1836_ = leanh::lean_unbox_uint64(v_anchorPrefix_1832_);
    leanh::lean_dec_ref(v_anchorPrefix_1832_);
    v_res_1837_ = l_Lean_Meta_Grind_mkAnchorSyntaxFromPrefix(
        v_numDigits_1831_,
        v_anchorPrefix_boxed_1836_,
        v_a_1833_,
        v_a_1834_,
    );
    leanh::lean_dec(v_a_1834_);
    leanh::lean_dec_ref(v_a_1833_);
    leanh::lean_dec(v_numDigits_1831_);
    return v_res_1837_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntax___redArg(
    mut v_numDigits_1838_: *mut leanh::LeanObject,
    mut v_anchor_1839_: u64,
    mut v_a_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1842_: u64 = 0;
    let mut v___x_1843_: u64 = 0;
    let mut v___x_1844_: u64 = 0;
    let mut v___x_1845_: u64 = 0;
    let mut v___x_1846_: u64 = 0;
    let mut v_anchorPrefix_1847_: u64 = 0;
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_numDigits_1849_: *mut leanh::LeanObject,
    mut v_anchor_1850_: *mut leanh::LeanObject,
    mut v_a_1851_: *mut leanh::LeanObject,
    mut v_a_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_anchor_boxed_1853_: u64 = 0;
    let mut v_res_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_anchor_boxed_1853_ = leanh::lean_unbox_uint64(v_anchor_1850_);
    leanh::lean_dec_ref(v_anchor_1850_);
    v_res_1854_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(
        v_numDigits_1849_,
        v_anchor_boxed_1853_,
        v_a_1851_,
    );
    leanh::lean_dec_ref(v_a_1851_);
    leanh::lean_dec(v_numDigits_1849_);
    return v_res_1854_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntax(
    mut v_numDigits_1855_: *mut leanh::LeanObject,
    mut v_anchor_1856_: u64,
    mut v_a_1857_: *mut leanh::LeanObject,
    mut v_a_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1860_ =
        l_Lean_Meta_Grind_mkAnchorSyntax___redArg(v_numDigits_1855_, v_anchor_1856_, v_a_1857_);
    return v___x_1860_;
}
pub unsafe fn l_Lean_Meta_Grind_mkAnchorSyntax___boxed(
    mut v_numDigits_1861_: *mut leanh::LeanObject,
    mut v_anchor_1862_: *mut leanh::LeanObject,
    mut v_a_1863_: *mut leanh::LeanObject,
    mut v_a_1864_: *mut leanh::LeanObject,
    mut v_a_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_anchor_boxed_1866_: u64 = 0;
    let mut v_res_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_anchor_boxed_1866_ = leanh::lean_unbox_uint64(v_anchor_1862_);
    leanh::lean_dec_ref(v_anchor_1862_);
    v_res_1867_ = l_Lean_Meta_Grind_mkAnchorSyntax(
        v_numDigits_1861_,
        v_anchor_boxed_1866_,
        v_a_1863_,
        v_a_1864_,
    );
    leanh::lean_dec(v_a_1864_);
    leanh::lean_dec_ref(v_a_1863_);
    leanh::lean_dec(v_numDigits_1861_);
    return v_res_1867_;
}
pub unsafe fn l_Lean_Meta_Grind_SplitInfo_getAnchor(
    mut v_s_1868_: *mut leanh::LeanObject,
    mut v_a_1869_: *mut leanh::LeanObject,
    mut v_a_1870_: *mut leanh::LeanObject,
    mut v_a_1871_: *mut leanh::LeanObject,
    mut v_a_1872_: *mut leanh::LeanObject,
    mut v_a_1873_: *mut leanh::LeanObject,
    mut v_a_1874_: *mut leanh::LeanObject,
    mut v_a_1875_: *mut leanh::LeanObject,
    mut v_a_1876_: *mut leanh::LeanObject,
    mut v_a_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_s_1881_: *mut leanh::LeanObject,
    mut v_a_1882_: *mut leanh::LeanObject,
    mut v_a_1883_: *mut leanh::LeanObject,
    mut v_a_1884_: *mut leanh::LeanObject,
    mut v_a_1885_: *mut leanh::LeanObject,
    mut v_a_1886_: *mut leanh::LeanObject,
    mut v_a_1887_: *mut leanh::LeanObject,
    mut v_a_1888_: *mut leanh::LeanObject,
    mut v_a_1889_: *mut leanh::LeanObject,
    mut v_a_1890_: *mut leanh::LeanObject,
    mut v_a_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1892_ = l_Lean_Meta_Grind_SplitInfo_getAnchor(
        v_s_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_,
        v_a_1889_, v_a_1890_,
    );
    leanh::lean_dec(v_a_1890_);
    leanh::lean_dec_ref(v_a_1889_);
    leanh::lean_dec(v_a_1888_);
    leanh::lean_dec_ref(v_a_1887_);
    leanh::lean_dec(v_a_1886_);
    leanh::lean_dec_ref(v_a_1885_);
    leanh::lean_dec(v_a_1884_);
    leanh::lean_dec_ref(v_a_1883_);
    leanh::lean_dec(v_a_1882_);
    leanh::lean_dec_ref(v_s_1881_);
    return v_res_1892_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
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
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Anchor(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Anchor(
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
    res = initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
}