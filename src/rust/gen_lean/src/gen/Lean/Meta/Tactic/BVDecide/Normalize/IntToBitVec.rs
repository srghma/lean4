// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec
// Imports: Lean.Meta.Tactic.BVDecide.Normalize.Basic
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
    l_Pi_instInhabited___redArg___lam__0, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_eqv___boxed, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar, l_Lean_Expr_hash, l_Lean_Expr_hash___boxed,
    l_Lean_Expr_isApp, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_replaceFVar, l_Lean_instBEqFVarId_beq, l_Lean_instBEqFVarId_beq___boxed,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableFVarId_hash,
    l_Lean_instHashableFVarId_hash___boxed, l_Lean_instHashableMVarId_hash,
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp6, l_Lean_mkAppN,
    l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkMVar, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofExpr,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getType___redArg,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkFreshExprMVar, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_getNatValue_x3f;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Attr::l_Lean_Meta_Tactic_BVDecide_intToBitVecExt;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Normalize::Basic::{
    initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClearMany_x27;
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_introNCore;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::l_Lean_Meta_simpGoal;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::l_Lean_Meta_SimpExtension_getTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_mkContext___redArg;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getNondepPropHyps, l_Lean_MVarId_getType, l_Lean_Meta_getPropHyps,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_revert, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::ForEachExprWhere::l_Lean_ForEachExprWhere_initCache;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mod, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_string_dec_eq,
    lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_ptr_addr;
use crate::ffi::lean_expr_eqv;
use crate::ffi::lean_replace_expr;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_eqv___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 115, 116, 101, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 108, 97, 116, 102, 111, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 117, 109, 66, 105, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,3794196532276496372 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value) as *mut crate::leanh::LeanObject,3058792918547557504 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value) as *mut crate::leanh::LeanObject,9241886346910436803 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 121, 109, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value) as *mut crate::leanh::LeanObject,15643637366941324764 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value) as *mut crate::leanh::LeanObject,13655884332201764339 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [122, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value) as *mut crate::leanh::LeanObject,5764232124464284678 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 115, 101, 115, 79, 110, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value) as *mut crate::leanh::LeanObject,5881126286461038842 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13_value: crate::leanh::LeanStringObject<76> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 76, m_capacity: 76, m_length: 75, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 114, 101, 97, 116, 101, 32, 98, 105, 110, 100, 101, 114, 32, 100, 117, 101, 32, 116, 111, 32, 102, 97, 105, 108, 117, 114, 101, 32, 119, 104, 101, 110, 32, 114, 101, 118, 101, 114, 116, 105, 110, 103, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0_value: crate::leanh::LeanStringObject<110> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 110, m_capacity: 110, m_length: 109, m_data: [68, 101, 116, 101, 99, 116, 101, 100, 32, 85, 83, 105, 122, 101, 47, 73, 83, 105, 122, 101, 32, 105, 110, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 98, 117, 116, 32, 110, 111, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 97, 98, 111, 117, 116, 32, 83, 121, 115, 116, 101, 109, 46, 80, 108, 97, 116, 102, 111, 114, 109, 46, 110, 117, 109, 66, 105, 116, 115, 44, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 99, 97, 115, 101, 32, 115, 112, 108, 105, 116, 116, 105, 110, 103, 32, 111, 110, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [110, 117, 109, 66, 105, 116, 115, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,3794196532276496372 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value) as *mut crate::leanh::LeanObject,3058792918547557504 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2_value) as *mut crate::leanh::LeanObject,11860477813648696129 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 83, 105, 122, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,17712594561405737325 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,9255850586598716316 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 83, 105, 122, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,16021149375362053230 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,12113648043307972955 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0: usize = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [105, 110, 116, 84, 111, 66, 105, 116, 86, 101, 99, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5625817593341794690 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(
    mut v_e_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3339_ = lean_st_ref_take(v_a_3337_);
                v_relevantTerms_3340_ = crate::leanh::lean_ctor_get(v___x_3339_, 0);
                v_relevantHyps_3341_ = crate::leanh::lean_ctor_get(v___x_3339_, 1);
                v_isSharedCheck_3354_ = (!crate::leanh::lean_is_exclusive(v___x_3339_)) as u8;
                if v_isSharedCheck_3354_ == 0 {
                    v___x_3343_ = v___x_3339_;
                    v_isShared_3344_ = v_isSharedCheck_3354_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_relevantHyps_3341_);
                    crate::leanh::lean_inc(v_relevantTerms_3340_);
                    crate::leanh::lean_dec(v___x_3339_);
                    v___x_3343_ = crate::leanh::lean_box(0);
                    v_isShared_3344_ = v_isSharedCheck_3354_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3345_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0;
                v___x_3346_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1;
                v___x_3347_ = crate::leanh::lean_box(0);
                v___x_3348_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_3345_,
                    v___x_3346_,
                    v_relevantTerms_3340_,
                    v_e_3336_,
                    v___x_3347_,
                );
                if v_isShared_3344_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3343_, 0, v___x_3348_);
                    v___x_3350_ = v___x_3343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3353_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_relevantHyps_3341_);
                    v___x_3350_ = v_reuseFailAlloc_3353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3351_ = lean_st_ref_set(v_a_3337_, v___x_3350_);
                v___x_3352_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3347_);
                return v___x_3352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___boxed(
    mut v_e_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3358_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(v_e_3355_, v_a_3356_);
    crate::leanh::lean_dec(v_a_3356_);
    return v_res_3358_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(
    mut v_e_3359_: *mut crate::leanh::LeanObject,
    mut v_a_3360_: *mut crate::leanh::LeanObject,
    mut v_a_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
    mut v_a_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3371_: u8 = 0;
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3366_ = lean_st_ref_take(v_a_3360_);
                v_relevantTerms_3367_ = crate::leanh::lean_ctor_get(v___x_3366_, 0);
                v_relevantHyps_3368_ = crate::leanh::lean_ctor_get(v___x_3366_, 1);
                v_isSharedCheck_3381_ = (!crate::leanh::lean_is_exclusive(v___x_3366_)) as u8;
                if v_isSharedCheck_3381_ == 0 {
                    v___x_3370_ = v___x_3366_;
                    v_isShared_3371_ = v_isSharedCheck_3381_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_relevantHyps_3368_);
                    crate::leanh::lean_inc(v_relevantTerms_3367_);
                    crate::leanh::lean_dec(v___x_3366_);
                    v___x_3370_ = crate::leanh::lean_box(0);
                    v_isShared_3371_ = v_isSharedCheck_3381_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3372_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0;
                v___x_3373_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1;
                v___x_3374_ = crate::leanh::lean_box(0);
                v___x_3375_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_3372_,
                    v___x_3373_,
                    v_relevantTerms_3367_,
                    v_e_3359_,
                    v___x_3374_,
                );
                if v_isShared_3371_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3370_, 0, v___x_3375_);
                    v___x_3377_ = v___x_3370_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3380_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_relevantHyps_3368_);
                    v___x_3377_ = v_reuseFailAlloc_3380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3378_ = lean_st_ref_set(v_a_3360_, v___x_3377_);
                v___x_3379_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3379_, 0, v___x_3374_);
                return v___x_3379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___boxed(
    mut v_e_3382_: *mut crate::leanh::LeanObject,
    mut v_a_3383_: *mut crate::leanh::LeanObject,
    mut v_a_3384_: *mut crate::leanh::LeanObject,
    mut v_a_3385_: *mut crate::leanh::LeanObject,
    mut v_a_3386_: *mut crate::leanh::LeanObject,
    mut v_a_3387_: *mut crate::leanh::LeanObject,
    mut v_a_3388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3389_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(v_e_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_);
    crate::leanh::lean_dec(v_a_3387_);
    crate::leanh::lean_dec_ref(v_a_3386_);
    crate::leanh::lean_dec(v_a_3385_);
    crate::leanh::lean_dec_ref(v_a_3384_);
    crate::leanh::lean_dec(v_a_3383_);
    return v_res_3389_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(
    mut v_f_3392_: *mut crate::leanh::LeanObject,
    mut v_a_3393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3400_: u8 = 0;
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3395_ = lean_st_ref_take(v_a_3393_);
                v_relevantTerms_3396_ = crate::leanh::lean_ctor_get(v___x_3395_, 0);
                v_relevantHyps_3397_ = crate::leanh::lean_ctor_get(v___x_3395_, 1);
                v_isSharedCheck_3410_ = (!crate::leanh::lean_is_exclusive(v___x_3395_)) as u8;
                if v_isSharedCheck_3410_ == 0 {
                    v___x_3399_ = v___x_3395_;
                    v_isShared_3400_ = v_isSharedCheck_3410_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_relevantHyps_3397_);
                    crate::leanh::lean_inc(v_relevantTerms_3396_);
                    crate::leanh::lean_dec(v___x_3395_);
                    v___x_3399_ = crate::leanh::lean_box(0);
                    v_isShared_3400_ = v_isSharedCheck_3410_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3401_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0;
                v___x_3402_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1;
                v___x_3403_ = crate::leanh::lean_box(0);
                v___x_3404_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_3401_,
                    v___x_3402_,
                    v_relevantHyps_3397_,
                    v_f_3392_,
                    v___x_3403_,
                );
                if v_isShared_3400_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3399_, 1, v___x_3404_);
                    v___x_3406_ = v___x_3399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_relevantTerms_3396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3409_, 1, v___x_3404_);
                    v___x_3406_ = v_reuseFailAlloc_3409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3407_ = lean_st_ref_set(v_a_3393_, v___x_3406_);
                v___x_3408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3408_, 0, v___x_3403_);
                return v___x_3408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___boxed(
    mut v_f_3411_: *mut crate::leanh::LeanObject,
    mut v_a_3412_: *mut crate::leanh::LeanObject,
    mut v_a_3413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3414_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(v_f_3411_, v_a_3412_);
    crate::leanh::lean_dec(v_a_3412_);
    return v_res_3414_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(
    mut v_f_3415_: *mut crate::leanh::LeanObject,
    mut v_a_3416_: *mut crate::leanh::LeanObject,
    mut v_a_3417_: *mut crate::leanh::LeanObject,
    mut v_a_3418_: *mut crate::leanh::LeanObject,
    mut v_a_3419_: *mut crate::leanh::LeanObject,
    mut v_a_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3427_: u8 = 0;
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3422_ = lean_st_ref_take(v_a_3416_);
                v_relevantTerms_3423_ = crate::leanh::lean_ctor_get(v___x_3422_, 0);
                v_relevantHyps_3424_ = crate::leanh::lean_ctor_get(v___x_3422_, 1);
                v_isSharedCheck_3437_ = (!crate::leanh::lean_is_exclusive(v___x_3422_)) as u8;
                if v_isSharedCheck_3437_ == 0 {
                    v___x_3426_ = v___x_3422_;
                    v_isShared_3427_ = v_isSharedCheck_3437_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_relevantHyps_3424_);
                    crate::leanh::lean_inc(v_relevantTerms_3423_);
                    crate::leanh::lean_dec(v___x_3422_);
                    v___x_3426_ = crate::leanh::lean_box(0);
                    v_isShared_3427_ = v_isSharedCheck_3437_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3428_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0;
                v___x_3429_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1;
                v___x_3430_ = crate::leanh::lean_box(0);
                v___x_3431_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_3428_,
                    v___x_3429_,
                    v_relevantHyps_3424_,
                    v_f_3415_,
                    v___x_3430_,
                );
                if v_isShared_3427_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3426_, 1, v___x_3431_);
                    v___x_3433_ = v___x_3426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3436_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_relevantTerms_3423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3436_, 1, v___x_3431_);
                    v___x_3433_ = v_reuseFailAlloc_3436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3434_ = lean_st_ref_set(v_a_3416_, v___x_3433_);
                v___x_3435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3435_, 0, v___x_3430_);
                return v___x_3435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___boxed(
    mut v_f_3438_: *mut crate::leanh::LeanObject,
    mut v_a_3439_: *mut crate::leanh::LeanObject,
    mut v_a_3440_: *mut crate::leanh::LeanObject,
    mut v_a_3441_: *mut crate::leanh::LeanObject,
    mut v_a_3442_: *mut crate::leanh::LeanObject,
    mut v_a_3443_: *mut crate::leanh::LeanObject,
    mut v_a_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3445_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(v_f_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
    crate::leanh::lean_dec(v_a_3443_);
    crate::leanh::lean_dec_ref(v_a_3442_);
    crate::leanh::lean_dec(v_a_3441_);
    crate::leanh::lean_dec_ref(v_a_3440_);
    crate::leanh::lean_dec(v_a_3439_);
    return v_res_3445_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(
    mut v_e_3446_: *mut crate::leanh::LeanObject,
    mut v___y_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3463_: u8 = 0;
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_unused_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3449_ = l_Lean_Expr_hasMVar(v_e_3446_);
                if v___x_3449_ == 0 {
                    v___x_3450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3450_, 0, v_e_3446_);
                    return v___x_3450_;
                } else {
                    v___x_3451_ = lean_st_ref_get(v___y_3447_);
                    v_mctx_3452_ = crate::leanh::lean_ctor_get(v___x_3451_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3452_);
                    crate::leanh::lean_dec(v___x_3451_);
                    v___x_3453_ = l_Lean_instantiateMVarsCore(v_mctx_3452_, v_e_3446_);
                    v_fst_3454_ = crate::leanh::lean_ctor_get(v___x_3453_, 0);
                    crate::leanh::lean_inc(v_fst_3454_);
                    v_snd_3455_ = crate::leanh::lean_ctor_get(v___x_3453_, 1);
                    crate::leanh::lean_inc(v_snd_3455_);
                    crate::leanh::lean_dec_ref(v___x_3453_);
                    v___x_3456_ = lean_st_ref_take(v___y_3447_);
                    v_cache_3457_ = crate::leanh::lean_ctor_get(v___x_3456_, 1);
                    v_zetaDeltaFVarIds_3458_ = crate::leanh::lean_ctor_get(v___x_3456_, 2);
                    v_postponed_3459_ = crate::leanh::lean_ctor_get(v___x_3456_, 3);
                    v_diag_3460_ = crate::leanh::lean_ctor_get(v___x_3456_, 4);
                    v_isSharedCheck_3469_ = (!crate::leanh::lean_is_exclusive(v___x_3456_)) as u8;
                    if v_isSharedCheck_3469_ == 0 {
                        v_unused_3470_ = crate::leanh::lean_ctor_get(v___x_3456_, 0);
                        crate::leanh::lean_dec(v_unused_3470_);
                        v___x_3462_ = v___x_3456_;
                        v_isShared_3463_ = v_isSharedCheck_3469_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_3460_);
                        crate::leanh::lean_inc(v_postponed_3459_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_3458_);
                        crate::leanh::lean_inc(v_cache_3457_);
                        crate::leanh::lean_dec(v___x_3456_);
                        v___x_3462_ = crate::leanh::lean_box(0);
                        v_isShared_3463_ = v_isSharedCheck_3469_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3462_, 0, v_snd_3455_);
                    v___x_3465_ = v___x_3462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3468_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_snd_3455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_cache_3457_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3468_,
                        2,
                        v_zetaDeltaFVarIds_3458_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 3, v_postponed_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 4, v_diag_3460_);
                    v___x_3465_ = v_reuseFailAlloc_3468_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3466_ = lean_st_ref_set(v___y_3447_, v___x_3465_);
                v___x_3467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3467_, 0, v_fst_3454_);
                return v___x_3467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(
    mut v_e_3471_: *mut crate::leanh::LeanObject,
    mut v___y_3472_: *mut crate::leanh::LeanObject,
    mut v___y_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3474_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_3471_, v___y_3472_);
    crate::leanh::lean_dec(v___y_3472_);
    return v_res_3474_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(
    mut v_e_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
    mut v___y_3477_: *mut crate::leanh::LeanObject,
    mut v___y_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3481_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_3475_, v___y_3477_);
    return v___x_3481_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(
    mut v_e_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3488_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(v_e_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
    crate::leanh::lean_dec(v___y_3486_);
    crate::leanh::lean_dec_ref(v___y_3485_);
    crate::leanh::lean_dec(v___y_3484_);
    crate::leanh::lean_dec_ref(v___y_3483_);
    return v_res_3488_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(
    mut v_mvarId_3489_: *mut crate::leanh::LeanObject,
    mut v_x_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3500_: u8 = 0;
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut v_a_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3508_: u8 = 0;
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3496_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_3489_,
                    v_x_3490_,
                    v___y_3491_,
                    v___y_3492_,
                    v___y_3493_,
                    v___y_3494_,
                );
                if crate::leanh::lean_obj_tag(v___x_3496_) == 0 {
                    v_a_3497_ = crate::leanh::lean_ctor_get(v___x_3496_, 0);
                    v_isSharedCheck_3504_ = (!crate::leanh::lean_is_exclusive(v___x_3496_)) as u8;
                    if v_isSharedCheck_3504_ == 0 {
                        v___x_3499_ = v___x_3496_;
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3497_);
                        crate::leanh::lean_dec(v___x_3496_);
                        v___x_3499_ = crate::leanh::lean_box(0);
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3505_ = crate::leanh::lean_ctor_get(v___x_3496_, 0);
                    v_isSharedCheck_3512_ = (!crate::leanh::lean_is_exclusive(v___x_3496_)) as u8;
                    if v_isSharedCheck_3512_ == 0 {
                        v___x_3507_ = v___x_3496_;
                        v_isShared_3508_ = v_isSharedCheck_3512_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3505_);
                        crate::leanh::lean_dec(v___x_3496_);
                        v___x_3507_ = crate::leanh::lean_box(0);
                        v_isShared_3508_ = v_isSharedCheck_3512_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3500_ == 0 {
                    v___x_3502_ = v___x_3499_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
                    v___x_3502_ = v_reuseFailAlloc_3503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3502_;
            }
            3 => {
                if v_isShared_3508_ == 0 {
                    v___x_3510_ = v___x_3507_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3511_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
                    v___x_3510_ = v_reuseFailAlloc_3511_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg___boxed(
    mut v_mvarId_3513_: *mut crate::leanh::LeanObject,
    mut v_x_3514_: *mut crate::leanh::LeanObject,
    mut v___y_3515_: *mut crate::leanh::LeanObject,
    mut v___y_3516_: *mut crate::leanh::LeanObject,
    mut v___y_3517_: *mut crate::leanh::LeanObject,
    mut v___y_3518_: *mut crate::leanh::LeanObject,
    mut v___y_3519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3520_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_3513_, v_x_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
    crate::leanh::lean_dec(v___y_3518_);
    crate::leanh::lean_dec_ref(v___y_3517_);
    crate::leanh::lean_dec(v___y_3516_);
    crate::leanh::lean_dec_ref(v___y_3515_);
    return v_res_3520_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(
    mut v_00_u03b1_3521_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3522_: *mut crate::leanh::LeanObject,
    mut v_x_3523_: *mut crate::leanh::LeanObject,
    mut v___y_3524_: *mut crate::leanh::LeanObject,
    mut v___y_3525_: *mut crate::leanh::LeanObject,
    mut v___y_3526_: *mut crate::leanh::LeanObject,
    mut v___y_3527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3529_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_3522_, v_x_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
    return v___x_3529_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(
    mut v_00_u03b1_3530_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3531_: *mut crate::leanh::LeanObject,
    mut v_x_3532_: *mut crate::leanh::LeanObject,
    mut v___y_3533_: *mut crate::leanh::LeanObject,
    mut v___y_3534_: *mut crate::leanh::LeanObject,
    mut v___y_3535_: *mut crate::leanh::LeanObject,
    mut v___y_3536_: *mut crate::leanh::LeanObject,
    mut v___y_3537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3538_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(v_00_u03b1_3530_, v_mvarId_3531_, v_x_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
    crate::leanh::lean_dec(v___y_3536_);
    crate::leanh::lean_dec_ref(v___y_3535_);
    crate::leanh::lean_dec(v___y_3534_);
    crate::leanh::lean_dec_ref(v___y_3533_);
    return v_res_3538_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3561_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3562_ = l_Lean_Level_ofNat(v___x_3561_);
    return v___x_3562_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3563_ = crate::leanh::lean_box(0);
    v___x_3564_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
    v___x_3565_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3565_, 0, v___x_3564_);
    crate::leanh::lean_ctor_set(v___x_3565_, 1, v___x_3563_);
    return v___x_3565_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3566_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
    v___x_3567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10;
    v___x_3568_ = l_Lean_mkConst(v___x_3567_, v___x_3566_);
    return v___x_3568_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(
    mut v_as_3569_: *mut crate::leanh::LeanObject,
    mut v_sz_3570_: usize,
    mut v_i_3571_: usize,
    mut v_b_3572_: *mut crate::leanh::LeanObject,
    mut v___y_3573_: *mut crate::leanh::LeanObject,
    mut v___y_3574_: *mut crate::leanh::LeanObject,
    mut v___y_3575_: *mut crate::leanh::LeanObject,
    mut v___y_3576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3578_: u8 = 0;
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: usize = 0;
    let mut v___x_3590_: usize = 0;
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: u8 = 0;
    let mut v_arg_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v_arg_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: u8 = 0;
    let mut v_arg_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: u8 = 0;
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: u8 = 0;
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3613_: u8 = 0;
    let mut v_val_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3617_: u8 = 0;
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3633_: u8 = 0;
    let mut v_a_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3646_: u8 = 0;
    let mut v_val_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3650_: u8 = 0;
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3668_: u8 = 0;
    let mut v_a_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3676_: u8 = 0;
    let mut v_a_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3680_: u8 = 0;
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3684_: u8 = 0;
    let mut v_a_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3688_: u8 = 0;
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut v_a_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3578_ = lean_usize_dec_lt(v_i_3571_, v_sz_3570_);
                if v___x_3578_ == 0 {
                    v___x_3579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3579_, 0, v_b_3572_);
                    return v___x_3579_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3572_);
                    v_a_3580_ = lean_array_uget_borrowed(v_as_3569_, v_i_3571_);
                    crate::leanh::lean_inc(v_a_3580_);
                    v___x_3581_ = l_Lean_FVarId_getType___redArg(
                        v_a_3580_,
                        v___y_3573_,
                        v___y_3575_,
                        v___y_3576_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3581_) == 0 {
                        v_a_3582_ = crate::leanh::lean_ctor_get(v___x_3581_, 0);
                        crate::leanh::lean_inc(v_a_3582_);
                        crate::leanh::lean_dec_ref_known(v___x_3581_, 1);
                        v___x_3583_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_a_3582_, v___y_3574_);
                        if crate::leanh::lean_obj_tag(v___x_3583_) == 0 {
                            v_a_3584_ = crate::leanh::lean_ctor_get(v___x_3583_, 0);
                            crate::leanh::lean_inc(v_a_3584_);
                            crate::leanh::lean_dec_ref_known(v___x_3583_, 1);
                            v___x_3585_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                v_a_3584_,
                                v___y_3574_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3585_) == 0 {
                                v_a_3586_ = crate::leanh::lean_ctor_get(v___x_3585_, 0);
                                crate::leanh::lean_inc(v_a_3586_);
                                crate::leanh::lean_dec_ref_known(v___x_3585_, 1);
                                v___x_3592_ = crate::leanh::lean_box(0);
                                v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0;
                                v___x_3594_ = l_Lean_Expr_cleanupAnnotations(v_a_3586_);
                                v___x_3595_ = l_Lean_Expr_isApp(v___x_3594_);
                                if v___x_3595_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_3594_);
                                    v_a_3588_ = v___x_3593_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_3596_ = crate::leanh::lean_ctor_get(v___x_3594_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_3596_);
                                    v___x_3597_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3594_);
                                    v___x_3598_ = l_Lean_Expr_isApp(v___x_3597_);
                                    if v___x_3598_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_3597_);
                                        crate::leanh::lean_dec_ref(v_arg_3596_);
                                        v_a_3588_ = v___x_3593_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_3599_ = crate::leanh::lean_ctor_get(v___x_3597_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_3599_);
                                        v___x_3600_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3597_);
                                        v___x_3601_ = l_Lean_Expr_isApp(v___x_3600_);
                                        if v___x_3601_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_3600_);
                                            crate::leanh::lean_dec_ref(v_arg_3599_);
                                            crate::leanh::lean_dec_ref(v_arg_3596_);
                                            v_a_3588_ = v___x_3593_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_arg_3602_ =
                                                crate::leanh::lean_ctor_get(v___x_3600_, 1);
                                            crate::leanh::lean_inc_ref(v_arg_3602_);
                                            v___x_3603_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3600_);
                                            v___x_3604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2;
                                            v___x_3605_ =
                                                l_Lean_Expr_isConstOf(v___x_3603_, v___x_3604_);
                                            crate::leanh::lean_dec_ref(v___x_3603_);
                                            if v___x_3605_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_3602_);
                                                crate::leanh::lean_dec_ref(v_arg_3599_);
                                                crate::leanh::lean_dec_ref(v_arg_3596_);
                                                v_a_3588_ = v___x_3593_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6;
                                                v___x_3607_ =
                                                    l_Lean_Expr_isConstOf(v_arg_3599_, v___x_3606_);
                                                if v___x_3607_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_arg_3602_);
                                                    v___x_3608_ = l_Lean_Expr_isConstOf(
                                                        v_arg_3596_,
                                                        v___x_3606_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v_arg_3596_);
                                                    if v___x_3608_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_3599_);
                                                        v_a_3588_ = v___x_3593_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_3609_ = l_Lean_Meta_getNatValue_x3f(
                                                            v_arg_3599_,
                                                            v___y_3573_,
                                                            v___y_3574_,
                                                            v___y_3575_,
                                                            v___y_3576_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v_arg_3599_);
                                                        if crate::leanh::lean_obj_tag(v___x_3609_)
                                                            == 0
                                                        {
                                                            v_a_3610_ = crate::leanh::lean_ctor_get(
                                                                v___x_3609_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_3633_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_3609_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_3633_ == 0 {
                                                                v___x_3612_ = v___x_3609_;
                                                                v_isShared_3613_ =
                                                                    v_isSharedCheck_3633_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_3610_);
                                                                crate::leanh::lean_dec(v___x_3609_);
                                                                v___x_3612_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_3613_ =
                                                                    v_isSharedCheck_3633_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_3634_ = crate::leanh::lean_ctor_get(
                                                                v___x_3609_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_3641_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_3609_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_3641_ == 0 {
                                                                v___x_3636_ = v___x_3609_;
                                                                v_isShared_3637_ =
                                                                    v_isSharedCheck_3641_;
                                                                state = 7;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_3634_);
                                                                crate::leanh::lean_dec(v___x_3609_);
                                                                v___x_3636_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_3637_ =
                                                                    v_isSharedCheck_3641_;
                                                                state = 7;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    v___x_3642_ = l_Lean_Meta_getNatValue_x3f(
                                                        v_arg_3596_,
                                                        v___y_3573_,
                                                        v___y_3574_,
                                                        v___y_3575_,
                                                        v___y_3576_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_3642_) == 0
                                                    {
                                                        v_a_3643_ = crate::leanh::lean_ctor_get(
                                                            v___x_3642_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3668_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_3642_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3668_ == 0 {
                                                            v___x_3645_ = v___x_3642_;
                                                            v_isShared_3646_ =
                                                                v_isSharedCheck_3668_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_3643_);
                                                            crate::leanh::lean_dec(v___x_3642_);
                                                            v___x_3645_ = crate::leanh::lean_box(0);
                                                            v_isShared_3646_ =
                                                                v_isSharedCheck_3668_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_arg_3602_);
                                                        crate::leanh::lean_dec_ref(v_arg_3599_);
                                                        crate::leanh::lean_dec_ref(v_arg_3596_);
                                                        v_a_3669_ = crate::leanh::lean_ctor_get(
                                                            v___x_3642_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3676_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_3642_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3676_ == 0 {
                                                            v___x_3671_ = v___x_3642_;
                                                            v_isShared_3672_ =
                                                                v_isSharedCheck_3676_;
                                                            state = 14;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_3669_);
                                                            crate::leanh::lean_dec(v___x_3642_);
                                                            v___x_3671_ = crate::leanh::lean_box(0);
                                                            v_isShared_3672_ =
                                                                v_isSharedCheck_3676_;
                                                            state = 14;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                v_a_3677_ = crate::leanh::lean_ctor_get(v___x_3585_, 0);
                                v_isSharedCheck_3684_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3585_)) as u8;
                                if v_isSharedCheck_3684_ == 0 {
                                    v___x_3679_ = v___x_3585_;
                                    v_isShared_3680_ = v_isSharedCheck_3684_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3677_);
                                    crate::leanh::lean_dec(v___x_3585_);
                                    v___x_3679_ = crate::leanh::lean_box(0);
                                    v_isShared_3680_ = v_isSharedCheck_3684_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            v_a_3685_ = crate::leanh::lean_ctor_get(v___x_3583_, 0);
                            v_isSharedCheck_3692_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3583_)) as u8;
                            if v_isSharedCheck_3692_ == 0 {
                                v___x_3687_ = v___x_3583_;
                                v_isShared_3688_ = v_isSharedCheck_3692_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3685_);
                                crate::leanh::lean_dec(v___x_3583_);
                                v___x_3687_ = crate::leanh::lean_box(0);
                                v_isShared_3688_ = v_isSharedCheck_3692_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        v_a_3693_ = crate::leanh::lean_ctor_get(v___x_3581_, 0);
                        v_isSharedCheck_3700_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3581_)) as u8;
                        if v_isSharedCheck_3700_ == 0 {
                            v___x_3695_ = v___x_3581_;
                            v_isShared_3696_ = v_isSharedCheck_3700_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3693_);
                            crate::leanh::lean_dec(v___x_3581_);
                            v___x_3695_ = crate::leanh::lean_box(0);
                            v_isShared_3696_ = v_isSharedCheck_3700_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3589_ = 1usize;
                v___x_3590_ = lean_usize_add(v_i_3571_, v___x_3589_);
                crate::leanh::lean_inc_ref(v_a_3588_);
                v_i_3571_ = v___x_3590_;
                v_b_3572_ = v_a_3588_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3610_) == 1 {
                    v_val_3614_ = crate::leanh::lean_ctor_get(v_a_3610_, 0);
                    v_isSharedCheck_3628_ = (!crate::leanh::lean_is_exclusive(v_a_3610_)) as u8;
                    if v_isSharedCheck_3628_ == 0 {
                        v___x_3616_ = v_a_3610_;
                        v_isShared_3617_ = v_isSharedCheck_3628_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3614_);
                        crate::leanh::lean_dec(v_a_3610_);
                        v___x_3616_ = crate::leanh::lean_box(0);
                        v_isShared_3617_ = v_isSharedCheck_3628_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3610_);
                    v___x_3629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8;
                    if v_isShared_3613_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3612_, 0, v___x_3629_);
                        v___x_3631_ = v___x_3612_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
                        v___x_3631_ = v_reuseFailAlloc_3632_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_3580_);
                v___x_3618_ = l_Lean_mkFVar(v_a_3580_);
                v___x_3619_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3619_, 0, v_val_3614_);
                crate::leanh::lean_ctor_set(v___x_3619_, 1, v___x_3618_);
                if v_isShared_3617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3616_, 0, v___x_3619_);
                    v___x_3621_ = v___x_3616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3619_);
                    v___x_3621_ = v_reuseFailAlloc_3627_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3622_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3622_, 0, v___x_3621_);
                v___x_3623_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3623_, 0, v___x_3622_);
                crate::leanh::lean_ctor_set(v___x_3623_, 1, v___x_3592_);
                if v_isShared_3613_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3612_, 0, v___x_3623_);
                    v___x_3625_ = v___x_3612_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
                    v___x_3625_ = v_reuseFailAlloc_3626_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3625_;
            }
            6 => {
                return v___x_3631_;
            }
            7 => {
                if v_isShared_3637_ == 0 {
                    v___x_3639_ = v___x_3636_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3640_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
                    v___x_3639_ = v_reuseFailAlloc_3640_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3639_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_a_3643_) == 1 {
                    v_val_3647_ = crate::leanh::lean_ctor_get(v_a_3643_, 0);
                    v_isSharedCheck_3663_ = (!crate::leanh::lean_is_exclusive(v_a_3643_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v___x_3649_ = v_a_3643_;
                        v_isShared_3650_ = v_isSharedCheck_3663_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3647_);
                        crate::leanh::lean_dec(v_a_3643_);
                        v___x_3649_ = crate::leanh::lean_box(0);
                        v_isShared_3650_ = v_isSharedCheck_3663_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3643_);
                    crate::leanh::lean_dec_ref(v_arg_3602_);
                    crate::leanh::lean_dec_ref(v_arg_3599_);
                    crate::leanh::lean_dec_ref(v_arg_3596_);
                    v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8;
                    if v_isShared_3646_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3645_, 0, v___x_3664_);
                        v___x_3666_ = v___x_3645_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
                        v___x_3666_ = v_reuseFailAlloc_3667_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                v___x_3651_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13);
                crate::leanh::lean_inc(v_a_3580_);
                v___x_3652_ = l_Lean_mkFVar(v_a_3580_);
                v___x_3653_ = l_Lean_mkApp4(
                    v___x_3651_,
                    v_arg_3602_,
                    v_arg_3599_,
                    v_arg_3596_,
                    v___x_3652_,
                );
                v___x_3654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3654_, 0, v_val_3647_);
                crate::leanh::lean_ctor_set(v___x_3654_, 1, v___x_3653_);
                if v_isShared_3650_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3649_, 0, v___x_3654_);
                    v___x_3656_ = v___x_3649_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3654_);
                    v___x_3656_ = v_reuseFailAlloc_3662_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3657_, 0, v___x_3656_);
                v___x_3658_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3658_, 0, v___x_3657_);
                crate::leanh::lean_ctor_set(v___x_3658_, 1, v___x_3592_);
                if v_isShared_3646_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3645_, 0, v___x_3658_);
                    v___x_3660_ = v___x_3645_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
                    v___x_3660_ = v_reuseFailAlloc_3661_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3660_;
            }
            13 => {
                return v___x_3666_;
            }
            14 => {
                if v_isShared_3672_ == 0 {
                    v___x_3674_ = v___x_3671_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3675_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
                    v___x_3674_ = v_reuseFailAlloc_3675_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3674_;
            }
            16 => {
                if v_isShared_3680_ == 0 {
                    v___x_3682_ = v___x_3679_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
                    v___x_3682_ = v_reuseFailAlloc_3683_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3682_;
            }
            18 => {
                if v_isShared_3688_ == 0 {
                    v___x_3690_ = v___x_3687_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3691_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
                    v___x_3690_ = v_reuseFailAlloc_3691_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3690_;
            }
            20 => {
                if v_isShared_3696_ == 0 {
                    v___x_3698_ = v___x_3695_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3699_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
                    v___x_3698_ = v_reuseFailAlloc_3699_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___boxed(
    mut v_as_3701_: *mut crate::leanh::LeanObject,
    mut v_sz_3702_: *mut crate::leanh::LeanObject,
    mut v_i_3703_: *mut crate::leanh::LeanObject,
    mut v_b_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
    mut v___y_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
    mut v___y_3709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3710_: usize = 0;
    let mut v_i_boxed_3711_: usize = 0;
    let mut v_res_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3710_ = crate::leanh::lean_unbox_usize(v_sz_3702_);
    crate::leanh::lean_dec(v_sz_3702_);
    v_i_boxed_3711_ = crate::leanh::lean_unbox_usize(v_i_3703_);
    crate::leanh::lean_dec(v_i_3703_);
    v_res_3712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_as_3701_, v_sz_boxed_3710_, v_i_boxed_3711_, v_b_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
    crate::leanh::lean_dec(v___y_3708_);
    crate::leanh::lean_dec_ref(v___y_3707_);
    crate::leanh::lean_dec(v___y_3706_);
    crate::leanh::lean_dec_ref(v___y_3705_);
    crate::leanh::lean_dec_ref(v_as_3701_);
    return v_res_3712_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(
    mut v___y_3713_: *mut crate::leanh::LeanObject,
    mut v___y_3714_: *mut crate::leanh::LeanObject,
    mut v___y_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3722_: usize = 0;
    let mut v___x_3723_: usize = 0;
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3728_: u8 = 0;
    let mut v_fst_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut v_a_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut v_a_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3749_: u8 = 0;
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3718_ =
                    l_Lean_Meta_getPropHyps(v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
                if crate::leanh::lean_obj_tag(v___x_3718_) == 0 {
                    v_a_3719_ = crate::leanh::lean_ctor_get(v___x_3718_, 0);
                    crate::leanh::lean_inc(v_a_3719_);
                    crate::leanh::lean_dec_ref_known(v___x_3718_, 1);
                    v___x_3720_ = crate::leanh::lean_box(0);
                    v___x_3721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0;
                    v_sz_3722_ = lean_array_size(v_a_3719_);
                    v___x_3723_ = 0usize;
                    v___x_3724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_a_3719_, v_sz_3722_, v___x_3723_, v___x_3721_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
                    crate::leanh::lean_dec(v_a_3719_);
                    if crate::leanh::lean_obj_tag(v___x_3724_) == 0 {
                        v_a_3725_ = crate::leanh::lean_ctor_get(v___x_3724_, 0);
                        v_isSharedCheck_3737_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3724_)) as u8;
                        if v_isSharedCheck_3737_ == 0 {
                            v___x_3727_ = v___x_3724_;
                            v_isShared_3728_ = v_isSharedCheck_3737_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3725_);
                            crate::leanh::lean_dec(v___x_3724_);
                            v___x_3727_ = crate::leanh::lean_box(0);
                            v_isShared_3728_ = v_isSharedCheck_3737_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3738_ = crate::leanh::lean_ctor_get(v___x_3724_, 0);
                        v_isSharedCheck_3745_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3724_)) as u8;
                        if v_isSharedCheck_3745_ == 0 {
                            v___x_3740_ = v___x_3724_;
                            v_isShared_3741_ = v_isSharedCheck_3745_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3738_);
                            crate::leanh::lean_dec(v___x_3724_);
                            v___x_3740_ = crate::leanh::lean_box(0);
                            v_isShared_3741_ = v_isSharedCheck_3745_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_3746_ = crate::leanh::lean_ctor_get(v___x_3718_, 0);
                    v_isSharedCheck_3753_ = (!crate::leanh::lean_is_exclusive(v___x_3718_)) as u8;
                    if v_isSharedCheck_3753_ == 0 {
                        v___x_3748_ = v___x_3718_;
                        v_isShared_3749_ = v_isSharedCheck_3753_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3746_);
                        crate::leanh::lean_dec(v___x_3718_);
                        v___x_3748_ = crate::leanh::lean_box(0);
                        v_isShared_3749_ = v_isSharedCheck_3753_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3729_ = crate::leanh::lean_ctor_get(v_a_3725_, 0);
                crate::leanh::lean_inc(v_fst_3729_);
                crate::leanh::lean_dec(v_a_3725_);
                if crate::leanh::lean_obj_tag(v_fst_3729_) == 0 {
                    if v_isShared_3728_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3727_, 0, v___x_3720_);
                        v___x_3731_ = v___x_3727_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3732_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3720_);
                        v___x_3731_ = v_reuseFailAlloc_3732_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3733_ = crate::leanh::lean_ctor_get(v_fst_3729_, 0);
                    crate::leanh::lean_inc(v_val_3733_);
                    crate::leanh::lean_dec_ref_known(v_fst_3729_, 1);
                    if v_isShared_3728_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3727_, 0, v_val_3733_);
                        v___x_3735_ = v___x_3727_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3736_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_val_3733_);
                        v___x_3735_ = v_reuseFailAlloc_3736_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3731_;
            }
            3 => {
                return v___x_3735_;
            }
            4 => {
                if v_isShared_3741_ == 0 {
                    v___x_3743_ = v___x_3740_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
                    v___x_3743_ = v_reuseFailAlloc_3744_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3743_;
            }
            6 => {
                if v_isShared_3749_ == 0 {
                    v___x_3751_ = v___x_3748_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3752_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
                    v___x_3751_ = v_reuseFailAlloc_3752_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed(
    mut v___y_3754_: *mut crate::leanh::LeanObject,
    mut v___y_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3759_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
    crate::leanh::lean_dec(v___y_3757_);
    crate::leanh::lean_dec_ref(v___y_3756_);
    crate::leanh::lean_dec(v___y_3755_);
    crate::leanh::lean_dec_ref(v___y_3754_);
    return v_res_3759_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(
    mut v_goal_3761_: *mut crate::leanh::LeanObject,
    mut v_a_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: *mut crate::leanh::LeanObject,
    mut v_a_3764_: *mut crate::leanh::LeanObject,
    mut v_a_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3767_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0;
    v___x_3768_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_goal_3761_, v___f_3767_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_);
    return v___x_3768_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___boxed(
    mut v_goal_3769_: *mut crate::leanh::LeanObject,
    mut v_a_3770_: *mut crate::leanh::LeanObject,
    mut v_a_3771_: *mut crate::leanh::LeanObject,
    mut v_a_3772_: *mut crate::leanh::LeanObject,
    mut v_a_3773_: *mut crate::leanh::LeanObject,
    mut v_a_3774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3775_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(v_goal_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
    crate::leanh::lean_dec(v_a_3773_);
    crate::leanh::lean_dec_ref(v_a_3772_);
    crate::leanh::lean_dec(v_a_3771_);
    crate::leanh::lean_dec_ref(v_a_3770_);
    return v_res_3775_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(
    mut v_x_3776_: *mut crate::leanh::LeanObject,
    mut v___y_3777_: *mut crate::leanh::LeanObject,
    mut v___y_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3777_);
    v___x_3783_ = crate::leanh::lean_apply_6(
        v_x_3776_,
        v___y_3777_,
        v___y_3778_,
        v___y_3779_,
        v___y_3780_,
        v___y_3781_,
        crate::leanh::lean_box(0),
    );
    return v___x_3783_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed(
    mut v_x_3784_: *mut crate::leanh::LeanObject,
    mut v___y_3785_: *mut crate::leanh::LeanObject,
    mut v___y_3786_: *mut crate::leanh::LeanObject,
    mut v___y_3787_: *mut crate::leanh::LeanObject,
    mut v___y_3788_: *mut crate::leanh::LeanObject,
    mut v___y_3789_: *mut crate::leanh::LeanObject,
    mut v___y_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(v_x_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
    crate::leanh::lean_dec(v___y_3785_);
    return v_res_3791_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(
    mut v_mvarId_3792_: *mut crate::leanh::LeanObject,
    mut v_x_3793_: *mut crate::leanh::LeanObject,
    mut v___y_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
    mut v___y_3796_: *mut crate::leanh::LeanObject,
    mut v___y_3797_: *mut crate::leanh::LeanObject,
    mut v___y_3798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3805_: u8 = 0;
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3794_);
                v___f_3800_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                crate::leanh::lean_closure_set(v___f_3800_, 0, v_x_3793_);
                crate::leanh::lean_closure_set(v___f_3800_, 1, v___y_3794_);
                v___x_3801_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_3792_,
                    v___f_3800_,
                    v___y_3795_,
                    v___y_3796_,
                    v___y_3797_,
                    v___y_3798_,
                );
                if crate::leanh::lean_obj_tag(v___x_3801_) == 0 {
                    return v___x_3801_;
                } else {
                    v_a_3802_ = crate::leanh::lean_ctor_get(v___x_3801_, 0);
                    v_isSharedCheck_3809_ = (!crate::leanh::lean_is_exclusive(v___x_3801_)) as u8;
                    if v_isSharedCheck_3809_ == 0 {
                        v___x_3804_ = v___x_3801_;
                        v_isShared_3805_ = v_isSharedCheck_3809_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3802_);
                        crate::leanh::lean_dec(v___x_3801_);
                        v___x_3804_ = crate::leanh::lean_box(0);
                        v_isShared_3805_ = v_isSharedCheck_3809_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3805_ == 0 {
                    v___x_3807_ = v___x_3804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
                    v___x_3807_ = v_reuseFailAlloc_3808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___boxed(
    mut v_mvarId_3810_: *mut crate::leanh::LeanObject,
    mut v_x_3811_: *mut crate::leanh::LeanObject,
    mut v___y_3812_: *mut crate::leanh::LeanObject,
    mut v___y_3813_: *mut crate::leanh::LeanObject,
    mut v___y_3814_: *mut crate::leanh::LeanObject,
    mut v___y_3815_: *mut crate::leanh::LeanObject,
    mut v___y_3816_: *mut crate::leanh::LeanObject,
    mut v___y_3817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3818_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_mvarId_3810_, v_x_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
    crate::leanh::lean_dec(v___y_3816_);
    crate::leanh::lean_dec_ref(v___y_3815_);
    crate::leanh::lean_dec(v___y_3814_);
    crate::leanh::lean_dec_ref(v___y_3813_);
    crate::leanh::lean_dec(v___y_3812_);
    return v_res_3818_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14(
    mut v_00_u03b1_3819_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3820_: *mut crate::leanh::LeanObject,
    mut v_x_3821_: *mut crate::leanh::LeanObject,
    mut v___y_3822_: *mut crate::leanh::LeanObject,
    mut v___y_3823_: *mut crate::leanh::LeanObject,
    mut v___y_3824_: *mut crate::leanh::LeanObject,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
    mut v___y_3826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3828_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_mvarId_3820_, v_x_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
    return v___x_3828_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___boxed(
    mut v_00_u03b1_3829_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3830_: *mut crate::leanh::LeanObject,
    mut v_x_3831_: *mut crate::leanh::LeanObject,
    mut v___y_3832_: *mut crate::leanh::LeanObject,
    mut v___y_3833_: *mut crate::leanh::LeanObject,
    mut v___y_3834_: *mut crate::leanh::LeanObject,
    mut v___y_3835_: *mut crate::leanh::LeanObject,
    mut v___y_3836_: *mut crate::leanh::LeanObject,
    mut v___y_3837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3838_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14(v_00_u03b1_3829_, v_mvarId_3830_, v_x_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
    crate::leanh::lean_dec(v___y_3836_);
    crate::leanh::lean_dec_ref(v___y_3835_);
    crate::leanh::lean_dec(v___y_3834_);
    crate::leanh::lean_dec_ref(v___y_3833_);
    crate::leanh::lean_dec(v___y_3832_);
    return v_res_3838_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(
    mut v_a_3839_: *mut crate::leanh::LeanObject,
    mut v_x_3840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: u8 = 0;
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3840_) == 0 {
                    v___x_3841_ = crate::leanh::lean_box(0);
                    return v___x_3841_;
                } else {
                    v_key_3842_ = crate::leanh::lean_ctor_get(v_x_3840_, 0);
                    v_value_3843_ = crate::leanh::lean_ctor_get(v_x_3840_, 1);
                    v_tail_3844_ = crate::leanh::lean_ctor_get(v_x_3840_, 2);
                    v___x_3845_ = lean_expr_eqv(v_key_3842_, v_a_3839_);
                    if v___x_3845_ == 0 {
                        v_x_3840_ = v_tail_3844_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3843_);
                        v___x_3847_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3847_, 0, v_value_3843_);
                        return v___x_3847_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg___boxed(
    mut v_a_3848_: *mut crate::leanh::LeanObject,
    mut v_x_3849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_3848_, v_x_3849_);
    crate::leanh::lean_dec(v_x_3849_);
    crate::leanh::lean_dec_ref(v_a_3848_);
    return v_res_3850_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(
    mut v_m_3851_: *mut crate::leanh::LeanObject,
    mut v_a_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: u64 = 0;
    let mut v___x_3856_: u64 = 0;
    let mut v___x_3857_: u64 = 0;
    let mut v_fold_3858_: u64 = 0;
    let mut v___x_3859_: u64 = 0;
    let mut v___x_3860_: u64 = 0;
    let mut v___x_3861_: u64 = 0;
    let mut v___x_3862_: usize = 0;
    let mut v___x_3863_: usize = 0;
    let mut v___x_3864_: usize = 0;
    let mut v___x_3865_: usize = 0;
    let mut v___x_3866_: usize = 0;
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3853_ = crate::leanh::lean_ctor_get(v_m_3851_, 1);
    v___x_3854_ = lean_array_get_size(v_buckets_3853_);
    v___x_3855_ = l_Lean_Expr_hash(v_a_3852_);
    v___x_3856_ = 32u64;
    v___x_3857_ = lean_uint64_shift_right(v___x_3855_, v___x_3856_);
    v_fold_3858_ = lean_uint64_xor(v___x_3855_, v___x_3857_);
    v___x_3859_ = 16u64;
    v___x_3860_ = lean_uint64_shift_right(v_fold_3858_, v___x_3859_);
    v___x_3861_ = lean_uint64_xor(v_fold_3858_, v___x_3860_);
    v___x_3862_ = lean_uint64_to_usize(v___x_3861_);
    v___x_3863_ = lean_usize_of_nat(v___x_3854_);
    v___x_3864_ = 1usize;
    v___x_3865_ = lean_usize_sub(v___x_3863_, v___x_3864_);
    v___x_3866_ = lean_usize_land(v___x_3862_, v___x_3865_);
    v___x_3867_ = lean_array_uget_borrowed(v_buckets_3853_, v___x_3866_);
    v___x_3868_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_3852_, v___x_3867_);
    return v___x_3868_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg___boxed(
    mut v_m_3869_: *mut crate::leanh::LeanObject,
    mut v_a_3870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_3869_, v_a_3870_);
    crate::leanh::lean_dec_ref(v_a_3870_);
    crate::leanh::lean_dec_ref(v_m_3869_);
    return v_res_3871_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0(
    mut v_fst_3872_: *mut crate::leanh::LeanObject,
    mut v___y_3873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3874_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_fst_3872_, v___y_3873_);
    return v___x_3874_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0___boxed(
    mut v_fst_3875_: *mut crate::leanh::LeanObject,
    mut v___y_3876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3877_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0(v_fst_3875_, v___y_3876_);
    crate::leanh::lean_dec_ref(v___y_3876_);
    crate::leanh::lean_dec(v_fst_3875_);
    return v_res_3877_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(
    mut v_a_3878_: *mut crate::leanh::LeanObject,
    mut v_x_3879_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3880_: u8 = 0;
    let mut v_key_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3879_) == 0 {
                    v___x_3880_ = 0;
                    return v___x_3880_;
                } else {
                    v_key_3881_ = crate::leanh::lean_ctor_get(v_x_3879_, 0);
                    v_tail_3882_ = crate::leanh::lean_ctor_get(v_x_3879_, 2);
                    v___x_3883_ = lean_expr_eqv(v_key_3881_, v_a_3878_);
                    if v___x_3883_ == 0 {
                        v_x_3879_ = v_tail_3882_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3883_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg___boxed(
    mut v_a_3885_: *mut crate::leanh::LeanObject,
    mut v_x_3886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3887_: u8 = 0;
    let mut v_r_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3887_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_3885_, v_x_3886_);
    crate::leanh::lean_dec(v_x_3886_);
    crate::leanh::lean_dec_ref(v_a_3885_);
    v_r_3888_ = crate::leanh::lean_box((v_res_3887_) as usize);
    return v_r_3888_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(
    mut v_x_3889_: *mut crate::leanh::LeanObject,
    mut v_x_3890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: u64 = 0;
    let mut v___x_3899_: u64 = 0;
    let mut v___x_3900_: u64 = 0;
    let mut v_fold_3901_: u64 = 0;
    let mut v___x_3902_: u64 = 0;
    let mut v___x_3903_: u64 = 0;
    let mut v___x_3904_: u64 = 0;
    let mut v___x_3905_: usize = 0;
    let mut v___x_3906_: usize = 0;
    let mut v___x_3907_: usize = 0;
    let mut v___x_3908_: usize = 0;
    let mut v___x_3909_: usize = 0;
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3890_) == 0 {
                    return v_x_3889_;
                } else {
                    v_key_3891_ = crate::leanh::lean_ctor_get(v_x_3890_, 0);
                    v_value_3892_ = crate::leanh::lean_ctor_get(v_x_3890_, 1);
                    v_tail_3893_ = crate::leanh::lean_ctor_get(v_x_3890_, 2);
                    v_isSharedCheck_3916_ = (!crate::leanh::lean_is_exclusive(v_x_3890_)) as u8;
                    if v_isSharedCheck_3916_ == 0 {
                        v___x_3895_ = v_x_3890_;
                        v_isShared_3896_ = v_isSharedCheck_3916_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3893_);
                        crate::leanh::lean_inc(v_value_3892_);
                        crate::leanh::lean_inc(v_key_3891_);
                        crate::leanh::lean_dec(v_x_3890_);
                        v___x_3895_ = crate::leanh::lean_box(0);
                        v_isShared_3896_ = v_isSharedCheck_3916_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3897_ = lean_array_get_size(v_x_3889_);
                v___x_3898_ = l_Lean_Expr_hash(v_key_3891_);
                v___x_3899_ = 32u64;
                v___x_3900_ = lean_uint64_shift_right(v___x_3898_, v___x_3899_);
                v_fold_3901_ = lean_uint64_xor(v___x_3898_, v___x_3900_);
                v___x_3902_ = 16u64;
                v___x_3903_ = lean_uint64_shift_right(v_fold_3901_, v___x_3902_);
                v___x_3904_ = lean_uint64_xor(v_fold_3901_, v___x_3903_);
                v___x_3905_ = lean_uint64_to_usize(v___x_3904_);
                v___x_3906_ = lean_usize_of_nat(v___x_3897_);
                v___x_3907_ = 1usize;
                v___x_3908_ = lean_usize_sub(v___x_3906_, v___x_3907_);
                v___x_3909_ = lean_usize_land(v___x_3905_, v___x_3908_);
                v___x_3910_ = lean_array_uget_borrowed(v_x_3889_, v___x_3909_);
                crate::leanh::lean_inc(v___x_3910_);
                if v_isShared_3896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3895_, 2, v___x_3910_);
                    v___x_3912_ = v___x_3895_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3915_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_key_3891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_value_3892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 2, v___x_3910_);
                    v___x_3912_ = v_reuseFailAlloc_3915_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3913_ = lean_array_uset(v_x_3889_, v___x_3909_, v___x_3912_);
                v_x_3889_ = v___x_3913_;
                v_x_3890_ = v_tail_3893_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(
    mut v_i_3917_: *mut crate::leanh::LeanObject,
    mut v_source_3918_: *mut crate::leanh::LeanObject,
    mut v_target_3919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: u8 = 0;
    let mut v_es_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3920_ = lean_array_get_size(v_source_3918_);
                v___x_3921_ = lean_nat_dec_lt(v_i_3917_, v___x_3920_);
                if v___x_3921_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3918_);
                    crate::leanh::lean_dec(v_i_3917_);
                    return v_target_3919_;
                } else {
                    v_es_3922_ = lean_array_fget(v_source_3918_, v_i_3917_);
                    v___x_3923_ = crate::leanh::lean_box(0);
                    v_source_3924_ = lean_array_fset(v_source_3918_, v_i_3917_, v___x_3923_);
                    v_target_3925_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_target_3919_, v_es_3922_);
                    v___x_3926_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3927_ = lean_nat_add(v_i_3917_, v___x_3926_);
                    crate::leanh::lean_dec(v_i_3917_);
                    v_i_3917_ = v___x_3927_;
                    v_source_3918_ = v_source_3924_;
                    v_target_3919_ = v_target_3925_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(
    mut v_data_3929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3930_ = lean_array_get_size(v_data_3929_);
    v___x_3931_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3932_ = lean_nat_mul(v___x_3930_, v___x_3931_);
    v___x_3933_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3934_ = crate::leanh::lean_box(0);
    v___x_3935_ = lean_mk_array(v_nbuckets_3932_, v___x_3934_);
    v___x_3936_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v___x_3933_, v_data_3929_, v___x_3935_);
    return v___x_3936_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(
    mut v_a_3937_: *mut crate::leanh::LeanObject,
    mut v_b_3938_: *mut crate::leanh::LeanObject,
    mut v_x_3939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v___x_3946_: u8 = 0;
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3939_) == 0 {
                    crate::leanh::lean_dec(v_b_3938_);
                    crate::leanh::lean_dec_ref(v_a_3937_);
                    return v_x_3939_;
                } else {
                    v_key_3940_ = crate::leanh::lean_ctor_get(v_x_3939_, 0);
                    v_value_3941_ = crate::leanh::lean_ctor_get(v_x_3939_, 1);
                    v_tail_3942_ = crate::leanh::lean_ctor_get(v_x_3939_, 2);
                    v_isSharedCheck_3954_ = (!crate::leanh::lean_is_exclusive(v_x_3939_)) as u8;
                    if v_isSharedCheck_3954_ == 0 {
                        v___x_3944_ = v_x_3939_;
                        v_isShared_3945_ = v_isSharedCheck_3954_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3942_);
                        crate::leanh::lean_inc(v_value_3941_);
                        crate::leanh::lean_inc(v_key_3940_);
                        crate::leanh::lean_dec(v_x_3939_);
                        v___x_3944_ = crate::leanh::lean_box(0);
                        v_isShared_3945_ = v_isSharedCheck_3954_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3946_ = lean_expr_eqv(v_key_3940_, v_a_3937_);
                if v___x_3946_ == 0 {
                    v___x_3947_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_3937_, v_b_3938_, v_tail_3942_);
                    if v_isShared_3945_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3944_, 2, v___x_3947_);
                        v___x_3949_ = v___x_3944_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3950_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_key_3940_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_value_3941_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3950_, 2, v___x_3947_);
                        v___x_3949_ = v_reuseFailAlloc_3950_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3941_);
                    crate::leanh::lean_dec(v_key_3940_);
                    if v_isShared_3945_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3944_, 1, v_b_3938_);
                        crate::leanh::lean_ctor_set(v___x_3944_, 0, v_a_3937_);
                        v___x_3952_ = v___x_3944_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3953_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3937_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_b_3938_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 2, v_tail_3942_);
                        v___x_3952_ = v_reuseFailAlloc_3953_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3949_;
            }
            3 => {
                return v___x_3952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(
    mut v_m_3955_: *mut crate::leanh::LeanObject,
    mut v_a_3956_: *mut crate::leanh::LeanObject,
    mut v_b_3957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u64 = 0;
    let mut v___x_3965_: u64 = 0;
    let mut v___x_3966_: u64 = 0;
    let mut v_fold_3967_: u64 = 0;
    let mut v___x_3968_: u64 = 0;
    let mut v___x_3969_: u64 = 0;
    let mut v___x_3970_: u64 = 0;
    let mut v___x_3971_: usize = 0;
    let mut v___x_3972_: usize = 0;
    let mut v___x_3973_: usize = 0;
    let mut v___x_3974_: usize = 0;
    let mut v___x_3975_: usize = 0;
    let mut v_bkt_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: u8 = 0;
    let mut v_val_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3958_ = crate::leanh::lean_ctor_get(v_m_3955_, 0);
                v_buckets_3959_ = crate::leanh::lean_ctor_get(v_m_3955_, 1);
                v_isSharedCheck_4002_ = (!crate::leanh::lean_is_exclusive(v_m_3955_)) as u8;
                if v_isSharedCheck_4002_ == 0 {
                    v___x_3961_ = v_m_3955_;
                    v_isShared_3962_ = v_isSharedCheck_4002_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3959_);
                    crate::leanh::lean_inc(v_size_3958_);
                    crate::leanh::lean_dec(v_m_3955_);
                    v___x_3961_ = crate::leanh::lean_box(0);
                    v_isShared_3962_ = v_isSharedCheck_4002_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3963_ = lean_array_get_size(v_buckets_3959_);
                v___x_3964_ = l_Lean_Expr_hash(v_a_3956_);
                v___x_3965_ = 32u64;
                v___x_3966_ = lean_uint64_shift_right(v___x_3964_, v___x_3965_);
                v_fold_3967_ = lean_uint64_xor(v___x_3964_, v___x_3966_);
                v___x_3968_ = 16u64;
                v___x_3969_ = lean_uint64_shift_right(v_fold_3967_, v___x_3968_);
                v___x_3970_ = lean_uint64_xor(v_fold_3967_, v___x_3969_);
                v___x_3971_ = lean_uint64_to_usize(v___x_3970_);
                v___x_3972_ = lean_usize_of_nat(v___x_3963_);
                v___x_3973_ = 1usize;
                v___x_3974_ = lean_usize_sub(v___x_3972_, v___x_3973_);
                v___x_3975_ = lean_usize_land(v___x_3971_, v___x_3974_);
                v_bkt_3976_ = lean_array_uget_borrowed(v_buckets_3959_, v___x_3975_);
                v___x_3977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_3956_, v_bkt_3976_);
                if v___x_3977_ == 0 {
                    v___x_3978_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3979_ = lean_nat_add(v_size_3958_, v___x_3978_);
                    crate::leanh::lean_dec(v_size_3958_);
                    crate::leanh::lean_inc(v_bkt_3976_);
                    v___x_3980_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3980_, 0, v_a_3956_);
                    crate::leanh::lean_ctor_set(v___x_3980_, 1, v_b_3957_);
                    crate::leanh::lean_ctor_set(v___x_3980_, 2, v_bkt_3976_);
                    v_buckets_x27_3981_ =
                        lean_array_uset(v_buckets_3959_, v___x_3975_, v___x_3980_);
                    v___x_3982_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3983_ = lean_nat_mul(v_size_x27_3979_, v___x_3982_);
                    v___x_3984_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3985_ = lean_nat_div(v___x_3983_, v___x_3984_);
                    crate::leanh::lean_dec(v___x_3983_);
                    v___x_3986_ = lean_array_get_size(v_buckets_x27_3981_);
                    v___x_3987_ = lean_nat_dec_le(v___x_3985_, v___x_3986_);
                    crate::leanh::lean_dec(v___x_3985_);
                    if v___x_3987_ == 0 {
                        v_val_3988_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_3981_);
                        if v_isShared_3962_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3961_, 1, v_val_3988_);
                            crate::leanh::lean_ctor_set(v___x_3961_, 0, v_size_x27_3979_);
                            v___x_3990_ = v___x_3961_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3991_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3991_,
                                0,
                                v_size_x27_3979_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3991_, 1, v_val_3988_);
                            v___x_3990_ = v_reuseFailAlloc_3991_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3962_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3961_, 1, v_buckets_x27_3981_);
                            crate::leanh::lean_ctor_set(v___x_3961_, 0, v_size_x27_3979_);
                            v___x_3993_ = v___x_3961_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3994_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3994_,
                                0,
                                v_size_x27_3979_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3994_,
                                1,
                                v_buckets_x27_3981_,
                            );
                            v___x_3993_ = v_reuseFailAlloc_3994_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3976_);
                    v___x_3995_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3996_ =
                        lean_array_uset(v_buckets_3959_, v___x_3975_, v___x_3995_);
                    v___x_3997_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_3956_, v_b_3957_, v_bkt_3976_);
                    v___x_3998_ = lean_array_uset(v_buckets_x27_3996_, v___x_3975_, v___x_3997_);
                    if v_isShared_3962_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3961_, 1, v___x_3998_);
                        v___x_4000_ = v___x_3961_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4001_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_size_3958_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4001_, 1, v___x_3998_);
                        v___x_4000_ = v_reuseFailAlloc_4001_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3990_;
            }
            3 => {
                return v___x_3993_;
            }
            4 => {
                return v___x_4000_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(
    mut v_as_4003_: *mut crate::leanh::LeanObject,
    mut v_sz_4004_: usize,
    mut v_i_4005_: usize,
    mut v_b_4006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4008_: u8 = 0;
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v_array_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: u8 = 0;
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4025_: u8 = 0;
    let mut v_a_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: usize = 0;
    let mut v___x_4036_: usize = 0;
    let mut v_reuseFailAlloc_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4040_: u8 = 0;
    let mut v_unused_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4008_ = lean_usize_dec_lt(v_i_4005_, v_sz_4004_);
                if v___x_4008_ == 0 {
                    v___x_4009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4009_, 0, v_b_4006_);
                    return v___x_4009_;
                } else {
                    v_snd_4010_ = crate::leanh::lean_ctor_get(v_b_4006_, 1);
                    v_fst_4011_ = crate::leanh::lean_ctor_get(v_b_4006_, 0);
                    v_isSharedCheck_4044_ = (!crate::leanh::lean_is_exclusive(v_b_4006_)) as u8;
                    if v_isSharedCheck_4044_ == 0 {
                        v___x_4013_ = v_b_4006_;
                        v_isShared_4014_ = v_isSharedCheck_4044_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4010_);
                        crate::leanh::lean_inc(v_fst_4011_);
                        crate::leanh::lean_dec(v_b_4006_);
                        v___x_4013_ = crate::leanh::lean_box(0);
                        v_isShared_4014_ = v_isSharedCheck_4044_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_4015_ = crate::leanh::lean_ctor_get(v_snd_4010_, 0);
                v_start_4016_ = crate::leanh::lean_ctor_get(v_snd_4010_, 1);
                v_stop_4017_ = crate::leanh::lean_ctor_get(v_snd_4010_, 2);
                v___x_4018_ = lean_nat_dec_lt(v_start_4016_, v_stop_4017_);
                if v___x_4018_ == 0 {
                    if v_isShared_4014_ == 0 {
                        v___x_4020_ = v___x_4013_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4022_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_fst_4011_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4022_, 1, v_snd_4010_);
                        v___x_4020_ = v_reuseFailAlloc_4022_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_4017_);
                    crate::leanh::lean_inc(v_start_4016_);
                    crate::leanh::lean_inc_ref(v_array_4015_);
                    v_isSharedCheck_4040_ = (!crate::leanh::lean_is_exclusive(v_snd_4010_)) as u8;
                    if v_isSharedCheck_4040_ == 0 {
                        v_unused_4041_ = crate::leanh::lean_ctor_get(v_snd_4010_, 2);
                        crate::leanh::lean_dec(v_unused_4041_);
                        v_unused_4042_ = crate::leanh::lean_ctor_get(v_snd_4010_, 1);
                        crate::leanh::lean_dec(v_unused_4042_);
                        v_unused_4043_ = crate::leanh::lean_ctor_get(v_snd_4010_, 0);
                        crate::leanh::lean_dec(v_unused_4043_);
                        v___x_4024_ = v_snd_4010_;
                        v_isShared_4025_ = v_isSharedCheck_4040_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_4010_);
                        v___x_4024_ = crate::leanh::lean_box(0);
                        v_isShared_4025_ = v_isSharedCheck_4040_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4021_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4021_, 0, v___x_4020_);
                return v___x_4021_;
            }
            3 => {
                v_a_4026_ = lean_array_uget_borrowed(v_as_4003_, v_i_4005_);
                v___x_4027_ = lean_array_fget(v_array_4015_, v_start_4016_);
                v___x_4028_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4029_ = lean_nat_add(v_start_4016_, v___x_4028_);
                crate::leanh::lean_dec(v_start_4016_);
                if v_isShared_4025_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4024_, 1, v___x_4029_);
                    v___x_4031_ = v___x_4024_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4039_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_array_4015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4039_, 1, v___x_4029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4039_, 2, v_stop_4017_);
                    v___x_4031_ = v_reuseFailAlloc_4039_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_4026_);
                v___x_4032_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_fst_4011_, v_a_4026_, v___x_4027_);
                if v_isShared_4014_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4013_, 1, v___x_4031_);
                    crate::leanh::lean_ctor_set(v___x_4013_, 0, v___x_4032_);
                    v___x_4034_ = v___x_4013_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4038_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4038_, 1, v___x_4031_);
                    v___x_4034_ = v_reuseFailAlloc_4038_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4035_ = 1usize;
                v___x_4036_ = lean_usize_add(v_i_4005_, v___x_4035_);
                v_i_4005_ = v___x_4036_;
                v_b_4006_ = v___x_4034_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg___boxed(
    mut v_as_4045_: *mut crate::leanh::LeanObject,
    mut v_sz_4046_: *mut crate::leanh::LeanObject,
    mut v_i_4047_: *mut crate::leanh::LeanObject,
    mut v_b_4048_: *mut crate::leanh::LeanObject,
    mut v___y_4049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4050_: usize = 0;
    let mut v_i_boxed_4051_: usize = 0;
    let mut v_res_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4050_ = crate::leanh::lean_unbox_usize(v_sz_4046_);
    crate::leanh::lean_dec(v_sz_4046_);
    v_i_boxed_4051_ = crate::leanh::lean_unbox_usize(v_i_4047_);
    crate::leanh::lean_dec(v_i_4047_);
    v_res_4052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_4045_, v_sz_boxed_4050_, v_i_boxed_4051_, v_b_4048_);
    crate::leanh::lean_dec_ref(v_as_4045_);
    return v_res_4052_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1(
    mut v___x_4053_: *mut crate::leanh::LeanObject,
    mut v___x_4054_: *mut crate::leanh::LeanObject,
    mut v_z_4055_: *mut crate::leanh::LeanObject,
    mut v___y_4056_: *mut crate::leanh::LeanObject,
    mut v___x_4057_: usize,
    mut v_a_4058_: *mut crate::leanh::LeanObject,
    mut v___x_4059_: u8,
    mut v_args_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
    mut v___y_4062_: *mut crate::leanh::LeanObject,
    mut v___y_4063_: *mut crate::leanh::LeanObject,
    mut v___y_4064_: *mut crate::leanh::LeanObject,
    mut v___y_4065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4083_: usize = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4095_: u8 = 0;
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4067_ = lean_array_get_size(v_args_4060_);
                v___x_4068_ = lean_nat_add(v___x_4067_, v___x_4053_);
                v___x_4069_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4070_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_4071_ = lean_nat_mul(v___x_4068_, v___x_4070_);
                crate::leanh::lean_dec(v___x_4068_);
                v___x_4072_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4073_ = lean_nat_div(v___x_4071_, v___x_4072_);
                crate::leanh::lean_dec(v___x_4071_);
                v___x_4074_ = l_Nat_nextPowerOfTwo(v___x_4073_);
                crate::leanh::lean_dec(v___x_4073_);
                v___x_4075_ = crate::leanh::lean_box(0);
                v___x_4076_ = lean_mk_array(v___x_4074_, v___x_4075_);
                v___x_4077_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4077_, 0, v___x_4069_);
                crate::leanh::lean_ctor_set(v___x_4077_, 1, v___x_4076_);
                v___x_4078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6;
                v___x_4079_ = l_Lean_mkConst(v___x_4078_, v___x_4054_);
                v___x_4080_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v___x_4077_, v___x_4079_, v_z_4055_);
                crate::leanh::lean_inc_ref(v_args_4060_);
                v___x_4081_ = l_Array_toSubarray___redArg(v_args_4060_, v___x_4069_, v___x_4067_);
                v___x_4082_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4082_, 0, v___x_4080_);
                crate::leanh::lean_ctor_set(v___x_4082_, 1, v___x_4081_);
                v_sz_4083_ = lean_array_size(v___y_4056_);
                v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v___y_4056_, v_sz_4083_, v___x_4057_, v___x_4082_);
                if crate::leanh::lean_obj_tag(v___x_4084_) == 0 {
                    v_a_4085_ = crate::leanh::lean_ctor_get(v___x_4084_, 0);
                    crate::leanh::lean_inc(v_a_4085_);
                    crate::leanh::lean_dec_ref_known(v___x_4084_, 1);
                    v_fst_4086_ = crate::leanh::lean_ctor_get(v_a_4085_, 0);
                    crate::leanh::lean_inc(v_fst_4086_);
                    crate::leanh::lean_dec(v_a_4085_);
                    v___f_4087_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_4087_, 0, v_fst_4086_);
                    v___x_4088_ = lean_replace_expr(v___f_4087_, v_a_4058_);
                    crate::leanh::lean_dec_ref(v___f_4087_);
                    v___x_4089_ = 0;
                    v___x_4090_ = 1;
                    v___x_4091_ = l_Lean_Meta_mkForallFVars(
                        v_args_4060_,
                        v___x_4088_,
                        v___x_4089_,
                        v___x_4059_,
                        v___x_4059_,
                        v___x_4090_,
                        v___y_4062_,
                        v___y_4063_,
                        v___y_4064_,
                        v___y_4065_,
                    );
                    crate::leanh::lean_dec_ref(v_args_4060_);
                    return v___x_4091_;
                } else {
                    crate::leanh::lean_dec_ref(v_args_4060_);
                    v_a_4092_ = crate::leanh::lean_ctor_get(v___x_4084_, 0);
                    v_isSharedCheck_4099_ = (!crate::leanh::lean_is_exclusive(v___x_4084_)) as u8;
                    if v_isSharedCheck_4099_ == 0 {
                        v___x_4094_ = v___x_4084_;
                        v_isShared_4095_ = v_isSharedCheck_4099_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4092_);
                        crate::leanh::lean_dec(v___x_4084_);
                        v___x_4094_ = crate::leanh::lean_box(0);
                        v_isShared_4095_ = v_isSharedCheck_4099_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4095_ == 0 {
                    v___x_4097_ = v___x_4094_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
                    v___x_4097_ = v_reuseFailAlloc_4098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1___boxed(
    mut v___x_4100_: *mut crate::leanh::LeanObject,
    mut v___x_4101_: *mut crate::leanh::LeanObject,
    mut v_z_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
    mut v___x_4104_: *mut crate::leanh::LeanObject,
    mut v_a_4105_: *mut crate::leanh::LeanObject,
    mut v___x_4106_: *mut crate::leanh::LeanObject,
    mut v_args_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_21195__boxed_4114_: usize = 0;
    let mut v___x_21197__boxed_4115_: u8 = 0;
    let mut v_res_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_21195__boxed_4114_ = crate::leanh::lean_unbox_usize(v___x_4104_);
    crate::leanh::lean_dec(v___x_4104_);
    v___x_21197__boxed_4115_ = (crate::leanh::lean_unbox(v___x_4106_) as u8);
    v_res_4116_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1(v___x_4100_, v___x_4101_, v_z_4102_, v___y_4103_, v___x_21195__boxed_4114_, v_a_4105_, v___x_21197__boxed_4115_, v_args_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
    crate::leanh::lean_dec(v___y_4112_);
    crate::leanh::lean_dec_ref(v___y_4111_);
    crate::leanh::lean_dec(v___y_4110_);
    crate::leanh::lean_dec_ref(v___y_4109_);
    crate::leanh::lean_dec(v___y_4108_);
    crate::leanh::lean_dec_ref(v_a_4105_);
    crate::leanh::lean_dec_ref(v___y_4103_);
    crate::leanh::lean_dec(v___x_4100_);
    return v_res_4116_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(
    mut v_sz_4117_: usize,
    mut v_i_4118_: usize,
    mut v_bs_4119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4120_: u8 = 0;
    let mut v_v_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4126_: u8 = 0;
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: u8 = 0;
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: usize = 0;
    let mut v___x_4135_: usize = 0;
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4120_ = lean_usize_dec_lt(v_i_4118_, v_sz_4117_);
                if v___x_4120_ == 0 {
                    return v_bs_4119_;
                } else {
                    v_v_4121_ = lean_array_uget(v_bs_4119_, v_i_4118_);
                    v_fst_4122_ = crate::leanh::lean_ctor_get(v_v_4121_, 0);
                    v_snd_4123_ = crate::leanh::lean_ctor_get(v_v_4121_, 1);
                    v_isSharedCheck_4139_ = (!crate::leanh::lean_is_exclusive(v_v_4121_)) as u8;
                    if v_isSharedCheck_4139_ == 0 {
                        v___x_4125_ = v_v_4121_;
                        v_isShared_4126_ = v_isSharedCheck_4139_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4123_);
                        crate::leanh::lean_inc(v_fst_4122_);
                        crate::leanh::lean_dec(v_v_4121_);
                        v___x_4125_ = crate::leanh::lean_box(0);
                        v_isShared_4126_ = v_isSharedCheck_4139_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4127_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_4128_ = lean_array_uset(v_bs_4119_, v_i_4118_, v___x_4127_);
                v___x_4129_ = 0;
                v___x_4130_ = crate::leanh::lean_box((v___x_4129_) as usize);
                if v_isShared_4126_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4125_, 0, v___x_4130_);
                    v___x_4132_ = v___x_4125_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4138_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4130_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4138_, 1, v_snd_4123_);
                    v___x_4132_ = v_reuseFailAlloc_4138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4133_, 0, v_fst_4122_);
                crate::leanh::lean_ctor_set(v___x_4133_, 1, v___x_4132_);
                v___x_4134_ = 1usize;
                v___x_4135_ = lean_usize_add(v_i_4118_, v___x_4134_);
                v___x_4136_ = lean_array_uset(v_bs_x27_4128_, v_i_4118_, v___x_4133_);
                v_i_4118_ = v___x_4135_;
                v_bs_4119_ = v___x_4136_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13___boxed(
    mut v_sz_4140_: *mut crate::leanh::LeanObject,
    mut v_i_4141_: *mut crate::leanh::LeanObject,
    mut v_bs_4142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4143_: usize = 0;
    let mut v_i_boxed_4144_: usize = 0;
    let mut v_res_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4143_ = crate::leanh::lean_unbox_usize(v_sz_4140_);
    crate::leanh::lean_dec(v_sz_4140_);
    v_i_boxed_4144_ = crate::leanh::lean_unbox_usize(v_i_4141_);
    crate::leanh::lean_dec(v_i_4141_);
    v_res_4145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_boxed_4143_, v_i_boxed_4144_, v_bs_4142_);
    return v_res_4145_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0(
    mut v___x_4146_: *mut crate::leanh::LeanObject,
    mut v_a_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
    mut v___y_4150_: *mut crate::leanh::LeanObject,
    mut v___y_4151_: *mut crate::leanh::LeanObject,
    mut v___y_4152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_20783__overap_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4154_ = l_Lean_instInhabitedExpr;
    v___x_20783__overap_4155_ = l_instInhabitedOfMonad___redArg(v___x_4146_, v___x_4154_);
    crate::leanh::lean_inc(v___y_4152_);
    crate::leanh::lean_inc_ref(v___y_4151_);
    crate::leanh::lean_inc(v___y_4150_);
    crate::leanh::lean_inc_ref(v___y_4149_);
    crate::leanh::lean_inc(v___y_4148_);
    v___x_4156_ = crate::leanh::lean_apply_6(
        v___x_20783__overap_4155_,
        v___y_4148_,
        v___y_4149_,
        v___y_4150_,
        v___y_4151_,
        v___y_4152_,
        crate::leanh::lean_box(0),
    );
    return v___x_4156_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0___boxed(
    mut v___x_4157_: *mut crate::leanh::LeanObject,
    mut v_a_4158_: *mut crate::leanh::LeanObject,
    mut v___y_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4165_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0(v___x_4157_, v_a_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
    crate::leanh::lean_dec(v___y_4163_);
    crate::leanh::lean_dec_ref(v___y_4162_);
    crate::leanh::lean_dec(v___y_4161_);
    crate::leanh::lean_dec_ref(v___y_4160_);
    crate::leanh::lean_dec(v___y_4159_);
    crate::leanh::lean_dec_ref(v_a_4158_);
    return v_res_4165_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4166_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_4166_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4167_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0);
    v___x_4168_ = l_StateRefT_x27_instMonad___redArg(v___x_4167_);
    return v___x_4168_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0___boxed(
    mut v_acc_4173_: *mut crate::leanh::LeanObject,
    mut v_declInfos_4174_: *mut crate::leanh::LeanObject,
    mut v_k_4175_: *mut crate::leanh::LeanObject,
    mut v_kind_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v_b_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4184_: u8 = 0;
    let mut v_res_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4184_ = (crate::leanh::lean_unbox(v_kind_4176_) as u8);
    v_res_4185_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0(v_acc_4173_, v_declInfos_4174_, v_k_4175_, v_kind_boxed_4184_, v___y_4177_, v_b_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
    crate::leanh::lean_dec(v___y_4182_);
    crate::leanh::lean_dec_ref(v___y_4181_);
    crate::leanh::lean_dec(v___y_4180_);
    crate::leanh::lean_dec_ref(v___y_4179_);
    crate::leanh::lean_dec(v___y_4177_);
    return v_res_4185_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(
    mut v_acc_4186_: *mut crate::leanh::LeanObject,
    mut v_declInfos_4187_: *mut crate::leanh::LeanObject,
    mut v_k_4188_: *mut crate::leanh::LeanObject,
    mut v_kind_4189_: u8,
    mut v_name_4190_: *mut crate::leanh::LeanObject,
    mut v_bi_4191_: u8,
    mut v_type_4192_: *mut crate::leanh::LeanObject,
    mut v_kind_4193_: u8,
    mut v___y_4194_: *mut crate::leanh::LeanObject,
    mut v___y_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4200_ = crate::leanh::lean_box((v_kind_4189_) as usize);
                crate::leanh::lean_inc(v___y_4194_);
                v___f_4201_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                crate::leanh::lean_closure_set(v___f_4201_, 0, v_acc_4186_);
                crate::leanh::lean_closure_set(v___f_4201_, 1, v_declInfos_4187_);
                crate::leanh::lean_closure_set(v___f_4201_, 2, v_k_4188_);
                crate::leanh::lean_closure_set(v___f_4201_, 3, v___x_4200_);
                crate::leanh::lean_closure_set(v___f_4201_, 4, v___y_4194_);
                v___x_4202_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_4190_,
                    v_bi_4191_,
                    v_type_4192_,
                    v___f_4201_,
                    v_kind_4193_,
                    v___y_4195_,
                    v___y_4196_,
                    v___y_4197_,
                    v___y_4198_,
                );
                if crate::leanh::lean_obj_tag(v___x_4202_) == 0 {
                    return v___x_4202_;
                } else {
                    v_a_4203_ = crate::leanh::lean_ctor_get(v___x_4202_, 0);
                    v_isSharedCheck_4210_ = (!crate::leanh::lean_is_exclusive(v___x_4202_)) as u8;
                    if v_isSharedCheck_4210_ == 0 {
                        v___x_4205_ = v___x_4202_;
                        v_isShared_4206_ = v_isSharedCheck_4210_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4203_);
                        crate::leanh::lean_dec(v___x_4202_);
                        v___x_4205_ = crate::leanh::lean_box(0);
                        v_isShared_4206_ = v_isSharedCheck_4210_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4206_ == 0 {
                    v___x_4208_ = v___x_4205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4209_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
                    v___x_4208_ = v_reuseFailAlloc_4209_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(
    mut v_declInfos_4211_: *mut crate::leanh::LeanObject,
    mut v_k_4212_: *mut crate::leanh::LeanObject,
    mut v_kind_4213_: u8,
    mut v_acc_4214_: *mut crate::leanh::LeanObject,
    mut v___y_4215_: *mut crate::leanh::LeanObject,
    mut v___y_4216_: *mut crate::leanh::LeanObject,
    mut v___y_4217_: *mut crate::leanh::LeanObject,
    mut v___y_4218_: *mut crate::leanh::LeanObject,
    mut v___y_4219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4241_: u8 = 0;
    let mut v_toFunctor_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___f_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: u8 = 0;
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    let mut v___f_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4284_: u8 = 0;
    let mut v_unused_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4286_: u8 = 0;
    let mut v_unused_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4221_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1);
                v_toApplicative_4222_ = crate::leanh::lean_ctor_get(v___x_4221_, 0);
                v_toFunctor_4223_ = crate::leanh::lean_ctor_get(v_toApplicative_4222_, 0);
                v_toSeq_4224_ = crate::leanh::lean_ctor_get(v_toApplicative_4222_, 2);
                v_toSeqLeft_4225_ = crate::leanh::lean_ctor_get(v_toApplicative_4222_, 3);
                v_toSeqRight_4226_ = crate::leanh::lean_ctor_get(v_toApplicative_4222_, 4);
                v___f_4227_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2;
                v___f_4228_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_4223_, 2);
                v___f_4229_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4229_, 0, v_toFunctor_4223_);
                v___f_4230_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4230_, 0, v_toFunctor_4223_);
                v___x_4231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4231_, 0, v___f_4229_);
                crate::leanh::lean_ctor_set(v___x_4231_, 1, v___f_4230_);
                crate::leanh::lean_inc(v_toSeqRight_4226_);
                v___f_4232_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4232_, 0, v_toSeqRight_4226_);
                crate::leanh::lean_inc(v_toSeqLeft_4225_);
                v___f_4233_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4233_, 0, v_toSeqLeft_4225_);
                crate::leanh::lean_inc(v_toSeq_4224_);
                v___f_4234_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4234_, 0, v_toSeq_4224_);
                v___x_4235_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4235_, 0, v___x_4231_);
                crate::leanh::lean_ctor_set(v___x_4235_, 1, v___f_4227_);
                crate::leanh::lean_ctor_set(v___x_4235_, 2, v___f_4234_);
                crate::leanh::lean_ctor_set(v___x_4235_, 3, v___f_4233_);
                crate::leanh::lean_ctor_set(v___x_4235_, 4, v___f_4232_);
                v___x_4236_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4236_, 0, v___x_4235_);
                crate::leanh::lean_ctor_set(v___x_4236_, 1, v___f_4228_);
                v___x_4237_ = l_StateRefT_x27_instMonad___redArg(v___x_4236_);
                v_toApplicative_4238_ = crate::leanh::lean_ctor_get(v___x_4237_, 0);
                v_isSharedCheck_4286_ = (!crate::leanh::lean_is_exclusive(v___x_4237_)) as u8;
                if v_isSharedCheck_4286_ == 0 {
                    v_unused_4287_ = crate::leanh::lean_ctor_get(v___x_4237_, 1);
                    crate::leanh::lean_dec(v_unused_4287_);
                    v___x_4240_ = v___x_4237_;
                    v_isShared_4241_ = v_isSharedCheck_4286_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_4238_);
                    crate::leanh::lean_dec(v___x_4237_);
                    v___x_4240_ = crate::leanh::lean_box(0);
                    v_isShared_4241_ = v_isSharedCheck_4286_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4242_ = crate::leanh::lean_ctor_get(v_toApplicative_4238_, 0);
                v_toSeq_4243_ = crate::leanh::lean_ctor_get(v_toApplicative_4238_, 2);
                v_toSeqLeft_4244_ = crate::leanh::lean_ctor_get(v_toApplicative_4238_, 3);
                v_toSeqRight_4245_ = crate::leanh::lean_ctor_get(v_toApplicative_4238_, 4);
                v_isSharedCheck_4284_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_4238_)) as u8;
                if v_isSharedCheck_4284_ == 0 {
                    v_unused_4285_ = crate::leanh::lean_ctor_get(v_toApplicative_4238_, 1);
                    crate::leanh::lean_dec(v_unused_4285_);
                    v___x_4247_ = v_toApplicative_4238_;
                    v_isShared_4248_ = v_isSharedCheck_4284_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_4245_);
                    crate::leanh::lean_inc(v_toSeqLeft_4244_);
                    crate::leanh::lean_inc(v_toSeq_4243_);
                    crate::leanh::lean_inc(v_toFunctor_4242_);
                    crate::leanh::lean_dec(v_toApplicative_4238_);
                    v___x_4247_ = crate::leanh::lean_box(0);
                    v_isShared_4248_ = v_isSharedCheck_4284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4249_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4;
                v___f_4250_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_4242_);
                v___f_4251_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4251_, 0, v_toFunctor_4242_);
                v___f_4252_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4252_, 0, v_toFunctor_4242_);
                v___x_4253_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4253_, 0, v___f_4251_);
                crate::leanh::lean_ctor_set(v___x_4253_, 1, v___f_4252_);
                v___f_4254_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4254_, 0, v_toSeqRight_4245_);
                v___f_4255_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4255_, 0, v_toSeqLeft_4244_);
                v___f_4256_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4256_, 0, v_toSeq_4243_);
                if v_isShared_4248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4247_, 4, v___f_4254_);
                    crate::leanh::lean_ctor_set(v___x_4247_, 3, v___f_4255_);
                    crate::leanh::lean_ctor_set(v___x_4247_, 2, v___f_4256_);
                    crate::leanh::lean_ctor_set(v___x_4247_, 1, v___f_4249_);
                    crate::leanh::lean_ctor_set(v___x_4247_, 0, v___x_4253_);
                    v___x_4258_ = v___x_4247_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4283_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4283_, 1, v___f_4249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4283_, 2, v___f_4256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4283_, 3, v___f_4255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4283_, 4, v___f_4254_);
                    v___x_4258_ = v_reuseFailAlloc_4283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4240_, 1, v___f_4250_);
                    crate::leanh::lean_ctor_set(v___x_4240_, 0, v___x_4258_);
                    v___x_4260_ = v___x_4240_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4282_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4258_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 1, v___f_4250_);
                    v___x_4260_ = v_reuseFailAlloc_4282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4261_ = l_StateRefT_x27_instMonad___redArg(v___x_4260_);
                v___x_4262_ = lean_array_get_size(v_acc_4214_);
                v___x_4263_ = lean_array_get_size(v_declInfos_4211_);
                v___x_4264_ = lean_nat_dec_lt(v___x_4262_, v___x_4263_);
                if v___x_4264_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4261_);
                    crate::leanh::lean_dec_ref(v_declInfos_4211_);
                    crate::leanh::lean_inc(v___y_4219_);
                    crate::leanh::lean_inc_ref(v___y_4218_);
                    crate::leanh::lean_inc(v___y_4217_);
                    crate::leanh::lean_inc_ref(v___y_4216_);
                    crate::leanh::lean_inc(v___y_4215_);
                    v___x_4265_ = crate::leanh::lean_apply_7(
                        v_k_4212_,
                        v_acc_4214_,
                        v___y_4215_,
                        v___y_4216_,
                        v___y_4217_,
                        v___y_4218_,
                        v___y_4219_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4265_;
                } else {
                    v___f_4266_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    crate::leanh::lean_closure_set(v___f_4266_, 0, v___x_4261_);
                    v___x_4267_ = crate::leanh::lean_box(0);
                    v___x_4268_ = 0;
                    v___f_4269_ = crate::leanh::lean_alloc_closure(
                        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4269_, 0, v___f_4266_);
                    v___x_4270_ = crate::leanh::lean_box((v___x_4268_) as usize);
                    v___x_4271_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4271_, 0, v___x_4270_);
                    crate::leanh::lean_ctor_set(v___x_4271_, 1, v___f_4269_);
                    v___x_4272_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4272_, 0, v___x_4267_);
                    crate::leanh::lean_ctor_set(v___x_4272_, 1, v___x_4271_);
                    v___x_4273_ = lean_array_get(v___x_4272_, v_declInfos_4211_, v___x_4262_);
                    crate::leanh::lean_dec_ref_known(v___x_4272_, 2);
                    v_snd_4274_ = crate::leanh::lean_ctor_get(v___x_4273_, 1);
                    crate::leanh::lean_inc(v_snd_4274_);
                    v_fst_4275_ = crate::leanh::lean_ctor_get(v___x_4273_, 0);
                    crate::leanh::lean_inc(v_fst_4275_);
                    crate::leanh::lean_dec(v___x_4273_);
                    v_fst_4276_ = crate::leanh::lean_ctor_get(v_snd_4274_, 0);
                    crate::leanh::lean_inc(v_fst_4276_);
                    v_snd_4277_ = crate::leanh::lean_ctor_get(v_snd_4274_, 1);
                    crate::leanh::lean_inc(v_snd_4277_);
                    crate::leanh::lean_dec(v_snd_4274_);
                    crate::leanh::lean_inc(v___y_4219_);
                    crate::leanh::lean_inc_ref(v___y_4218_);
                    crate::leanh::lean_inc(v___y_4217_);
                    crate::leanh::lean_inc_ref(v___y_4216_);
                    crate::leanh::lean_inc(v___y_4215_);
                    crate::leanh::lean_inc_ref(v_acc_4214_);
                    v___x_4278_ = crate::leanh::lean_apply_7(
                        v_snd_4277_,
                        v_acc_4214_,
                        v___y_4215_,
                        v___y_4216_,
                        v___y_4217_,
                        v___y_4218_,
                        v___y_4219_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4278_) == 0 {
                        v_a_4279_ = crate::leanh::lean_ctor_get(v___x_4278_, 0);
                        crate::leanh::lean_inc(v_a_4279_);
                        crate::leanh::lean_dec_ref_known(v___x_4278_, 1);
                        v___x_4280_ = (crate::leanh::lean_unbox(v_fst_4276_) as u8);
                        crate::leanh::lean_dec(v_fst_4276_);
                        v___x_4281_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(v_acc_4214_, v_declInfos_4211_, v_k_4212_, v_kind_4213_, v_fst_4275_, v___x_4280_, v_a_4279_, v_kind_4213_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
                        return v___x_4281_;
                    } else {
                        crate::leanh::lean_dec(v_fst_4276_);
                        crate::leanh::lean_dec(v_fst_4275_);
                        crate::leanh::lean_dec_ref(v_acc_4214_);
                        crate::leanh::lean_dec_ref(v_k_4212_);
                        crate::leanh::lean_dec_ref(v_declInfos_4211_);
                        return v___x_4278_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0(
    mut v_acc_4288_: *mut crate::leanh::LeanObject,
    mut v_declInfos_4289_: *mut crate::leanh::LeanObject,
    mut v_k_4290_: *mut crate::leanh::LeanObject,
    mut v_kind_4291_: u8,
    mut v___y_4292_: *mut crate::leanh::LeanObject,
    mut v_b_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
    mut v___y_4296_: *mut crate::leanh::LeanObject,
    mut v___y_4297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4299_ = lean_array_push(v_acc_4288_, v_b_4293_);
    v___x_4300_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_4289_, v_k_4290_, v_kind_4291_, v___x_4299_, v___y_4292_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
    return v___x_4300_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___boxed(
    mut v_acc_4301_: *mut crate::leanh::LeanObject,
    mut v_declInfos_4302_: *mut crate::leanh::LeanObject,
    mut v_k_4303_: *mut crate::leanh::LeanObject,
    mut v_kind_4304_: *mut crate::leanh::LeanObject,
    mut v_name_4305_: *mut crate::leanh::LeanObject,
    mut v_bi_4306_: *mut crate::leanh::LeanObject,
    mut v_type_4307_: *mut crate::leanh::LeanObject,
    mut v_kind_4308_: *mut crate::leanh::LeanObject,
    mut v___y_4309_: *mut crate::leanh::LeanObject,
    mut v___y_4310_: *mut crate::leanh::LeanObject,
    mut v___y_4311_: *mut crate::leanh::LeanObject,
    mut v___y_4312_: *mut crate::leanh::LeanObject,
    mut v___y_4313_: *mut crate::leanh::LeanObject,
    mut v___y_4314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4315_: u8 = 0;
    let mut v_bi_boxed_4316_: u8 = 0;
    let mut v_kind_boxed_4317_: u8 = 0;
    let mut v_res_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4315_ = (crate::leanh::lean_unbox(v_kind_4304_) as u8);
    v_bi_boxed_4316_ = (crate::leanh::lean_unbox(v_bi_4306_) as u8);
    v_kind_boxed_4317_ = (crate::leanh::lean_unbox(v_kind_4308_) as u8);
    v_res_4318_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(v_acc_4301_, v_declInfos_4302_, v_k_4303_, v_kind_boxed_4315_, v_name_4305_, v_bi_boxed_4316_, v_type_4307_, v_kind_boxed_4317_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
    crate::leanh::lean_dec(v___y_4313_);
    crate::leanh::lean_dec_ref(v___y_4312_);
    crate::leanh::lean_dec(v___y_4311_);
    crate::leanh::lean_dec_ref(v___y_4310_);
    crate::leanh::lean_dec(v___y_4309_);
    return v_res_4318_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___boxed(
    mut v_declInfos_4319_: *mut crate::leanh::LeanObject,
    mut v_k_4320_: *mut crate::leanh::LeanObject,
    mut v_kind_4321_: *mut crate::leanh::LeanObject,
    mut v_acc_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
    mut v___y_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
    mut v___y_4326_: *mut crate::leanh::LeanObject,
    mut v___y_4327_: *mut crate::leanh::LeanObject,
    mut v___y_4328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4329_: u8 = 0;
    let mut v_res_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4329_ = (crate::leanh::lean_unbox(v_kind_4321_) as u8);
    v_res_4330_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_4319_, v_k_4320_, v_kind_boxed_4329_, v_acc_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
    crate::leanh::lean_dec(v___y_4327_);
    crate::leanh::lean_dec_ref(v___y_4326_);
    crate::leanh::lean_dec(v___y_4325_);
    crate::leanh::lean_dec_ref(v___y_4324_);
    crate::leanh::lean_dec(v___y_4323_);
    return v_res_4330_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(
    mut v_declInfos_4333_: *mut crate::leanh::LeanObject,
    mut v_k_4334_: *mut crate::leanh::LeanObject,
    mut v_kind_4335_: u8,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4342_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0;
    v___x_4343_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_4333_, v_k_4334_, v_kind_4335_, v___x_4342_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
    return v___x_4343_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___boxed(
    mut v_declInfos_4344_: *mut crate::leanh::LeanObject,
    mut v_k_4345_: *mut crate::leanh::LeanObject,
    mut v_kind_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
    mut v___y_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
    mut v___y_4350_: *mut crate::leanh::LeanObject,
    mut v___y_4351_: *mut crate::leanh::LeanObject,
    mut v___y_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4353_: u8 = 0;
    let mut v_res_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4353_ = (crate::leanh::lean_unbox(v_kind_4346_) as u8);
    v_res_4354_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(v_declInfos_4344_, v_k_4345_, v_kind_boxed_4353_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
    crate::leanh::lean_dec(v___y_4351_);
    crate::leanh::lean_dec_ref(v___y_4350_);
    crate::leanh::lean_dec(v___y_4349_);
    crate::leanh::lean_dec_ref(v___y_4348_);
    crate::leanh::lean_dec(v___y_4347_);
    return v_res_4354_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(
    mut v_declInfos_4355_: *mut crate::leanh::LeanObject,
    mut v_k_4356_: *mut crate::leanh::LeanObject,
    mut v_kind_4357_: u8,
    mut v___y_4358_: *mut crate::leanh::LeanObject,
    mut v___y_4359_: *mut crate::leanh::LeanObject,
    mut v___y_4360_: *mut crate::leanh::LeanObject,
    mut v___y_4361_: *mut crate::leanh::LeanObject,
    mut v___y_4362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4364_: usize = 0;
    let mut v___x_4365_: usize = 0;
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4364_ = lean_array_size(v_declInfos_4355_);
    v___x_4365_ = 0usize;
    v___x_4366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_4364_, v___x_4365_, v_declInfos_4355_);
    v___x_4367_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(v___x_4366_, v_k_4356_, v_kind_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
    return v___x_4367_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___boxed(
    mut v_declInfos_4368_: *mut crate::leanh::LeanObject,
    mut v_k_4369_: *mut crate::leanh::LeanObject,
    mut v_kind_4370_: *mut crate::leanh::LeanObject,
    mut v___y_4371_: *mut crate::leanh::LeanObject,
    mut v___y_4372_: *mut crate::leanh::LeanObject,
    mut v___y_4373_: *mut crate::leanh::LeanObject,
    mut v___y_4374_: *mut crate::leanh::LeanObject,
    mut v___y_4375_: *mut crate::leanh::LeanObject,
    mut v___y_4376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4377_: u8 = 0;
    let mut v_res_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4377_ = (crate::leanh::lean_unbox(v_kind_4370_) as u8);
    v_res_4378_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(v_declInfos_4368_, v_k_4369_, v_kind_boxed_4377_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
    crate::leanh::lean_dec(v___y_4375_);
    crate::leanh::lean_dec_ref(v___y_4374_);
    crate::leanh::lean_dec(v___y_4373_);
    crate::leanh::lean_dec_ref(v___y_4372_);
    crate::leanh::lean_dec(v___y_4371_);
    return v_res_4378_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(
    mut v_snd_4379_: *mut crate::leanh::LeanObject,
    mut v_x_4380_: *mut crate::leanh::LeanObject,
    mut v___y_4381_: *mut crate::leanh::LeanObject,
    mut v___y_4382_: *mut crate::leanh::LeanObject,
    mut v___y_4383_: *mut crate::leanh::LeanObject,
    mut v___y_4384_: *mut crate::leanh::LeanObject,
    mut v___y_4385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4387_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4387_, 0, v_snd_4379_);
    return v___x_4387_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed(
    mut v_snd_4388_: *mut crate::leanh::LeanObject,
    mut v_x_4389_: *mut crate::leanh::LeanObject,
    mut v___y_4390_: *mut crate::leanh::LeanObject,
    mut v___y_4391_: *mut crate::leanh::LeanObject,
    mut v___y_4392_: *mut crate::leanh::LeanObject,
    mut v___y_4393_: *mut crate::leanh::LeanObject,
    mut v___y_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(v_snd_4388_, v_x_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
    crate::leanh::lean_dec(v___y_4394_);
    crate::leanh::lean_dec_ref(v___y_4393_);
    crate::leanh::lean_dec(v___y_4392_);
    crate::leanh::lean_dec_ref(v___y_4391_);
    crate::leanh::lean_dec(v___y_4390_);
    crate::leanh::lean_dec_ref(v_x_4389_);
    return v_res_4396_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(
    mut v_sz_4397_: usize,
    mut v_i_4398_: usize,
    mut v_bs_4399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4400_: u8 = 0;
    let mut v_v_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4406_: u8 = 0;
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: usize = 0;
    let mut v___x_4413_: usize = 0;
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4400_ = lean_usize_dec_lt(v_i_4398_, v_sz_4397_);
                if v___x_4400_ == 0 {
                    return v_bs_4399_;
                } else {
                    v_v_4401_ = lean_array_uget(v_bs_4399_, v_i_4398_);
                    v_fst_4402_ = crate::leanh::lean_ctor_get(v_v_4401_, 0);
                    v_snd_4403_ = crate::leanh::lean_ctor_get(v_v_4401_, 1);
                    v_isSharedCheck_4417_ = (!crate::leanh::lean_is_exclusive(v_v_4401_)) as u8;
                    if v_isSharedCheck_4417_ == 0 {
                        v___x_4405_ = v_v_4401_;
                        v_isShared_4406_ = v_isSharedCheck_4417_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4403_);
                        crate::leanh::lean_inc(v_fst_4402_);
                        crate::leanh::lean_dec(v_v_4401_);
                        v___x_4405_ = crate::leanh::lean_box(0);
                        v_isShared_4406_ = v_isSharedCheck_4417_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4407_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_4408_ = lean_array_uset(v_bs_4399_, v_i_4398_, v___x_4407_);
                v___f_4409_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_4409_, 0, v_snd_4403_);
                if v_isShared_4406_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4405_, 1, v___f_4409_);
                    v___x_4411_ = v___x_4405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4416_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_fst_4402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4416_, 1, v___f_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4412_ = 1usize;
                v___x_4413_ = lean_usize_add(v_i_4398_, v___x_4412_);
                v___x_4414_ = lean_array_uset(v_bs_x27_4408_, v_i_4398_, v___x_4411_);
                v_i_4398_ = v___x_4413_;
                v_bs_4399_ = v___x_4414_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___boxed(
    mut v_sz_4418_: *mut crate::leanh::LeanObject,
    mut v_i_4419_: *mut crate::leanh::LeanObject,
    mut v_bs_4420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4421_: usize = 0;
    let mut v_i_boxed_4422_: usize = 0;
    let mut v_res_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4421_ = crate::leanh::lean_unbox_usize(v_sz_4418_);
    crate::leanh::lean_dec(v_sz_4418_);
    v_i_boxed_4422_ = crate::leanh::lean_unbox_usize(v_i_4419_);
    crate::leanh::lean_dec(v_i_4419_);
    v_res_4423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_boxed_4421_, v_i_boxed_4422_, v_bs_4420_);
    return v_res_4423_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5(
    mut v_declInfos_4424_: *mut crate::leanh::LeanObject,
    mut v_k_4425_: *mut crate::leanh::LeanObject,
    mut v_kind_4426_: u8,
    mut v___y_4427_: *mut crate::leanh::LeanObject,
    mut v___y_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4433_: usize = 0;
    let mut v___x_4434_: usize = 0;
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4433_ = lean_array_size(v_declInfos_4424_);
    v___x_4434_ = 0usize;
    v___x_4435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_4433_, v___x_4434_, v_declInfos_4424_);
    v___x_4436_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(v___x_4435_, v_k_4425_, v_kind_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
    return v___x_4436_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5___boxed(
    mut v_declInfos_4437_: *mut crate::leanh::LeanObject,
    mut v_k_4438_: *mut crate::leanh::LeanObject,
    mut v_kind_4439_: *mut crate::leanh::LeanObject,
    mut v___y_4440_: *mut crate::leanh::LeanObject,
    mut v___y_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
    mut v___y_4443_: *mut crate::leanh::LeanObject,
    mut v___y_4444_: *mut crate::leanh::LeanObject,
    mut v___y_4445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4446_: u8 = 0;
    let mut v_res_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4446_ = (crate::leanh::lean_unbox(v_kind_4439_) as u8);
    v_res_4447_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5(v_declInfos_4437_, v_k_4438_, v_kind_boxed_4446_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
    crate::leanh::lean_dec(v___y_4444_);
    crate::leanh::lean_dec_ref(v___y_4443_);
    crate::leanh::lean_dec(v___y_4442_);
    crate::leanh::lean_dec_ref(v___y_4441_);
    crate::leanh::lean_dec(v___y_4440_);
    return v_res_4447_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4(
    mut v___x_4451_: *mut crate::leanh::LeanObject,
    mut v_sz_4452_: usize,
    mut v_i_4453_: usize,
    mut v_bs_4454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4455_: u8 = 0;
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: usize = 0;
    let mut v___x_4461_: usize = 0;
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4455_ = lean_usize_dec_lt(v_i_4453_, v_sz_4452_);
                if v___x_4455_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4451_);
                    return v_bs_4454_;
                } else {
                    v___x_4456_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4457_ = lean_array_uset(v_bs_4454_, v_i_4453_, v___x_4456_);
                    v___x_4458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1;
                    crate::leanh::lean_inc_ref(v___x_4451_);
                    v___x_4459_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4459_, 0, v___x_4458_);
                    crate::leanh::lean_ctor_set(v___x_4459_, 1, v___x_4451_);
                    v___x_4460_ = 1usize;
                    v___x_4461_ = lean_usize_add(v_i_4453_, v___x_4460_);
                    v___x_4462_ = lean_array_uset(v_bs_x27_4457_, v_i_4453_, v___x_4459_);
                    v_i_4453_ = v___x_4461_;
                    v_bs_4454_ = v___x_4462_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___boxed(
    mut v___x_4464_: *mut crate::leanh::LeanObject,
    mut v_sz_4465_: *mut crate::leanh::LeanObject,
    mut v_i_4466_: *mut crate::leanh::LeanObject,
    mut v_bs_4467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4468_: usize = 0;
    let mut v_i_boxed_4469_: usize = 0;
    let mut v_res_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4468_ = crate::leanh::lean_unbox_usize(v_sz_4465_);
    crate::leanh::lean_dec(v_sz_4465_);
    v_i_boxed_4469_ = crate::leanh::lean_unbox_usize(v_i_4466_);
    crate::leanh::lean_dec(v_i_4466_);
    v_res_4470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_4464_, v_sz_boxed_4468_, v_i_boxed_4469_, v_bs_4467_);
    return v_res_4470_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2(
    mut v___x_4474_: *mut crate::leanh::LeanObject,
    mut v_z_4475_: *mut crate::leanh::LeanObject,
    mut v___y_4476_: *mut crate::leanh::LeanObject,
    mut v___x_4477_: usize,
    mut v___f_4478_: *mut crate::leanh::LeanObject,
    mut v___x_4479_: *mut crate::leanh::LeanObject,
    mut v___x_4480_: u8,
    mut v_other_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
    mut v___y_4483_: *mut crate::leanh::LeanObject,
    mut v___y_4484_: *mut crate::leanh::LeanObject,
    mut v___y_4485_: *mut crate::leanh::LeanObject,
    mut v___y_4486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4491_: usize = 0;
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: u8 = 0;
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4507_: u8 = 0;
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4512_: u8 = 0;
    let mut v_a_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4516_: u8 = 0;
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4520_: u8 = 0;
    let mut v_a_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4488_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1;
                v___x_4489_ = l_Lean_mkConst(v___x_4488_, v___x_4474_);
                crate::leanh::lean_inc_ref(v_z_4475_);
                v___x_4490_ = l_Lean_Expr_app___override(v___x_4489_, v_z_4475_);
                v_sz_4491_ = lean_array_size(v___y_4476_);
                v___x_4492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_4490_, v_sz_4491_, v___x_4477_, v___y_4476_);
                v___x_4493_ = 0;
                v___x_4494_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5(v___x_4492_, v___f_4478_, v___x_4493_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
                if crate::leanh::lean_obj_tag(v___x_4494_) == 0 {
                    v_a_4495_ = crate::leanh::lean_ctor_get(v___x_4494_, 0);
                    crate::leanh::lean_inc(v_a_4495_);
                    crate::leanh::lean_dec_ref_known(v___x_4494_, 1);
                    crate::leanh::lean_inc_ref(v_z_4475_);
                    v___x_4496_ = l_Lean_Expr_replaceFVar(v_a_4495_, v_z_4475_, v___x_4479_);
                    v___x_4497_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_4498_ = lean_mk_empty_array_with_capacity(v___x_4497_);
                    v___x_4499_ = lean_array_push(v___x_4498_, v_z_4475_);
                    v___x_4500_ = lean_array_push(v___x_4499_, v_other_4481_);
                    v___x_4501_ = 0;
                    v___x_4502_ = 1;
                    v___x_4503_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_4500_,
                        v_a_4495_,
                        v___x_4501_,
                        v___x_4480_,
                        v___x_4501_,
                        v___x_4480_,
                        v___x_4502_,
                        v___y_4483_,
                        v___y_4484_,
                        v___y_4485_,
                        v___y_4486_,
                    );
                    crate::leanh::lean_dec_ref(v___x_4500_);
                    if crate::leanh::lean_obj_tag(v___x_4503_) == 0 {
                        v_a_4504_ = crate::leanh::lean_ctor_get(v___x_4503_, 0);
                        v_isSharedCheck_4512_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4503_)) as u8;
                        if v_isSharedCheck_4512_ == 0 {
                            v___x_4506_ = v___x_4503_;
                            v_isShared_4507_ = v_isSharedCheck_4512_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4504_);
                            crate::leanh::lean_dec(v___x_4503_);
                            v___x_4506_ = crate::leanh::lean_box(0);
                            v_isShared_4507_ = v_isSharedCheck_4512_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4496_);
                        v_a_4513_ = crate::leanh::lean_ctor_get(v___x_4503_, 0);
                        v_isSharedCheck_4520_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4503_)) as u8;
                        if v_isSharedCheck_4520_ == 0 {
                            v___x_4515_ = v___x_4503_;
                            v_isShared_4516_ = v_isSharedCheck_4520_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4513_);
                            crate::leanh::lean_dec(v___x_4503_);
                            v___x_4515_ = crate::leanh::lean_box(0);
                            v_isShared_4516_ = v_isSharedCheck_4520_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_other_4481_);
                    crate::leanh::lean_dec_ref(v_z_4475_);
                    v_a_4521_ = crate::leanh::lean_ctor_get(v___x_4494_, 0);
                    v_isSharedCheck_4528_ = (!crate::leanh::lean_is_exclusive(v___x_4494_)) as u8;
                    if v_isSharedCheck_4528_ == 0 {
                        v___x_4523_ = v___x_4494_;
                        v_isShared_4524_ = v_isSharedCheck_4528_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4521_);
                        crate::leanh::lean_dec(v___x_4494_);
                        v___x_4523_ = crate::leanh::lean_box(0);
                        v_isShared_4524_ = v_isSharedCheck_4528_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4508_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4508_, 0, v_a_4504_);
                crate::leanh::lean_ctor_set(v___x_4508_, 1, v___x_4496_);
                if v_isShared_4507_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4506_, 0, v___x_4508_);
                    v___x_4510_ = v___x_4506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4511_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
                    v___x_4510_ = v_reuseFailAlloc_4511_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4510_;
            }
            3 => {
                if v_isShared_4516_ == 0 {
                    v___x_4518_ = v___x_4515_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
                    v___x_4518_ = v_reuseFailAlloc_4519_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4518_;
            }
            5 => {
                if v_isShared_4524_ == 0 {
                    v___x_4526_ = v___x_4523_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
                    v___x_4526_ = v_reuseFailAlloc_4527_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___boxed(
    mut v___x_4529_: *mut crate::leanh::LeanObject,
    mut v_z_4530_: *mut crate::leanh::LeanObject,
    mut v___y_4531_: *mut crate::leanh::LeanObject,
    mut v___x_4532_: *mut crate::leanh::LeanObject,
    mut v___f_4533_: *mut crate::leanh::LeanObject,
    mut v___x_4534_: *mut crate::leanh::LeanObject,
    mut v___x_4535_: *mut crate::leanh::LeanObject,
    mut v_other_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
    mut v___y_4538_: *mut crate::leanh::LeanObject,
    mut v___y_4539_: *mut crate::leanh::LeanObject,
    mut v___y_4540_: *mut crate::leanh::LeanObject,
    mut v___y_4541_: *mut crate::leanh::LeanObject,
    mut v___y_4542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_21741__boxed_4543_: usize = 0;
    let mut v___x_21744__boxed_4544_: u8 = 0;
    let mut v_res_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_21741__boxed_4543_ = crate::leanh::lean_unbox_usize(v___x_4532_);
    crate::leanh::lean_dec(v___x_4532_);
    v___x_21744__boxed_4544_ = (crate::leanh::lean_unbox(v___x_4535_) as u8);
    v_res_4545_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2(v___x_4529_, v_z_4530_, v___y_4531_, v___x_21741__boxed_4543_, v___f_4533_, v___x_4534_, v___x_21744__boxed_4544_, v_other_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
    crate::leanh::lean_dec(v___y_4541_);
    crate::leanh::lean_dec_ref(v___y_4540_);
    crate::leanh::lean_dec(v___y_4539_);
    crate::leanh::lean_dec_ref(v___y_4538_);
    crate::leanh::lean_dec(v___y_4537_);
    crate::leanh::lean_dec_ref(v___x_4534_);
    return v_res_4545_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(
    mut v_k_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
    mut v_b_4548_: *mut crate::leanh::LeanObject,
    mut v___y_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
    mut v___y_4551_: *mut crate::leanh::LeanObject,
    mut v___y_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4552_);
    crate::leanh::lean_inc_ref(v___y_4551_);
    crate::leanh::lean_inc(v___y_4550_);
    crate::leanh::lean_inc_ref(v___y_4549_);
    crate::leanh::lean_inc(v___y_4547_);
    v___x_4554_ = crate::leanh::lean_apply_7(
        v_k_4546_,
        v_b_4548_,
        v___y_4547_,
        v___y_4549_,
        v___y_4550_,
        v___y_4551_,
        v___y_4552_,
        crate::leanh::lean_box(0),
    );
    return v___x_4554_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed(
    mut v_k_4555_: *mut crate::leanh::LeanObject,
    mut v___y_4556_: *mut crate::leanh::LeanObject,
    mut v_b_4557_: *mut crate::leanh::LeanObject,
    mut v___y_4558_: *mut crate::leanh::LeanObject,
    mut v___y_4559_: *mut crate::leanh::LeanObject,
    mut v___y_4560_: *mut crate::leanh::LeanObject,
    mut v___y_4561_: *mut crate::leanh::LeanObject,
    mut v___y_4562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4563_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(v_k_4555_, v___y_4556_, v_b_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
    crate::leanh::lean_dec(v___y_4561_);
    crate::leanh::lean_dec_ref(v___y_4560_);
    crate::leanh::lean_dec(v___y_4559_);
    crate::leanh::lean_dec_ref(v___y_4558_);
    crate::leanh::lean_dec(v___y_4556_);
    return v_res_4563_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(
    mut v_name_4564_: *mut crate::leanh::LeanObject,
    mut v_bi_4565_: u8,
    mut v_type_4566_: *mut crate::leanh::LeanObject,
    mut v_k_4567_: *mut crate::leanh::LeanObject,
    mut v_kind_4568_: u8,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
    mut v___y_4573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4569_);
                v___f_4575_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                crate::leanh::lean_closure_set(v___f_4575_, 0, v_k_4567_);
                crate::leanh::lean_closure_set(v___f_4575_, 1, v___y_4569_);
                v___x_4576_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_4564_,
                    v_bi_4565_,
                    v_type_4566_,
                    v___f_4575_,
                    v_kind_4568_,
                    v___y_4570_,
                    v___y_4571_,
                    v___y_4572_,
                    v___y_4573_,
                );
                if crate::leanh::lean_obj_tag(v___x_4576_) == 0 {
                    return v___x_4576_;
                } else {
                    v_a_4577_ = crate::leanh::lean_ctor_get(v___x_4576_, 0);
                    v_isSharedCheck_4584_ = (!crate::leanh::lean_is_exclusive(v___x_4576_)) as u8;
                    if v_isSharedCheck_4584_ == 0 {
                        v___x_4579_ = v___x_4576_;
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4577_);
                        crate::leanh::lean_dec(v___x_4576_);
                        v___x_4579_ = crate::leanh::lean_box(0);
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4580_ == 0 {
                    v___x_4582_ = v___x_4579_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
                    v___x_4582_ = v_reuseFailAlloc_4583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___boxed(
    mut v_name_4585_: *mut crate::leanh::LeanObject,
    mut v_bi_4586_: *mut crate::leanh::LeanObject,
    mut v_type_4587_: *mut crate::leanh::LeanObject,
    mut v_k_4588_: *mut crate::leanh::LeanObject,
    mut v_kind_4589_: *mut crate::leanh::LeanObject,
    mut v___y_4590_: *mut crate::leanh::LeanObject,
    mut v___y_4591_: *mut crate::leanh::LeanObject,
    mut v___y_4592_: *mut crate::leanh::LeanObject,
    mut v___y_4593_: *mut crate::leanh::LeanObject,
    mut v___y_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4596_: u8 = 0;
    let mut v_kind_boxed_4597_: u8 = 0;
    let mut v_res_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4596_ = (crate::leanh::lean_unbox(v_bi_4586_) as u8);
    v_kind_boxed_4597_ = (crate::leanh::lean_unbox(v_kind_4589_) as u8);
    v_res_4598_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_4585_, v_bi_boxed_4596_, v_type_4587_, v_k_4588_, v_kind_boxed_4597_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
    crate::leanh::lean_dec(v___y_4594_);
    crate::leanh::lean_dec_ref(v___y_4593_);
    crate::leanh::lean_dec(v___y_4592_);
    crate::leanh::lean_dec_ref(v___y_4591_);
    crate::leanh::lean_dec(v___y_4590_);
    return v_res_4598_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(
    mut v_name_4599_: *mut crate::leanh::LeanObject,
    mut v_type_4600_: *mut crate::leanh::LeanObject,
    mut v_k_4601_: *mut crate::leanh::LeanObject,
    mut v___y_4602_: *mut crate::leanh::LeanObject,
    mut v___y_4603_: *mut crate::leanh::LeanObject,
    mut v___y_4604_: *mut crate::leanh::LeanObject,
    mut v___y_4605_: *mut crate::leanh::LeanObject,
    mut v___y_4606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4608_: u8 = 0;
    let mut v___x_4609_: u8 = 0;
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4608_ = 0;
    v___x_4609_ = 0;
    v___x_4610_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_4599_, v___x_4608_, v_type_4600_, v_k_4601_, v___x_4609_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
    return v___x_4610_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg___boxed(
    mut v_name_4611_: *mut crate::leanh::LeanObject,
    mut v_type_4612_: *mut crate::leanh::LeanObject,
    mut v_k_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
    mut v___y_4616_: *mut crate::leanh::LeanObject,
    mut v___y_4617_: *mut crate::leanh::LeanObject,
    mut v___y_4618_: *mut crate::leanh::LeanObject,
    mut v___y_4619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4620_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_4611_, v_type_4612_, v_k_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
    crate::leanh::lean_dec(v___y_4618_);
    crate::leanh::lean_dec_ref(v___y_4617_);
    crate::leanh::lean_dec(v___y_4616_);
    crate::leanh::lean_dec_ref(v___y_4615_);
    crate::leanh::lean_dec(v___y_4614_);
    return v_res_4620_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3(
    mut v___x_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___x_4626_: usize,
    mut v_a_4627_: *mut crate::leanh::LeanObject,
    mut v___x_4628_: u8,
    mut v_fst_4629_: *mut crate::leanh::LeanObject,
    mut v___x_4630_: *mut crate::leanh::LeanObject,
    mut v_z_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2;
    v___x_4639_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4640_ = crate::leanh::lean_box_usize(v___x_4626_);
    v___x_4641_ = crate::leanh::lean_box((v___x_4628_) as usize);
    crate::leanh::lean_inc_ref(v___y_4625_);
    crate::leanh::lean_inc_ref_n(v_z_4631_, 2);
    crate::leanh::lean_inc_n(v___x_4624_, 2);
    v___f_4642_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1___boxed as *mut core::ffi::c_void, 14, 7);
    crate::leanh::lean_closure_set(v___f_4642_, 0, v___x_4639_);
    crate::leanh::lean_closure_set(v___f_4642_, 1, v___x_4624_);
    crate::leanh::lean_closure_set(v___f_4642_, 2, v_z_4631_);
    crate::leanh::lean_closure_set(v___f_4642_, 3, v___y_4625_);
    crate::leanh::lean_closure_set(v___f_4642_, 4, v___x_4640_);
    crate::leanh::lean_closure_set(v___f_4642_, 5, v_a_4627_);
    crate::leanh::lean_closure_set(v___f_4642_, 6, v___x_4641_);
    v___x_4643_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
    v___x_4644_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4644_, 0, v___x_4643_);
    crate::leanh::lean_ctor_set(v___x_4644_, 1, v___x_4624_);
    v___x_4645_ = l_Lean_mkConst(v___x_4638_, v___x_4644_);
    v___x_4646_ = l_Lean_mkNatLit(v_fst_4629_);
    v___x_4647_ = crate::leanh::lean_box_usize(v___x_4626_);
    v___x_4648_ = crate::leanh::lean_box((v___x_4628_) as usize);
    crate::leanh::lean_inc_ref(v___x_4646_);
    v___f_4649_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___boxed as *mut core::ffi::c_void, 14, 7);
    crate::leanh::lean_closure_set(v___f_4649_, 0, v___x_4624_);
    crate::leanh::lean_closure_set(v___f_4649_, 1, v_z_4631_);
    crate::leanh::lean_closure_set(v___f_4649_, 2, v___y_4625_);
    crate::leanh::lean_closure_set(v___f_4649_, 3, v___x_4647_);
    crate::leanh::lean_closure_set(v___f_4649_, 4, v___f_4642_);
    crate::leanh::lean_closure_set(v___f_4649_, 5, v___x_4646_);
    crate::leanh::lean_closure_set(v___f_4649_, 6, v___x_4648_);
    v___x_4650_ = l_Lean_mkApp3(v___x_4645_, v___x_4630_, v___x_4646_, v_z_4631_);
    v___x_4651_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1;
    v___x_4652_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_4651_, v___x_4650_, v___f_4649_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_);
    return v___x_4652_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___boxed(
    mut v___x_4653_: *mut crate::leanh::LeanObject,
    mut v___y_4654_: *mut crate::leanh::LeanObject,
    mut v___x_4655_: *mut crate::leanh::LeanObject,
    mut v_a_4656_: *mut crate::leanh::LeanObject,
    mut v___x_4657_: *mut crate::leanh::LeanObject,
    mut v_fst_4658_: *mut crate::leanh::LeanObject,
    mut v___x_4659_: *mut crate::leanh::LeanObject,
    mut v_z_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
    mut v___y_4662_: *mut crate::leanh::LeanObject,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_21954__boxed_4667_: usize = 0;
    let mut v___x_21956__boxed_4668_: u8 = 0;
    let mut v_res_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_21954__boxed_4667_ = crate::leanh::lean_unbox_usize(v___x_4655_);
    crate::leanh::lean_dec(v___x_4655_);
    v___x_21956__boxed_4668_ = (crate::leanh::lean_unbox(v___x_4657_) as u8);
    v_res_4669_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3(v___x_4653_, v___y_4654_, v___x_21954__boxed_4667_, v_a_4656_, v___x_21956__boxed_4668_, v_fst_4658_, v___x_4659_, v_z_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
    crate::leanh::lean_dec(v___y_4665_);
    crate::leanh::lean_dec_ref(v___y_4664_);
    crate::leanh::lean_dec(v___y_4663_);
    crate::leanh::lean_dec_ref(v___y_4662_);
    crate::leanh::lean_dec(v___y_4661_);
    return v_res_4669_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__10(
    mut v_x_4670_: *mut crate::leanh::LeanObject,
    mut v_x_4671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4671_) == 0 {
                    return v_x_4670_;
                } else {
                    v_key_4672_ = crate::leanh::lean_ctor_get(v_x_4671_, 0);
                    crate::leanh::lean_inc(v_key_4672_);
                    v_tail_4673_ = crate::leanh::lean_ctor_get(v_x_4671_, 2);
                    crate::leanh::lean_inc(v_tail_4673_);
                    crate::leanh::lean_dec_ref_known(v_x_4671_, 3);
                    v___x_4674_ = lean_array_push(v_x_4670_, v_key_4672_);
                    v_x_4670_ = v___x_4674_;
                    v_x_4671_ = v_tail_4673_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(
    mut v_as_4676_: *mut crate::leanh::LeanObject,
    mut v_i_4677_: usize,
    mut v_stop_4678_: usize,
    mut v_b_4679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4680_: u8 = 0;
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: usize = 0;
    let mut v___x_4684_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4680_ = lean_usize_dec_eq(v_i_4677_, v_stop_4678_);
                if v___x_4680_ == 0 {
                    v___x_4681_ = lean_array_uget_borrowed(v_as_4676_, v_i_4677_);
                    crate::leanh::lean_inc(v___x_4681_);
                    v___x_4682_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__10(v_b_4679_, v___x_4681_);
                    v___x_4683_ = 1usize;
                    v___x_4684_ = lean_usize_add(v_i_4677_, v___x_4683_);
                    v_i_4677_ = v___x_4684_;
                    v_b_4679_ = v___x_4682_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4679_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11___boxed(
    mut v_as_4686_: *mut crate::leanh::LeanObject,
    mut v_i_4687_: *mut crate::leanh::LeanObject,
    mut v_stop_4688_: *mut crate::leanh::LeanObject,
    mut v_b_4689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4690_: usize = 0;
    let mut v_stop_boxed_4691_: usize = 0;
    let mut v_res_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4690_ = crate::leanh::lean_unbox_usize(v_i_4687_);
    crate::leanh::lean_dec(v_i_4687_);
    v_stop_boxed_4691_ = crate::leanh::lean_unbox_usize(v_stop_4688_);
    crate::leanh::lean_dec(v_stop_4688_);
    v_res_4692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(v_as_4686_, v_i_boxed_4690_, v_stop_boxed_4691_, v_b_4689_);
    crate::leanh::lean_dec_ref(v_as_4686_);
    return v_res_4692_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(
    mut v_msgData_4693_: *mut crate::leanh::LeanObject,
    mut v___y_4694_: *mut crate::leanh::LeanObject,
    mut v___y_4695_: *mut crate::leanh::LeanObject,
    mut v___y_4696_: *mut crate::leanh::LeanObject,
    mut v___y_4697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4699_ = lean_st_ref_get(v___y_4697_);
    v_env_4700_ = crate::leanh::lean_ctor_get(v___x_4699_, 0);
    crate::leanh::lean_inc_ref(v_env_4700_);
    crate::leanh::lean_dec(v___x_4699_);
    v___x_4701_ = lean_st_ref_get(v___y_4695_);
    v_mctx_4702_ = crate::leanh::lean_ctor_get(v___x_4701_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4702_);
    crate::leanh::lean_dec(v___x_4701_);
    v_lctx_4703_ = crate::leanh::lean_ctor_get(v___y_4694_, 2);
    v_options_4704_ = crate::leanh::lean_ctor_get(v___y_4696_, 2);
    crate::leanh::lean_inc_ref(v_options_4704_);
    crate::leanh::lean_inc_ref(v_lctx_4703_);
    v___x_4705_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4705_, 0, v_env_4700_);
    crate::leanh::lean_ctor_set(v___x_4705_, 1, v_mctx_4702_);
    crate::leanh::lean_ctor_set(v___x_4705_, 2, v_lctx_4703_);
    crate::leanh::lean_ctor_set(v___x_4705_, 3, v_options_4704_);
    v___x_4706_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4706_, 0, v___x_4705_);
    crate::leanh::lean_ctor_set(v___x_4706_, 1, v_msgData_4693_);
    v___x_4707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4707_, 0, v___x_4706_);
    return v___x_4707_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17___boxed(
    mut v_msgData_4708_: *mut crate::leanh::LeanObject,
    mut v___y_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
    mut v___y_4712_: *mut crate::leanh::LeanObject,
    mut v___y_4713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4714_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msgData_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
    crate::leanh::lean_dec(v___y_4712_);
    crate::leanh::lean_dec_ref(v___y_4711_);
    crate::leanh::lean_dec(v___y_4710_);
    crate::leanh::lean_dec_ref(v___y_4709_);
    return v_res_4714_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(
    mut v_msg_4715_: *mut crate::leanh::LeanObject,
    mut v___y_4716_: *mut crate::leanh::LeanObject,
    mut v___y_4717_: *mut crate::leanh::LeanObject,
    mut v___y_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4726_: u8 = 0;
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4721_ = crate::leanh::lean_ctor_get(v___y_4718_, 5);
                v___x_4722_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msg_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
                v_a_4723_ = crate::leanh::lean_ctor_get(v___x_4722_, 0);
                v_isSharedCheck_4731_ = (!crate::leanh::lean_is_exclusive(v___x_4722_)) as u8;
                if v_isSharedCheck_4731_ == 0 {
                    v___x_4725_ = v___x_4722_;
                    v_isShared_4726_ = v_isSharedCheck_4731_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4723_);
                    crate::leanh::lean_dec(v___x_4722_);
                    v___x_4725_ = crate::leanh::lean_box(0);
                    v_isShared_4726_ = v_isSharedCheck_4731_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4721_);
                v___x_4727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4727_, 0, v_ref_4721_);
                crate::leanh::lean_ctor_set(v___x_4727_, 1, v_a_4723_);
                if v_isShared_4726_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4725_, 1);
                    crate::leanh::lean_ctor_set(v___x_4725_, 0, v___x_4727_);
                    v___x_4729_ = v___x_4725_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4727_);
                    v___x_4729_ = v_reuseFailAlloc_4730_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg___boxed(
    mut v_msg_4732_: *mut crate::leanh::LeanObject,
    mut v___y_4733_: *mut crate::leanh::LeanObject,
    mut v___y_4734_: *mut crate::leanh::LeanObject,
    mut v___y_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4738_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
    crate::leanh::lean_dec(v___y_4736_);
    crate::leanh::lean_dec_ref(v___y_4735_);
    crate::leanh::lean_dec(v___y_4734_);
    crate::leanh::lean_dec_ref(v___y_4733_);
    return v_res_4738_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1(
    mut v_sz_4739_: usize,
    mut v_i_4740_: usize,
    mut v_bs_4741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4742_: u8 = 0;
    let mut v_v_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: usize = 0;
    let mut v___x_4748_: usize = 0;
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4742_ = lean_usize_dec_lt(v_i_4740_, v_sz_4739_);
                if v___x_4742_ == 0 {
                    return v_bs_4741_;
                } else {
                    v_v_4743_ = lean_array_uget(v_bs_4741_, v_i_4740_);
                    v___x_4744_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4745_ = lean_array_uset(v_bs_4741_, v_i_4740_, v___x_4744_);
                    v___x_4746_ = l_Lean_mkFVar(v_v_4743_);
                    v___x_4747_ = 1usize;
                    v___x_4748_ = lean_usize_add(v_i_4740_, v___x_4747_);
                    v___x_4749_ = lean_array_uset(v_bs_x27_4745_, v_i_4740_, v___x_4746_);
                    v_i_4740_ = v___x_4748_;
                    v_bs_4741_ = v___x_4749_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1___boxed(
    mut v_sz_4751_: *mut crate::leanh::LeanObject,
    mut v_i_4752_: *mut crate::leanh::LeanObject,
    mut v_bs_4753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4754_: usize = 0;
    let mut v_i_boxed_4755_: usize = 0;
    let mut v_res_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4754_ = crate::leanh::lean_unbox_usize(v_sz_4751_);
    crate::leanh::lean_dec(v_sz_4751_);
    v_i_boxed_4755_ = crate::leanh::lean_unbox_usize(v_i_4752_);
    crate::leanh::lean_dec(v_i_4752_);
    v_res_4756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_boxed_4754_, v_i_boxed_4755_, v_bs_4753_);
    return v_res_4756_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__12(
    mut v_x_4757_: *mut crate::leanh::LeanObject,
    mut v_x_4758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4758_) == 0 {
                    return v_x_4757_;
                } else {
                    v_key_4759_ = crate::leanh::lean_ctor_get(v_x_4758_, 0);
                    crate::leanh::lean_inc(v_key_4759_);
                    v_tail_4760_ = crate::leanh::lean_ctor_get(v_x_4758_, 2);
                    crate::leanh::lean_inc(v_tail_4760_);
                    crate::leanh::lean_dec_ref_known(v_x_4758_, 3);
                    v___x_4761_ = lean_array_push(v_x_4757_, v_key_4759_);
                    v_x_4757_ = v___x_4761_;
                    v_x_4758_ = v_tail_4760_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(
    mut v_as_4763_: *mut crate::leanh::LeanObject,
    mut v_i_4764_: usize,
    mut v_stop_4765_: usize,
    mut v_b_4766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4767_: u8 = 0;
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: usize = 0;
    let mut v___x_4771_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4767_ = lean_usize_dec_eq(v_i_4764_, v_stop_4765_);
                if v___x_4767_ == 0 {
                    v___x_4768_ = lean_array_uget_borrowed(v_as_4763_, v_i_4764_);
                    crate::leanh::lean_inc(v___x_4768_);
                    v___x_4769_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__12(v_b_4766_, v___x_4768_);
                    v___x_4770_ = 1usize;
                    v___x_4771_ = lean_usize_add(v_i_4764_, v___x_4770_);
                    v_i_4764_ = v___x_4771_;
                    v_b_4766_ = v___x_4769_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4766_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13___boxed(
    mut v_as_4773_: *mut crate::leanh::LeanObject,
    mut v_i_4774_: *mut crate::leanh::LeanObject,
    mut v_stop_4775_: *mut crate::leanh::LeanObject,
    mut v_b_4776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4777_: usize = 0;
    let mut v_stop_boxed_4778_: usize = 0;
    let mut v_res_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4777_ = crate::leanh::lean_unbox_usize(v_i_4774_);
    crate::leanh::lean_dec(v_i_4774_);
    v_stop_boxed_4778_ = crate::leanh::lean_unbox_usize(v_stop_4775_);
    crate::leanh::lean_dec(v_stop_4775_);
    v_res_4779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(v_as_4773_, v_i_boxed_4777_, v_stop_boxed_4778_, v_b_4776_);
    crate::leanh::lean_dec_ref(v_as_4773_);
    return v_res_4779_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8(
    mut v_sz_4780_: usize,
    mut v_i_4781_: usize,
    mut v_bs_4782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4783_: u8 = 0;
    let mut v_v_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: usize = 0;
    let mut v___x_4789_: usize = 0;
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4783_ = lean_usize_dec_lt(v_i_4781_, v_sz_4780_);
                if v___x_4783_ == 0 {
                    return v_bs_4782_;
                } else {
                    v_v_4784_ = lean_array_uget(v_bs_4782_, v_i_4781_);
                    v___x_4785_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4786_ = lean_array_uset(v_bs_4782_, v_i_4781_, v___x_4785_);
                    v___x_4787_ = l_Lean_Expr_fvarId_x21(v_v_4784_);
                    crate::leanh::lean_dec(v_v_4784_);
                    v___x_4788_ = 1usize;
                    v___x_4789_ = lean_usize_add(v_i_4781_, v___x_4788_);
                    v___x_4790_ = lean_array_uset(v_bs_x27_4786_, v_i_4781_, v___x_4787_);
                    v_i_4781_ = v___x_4789_;
                    v_bs_4782_ = v___x_4790_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8___boxed(
    mut v_sz_4792_: *mut crate::leanh::LeanObject,
    mut v_i_4793_: *mut crate::leanh::LeanObject,
    mut v_bs_4794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4795_: usize = 0;
    let mut v_i_boxed_4796_: usize = 0;
    let mut v_res_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4795_ = crate::leanh::lean_unbox_usize(v_sz_4792_);
    crate::leanh::lean_dec(v_sz_4792_);
    v_i_boxed_4796_ = crate::leanh::lean_unbox_usize(v_i_4793_);
    crate::leanh::lean_dec(v_i_4793_);
    v_res_4797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_boxed_4795_, v_i_boxed_4796_, v_bs_4794_);
    return v_res_4797_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(
    mut v_x_4798_: *mut crate::leanh::LeanObject,
    mut v_x_4799_: *mut crate::leanh::LeanObject,
    mut v_x_4800_: *mut crate::leanh::LeanObject,
    mut v_x_4801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4806_: u8 = 0;
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: u8 = 0;
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: u8 = 0;
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4802_ = crate::leanh::lean_ctor_get(v_x_4798_, 0);
                v_vs_4803_ = crate::leanh::lean_ctor_get(v_x_4798_, 1);
                v_isSharedCheck_4827_ = (!crate::leanh::lean_is_exclusive(v_x_4798_)) as u8;
                if v_isSharedCheck_4827_ == 0 {
                    v___x_4805_ = v_x_4798_;
                    v_isShared_4806_ = v_isSharedCheck_4827_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4803_);
                    crate::leanh::lean_inc(v_ks_4802_);
                    crate::leanh::lean_dec(v_x_4798_);
                    v___x_4805_ = crate::leanh::lean_box(0);
                    v_isShared_4806_ = v_isSharedCheck_4827_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4807_ = lean_array_get_size(v_ks_4802_);
                v___x_4808_ = lean_nat_dec_lt(v_x_4799_, v___x_4807_);
                if v___x_4808_ == 0 {
                    crate::leanh::lean_dec(v_x_4799_);
                    v___x_4809_ = lean_array_push(v_ks_4802_, v_x_4800_);
                    v___x_4810_ = lean_array_push(v_vs_4803_, v_x_4801_);
                    if v_isShared_4806_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4805_, 1, v___x_4810_);
                        crate::leanh::lean_ctor_set(v___x_4805_, 0, v___x_4809_);
                        v___x_4812_ = v___x_4805_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4813_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4809_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4813_, 1, v___x_4810_);
                        v___x_4812_ = v_reuseFailAlloc_4813_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4814_ = lean_array_fget_borrowed(v_ks_4802_, v_x_4799_);
                    v___x_4815_ = l_Lean_instBEqMVarId_beq(v_x_4800_, v_k_x27_4814_);
                    if v___x_4815_ == 0 {
                        if v_isShared_4806_ == 0 {
                            v___x_4817_ = v___x_4805_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4821_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_ks_4802_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4821_, 1, v_vs_4803_);
                            v___x_4817_ = v_reuseFailAlloc_4821_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4822_ = lean_array_fset(v_ks_4802_, v_x_4799_, v_x_4800_);
                        v___x_4823_ = lean_array_fset(v_vs_4803_, v_x_4799_, v_x_4801_);
                        crate::leanh::lean_dec(v_x_4799_);
                        if v_isShared_4806_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4805_, 1, v___x_4823_);
                            crate::leanh::lean_ctor_set(v___x_4805_, 0, v___x_4822_);
                            v___x_4825_ = v___x_4805_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4826_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4822_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 1, v___x_4823_);
                            v___x_4825_ = v_reuseFailAlloc_4826_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4812_;
            }
            3 => {
                v___x_4818_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4819_ = lean_nat_add(v_x_4799_, v___x_4818_);
                crate::leanh::lean_dec(v_x_4799_);
                v_x_4798_ = v___x_4817_;
                v_x_4799_ = v___x_4819_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(
    mut v_n_4828_: *mut crate::leanh::LeanObject,
    mut v_k_4829_: *mut crate::leanh::LeanObject,
    mut v_v_4830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4832_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_n_4828_, v___x_4831_, v_k_4829_, v_v_4830_);
    return v___x_4832_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0()
-> usize {
    let mut v___x_4833_: usize = 0;
    let mut v___x_4834_: usize = 0;
    let mut v___x_4835_: usize = 0;
    v___x_4833_ = 5usize;
    v___x_4834_ = 1usize;
    v___x_4835_ = lean_usize_shift_left(v___x_4834_, v___x_4833_);
    return v___x_4835_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1()
-> usize {
    let mut v___x_4836_: usize = 0;
    let mut v___x_4837_: usize = 0;
    let mut v___x_4838_: usize = 0;
    v___x_4836_ = 1usize;
    v___x_4837_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0);
    v___x_4838_ = lean_usize_sub(v___x_4837_, v___x_4836_);
    return v___x_4838_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4839_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4839_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(
    mut v_x_4840_: *mut crate::leanh::LeanObject,
    mut v_x_4841_: usize,
    mut v_x_4842_: usize,
    mut v_x_4843_: *mut crate::leanh::LeanObject,
    mut v_x_4844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: usize = 0;
    let mut v___x_4847_: usize = 0;
    let mut v___x_4848_: usize = 0;
    let mut v___x_4849_: usize = 0;
    let mut v_j_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u8 = 0;
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v_v_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v___x_4870_: u8 = 0;
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4876_: u8 = 0;
    let mut v_node_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4880_: u8 = 0;
    let mut v___x_4881_: usize = 0;
    let mut v___x_4882_: usize = 0;
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4889_: u8 = 0;
    let mut v_unused_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4895_: u8 = 0;
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: u8 = 0;
    let mut v_ks_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: usize = 0;
    let mut v___x_4907_: u8 = 0;
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: u8 = 0;
    let mut v_reuseFailAlloc_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4840_) == 0 {
                    v_es_4845_ = crate::leanh::lean_ctor_get(v_x_4840_, 0);
                    v___x_4846_ = 5usize;
                    v___x_4847_ = 1usize;
                    v___x_4848_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1);
                    v___x_4849_ = lean_usize_land(v_x_4841_, v___x_4848_);
                    v_j_4850_ = lean_usize_to_nat(v___x_4849_);
                    v___x_4851_ = lean_array_get_size(v_es_4845_);
                    v___x_4852_ = lean_nat_dec_lt(v_j_4850_, v___x_4851_);
                    if v___x_4852_ == 0 {
                        crate::leanh::lean_dec(v_j_4850_);
                        crate::leanh::lean_dec(v_x_4844_);
                        crate::leanh::lean_dec(v_x_4843_);
                        return v_x_4840_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4845_);
                        v_isSharedCheck_4889_ = (!crate::leanh::lean_is_exclusive(v_x_4840_)) as u8;
                        if v_isSharedCheck_4889_ == 0 {
                            v_unused_4890_ = crate::leanh::lean_ctor_get(v_x_4840_, 0);
                            crate::leanh::lean_dec(v_unused_4890_);
                            v___x_4854_ = v_x_4840_;
                            v_isShared_4855_ = v_isSharedCheck_4889_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4840_);
                            v___x_4854_ = crate::leanh::lean_box(0);
                            v_isShared_4855_ = v_isSharedCheck_4889_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4891_ = crate::leanh::lean_ctor_get(v_x_4840_, 0);
                    v_vs_4892_ = crate::leanh::lean_ctor_get(v_x_4840_, 1);
                    v_isSharedCheck_4912_ = (!crate::leanh::lean_is_exclusive(v_x_4840_)) as u8;
                    if v_isSharedCheck_4912_ == 0 {
                        v___x_4894_ = v_x_4840_;
                        v_isShared_4895_ = v_isSharedCheck_4912_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4892_);
                        crate::leanh::lean_inc(v_ks_4891_);
                        crate::leanh::lean_dec(v_x_4840_);
                        v___x_4894_ = crate::leanh::lean_box(0);
                        v_isShared_4895_ = v_isSharedCheck_4912_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4856_ = lean_array_fget(v_es_4845_, v_j_4850_);
                v___x_4857_ = crate::leanh::lean_box(0);
                v_xs_x27_4858_ = lean_array_fset(v_es_4845_, v_j_4850_, v___x_4857_);
                match crate::leanh::lean_obj_tag(v_v_4856_) {
                    0 => {
                        v_key_4865_ = crate::leanh::lean_ctor_get(v_v_4856_, 0);
                        v_val_4866_ = crate::leanh::lean_ctor_get(v_v_4856_, 1);
                        v_isSharedCheck_4876_ = (!crate::leanh::lean_is_exclusive(v_v_4856_)) as u8;
                        if v_isSharedCheck_4876_ == 0 {
                            v___x_4868_ = v_v_4856_;
                            v_isShared_4869_ = v_isSharedCheck_4876_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4866_);
                            crate::leanh::lean_inc(v_key_4865_);
                            crate::leanh::lean_dec(v_v_4856_);
                            v___x_4868_ = crate::leanh::lean_box(0);
                            v_isShared_4869_ = v_isSharedCheck_4876_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4877_ = crate::leanh::lean_ctor_get(v_v_4856_, 0);
                        v_isSharedCheck_4887_ = (!crate::leanh::lean_is_exclusive(v_v_4856_)) as u8;
                        if v_isSharedCheck_4887_ == 0 {
                            v___x_4879_ = v_v_4856_;
                            v_isShared_4880_ = v_isSharedCheck_4887_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4877_);
                            crate::leanh::lean_dec(v_v_4856_);
                            v___x_4879_ = crate::leanh::lean_box(0);
                            v_isShared_4880_ = v_isSharedCheck_4887_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4888_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4888_, 0, v_x_4843_);
                        crate::leanh::lean_ctor_set(v___x_4888_, 1, v_x_4844_);
                        v___y_4860_ = v___x_4888_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4861_ = lean_array_fset(v_xs_x27_4858_, v_j_4850_, v___y_4860_);
                crate::leanh::lean_dec(v_j_4850_);
                if v_isShared_4855_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4854_, 0, v___x_4861_);
                    v___x_4863_ = v___x_4854_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4864_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 0, v___x_4861_);
                    v___x_4863_ = v_reuseFailAlloc_4864_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4863_;
            }
            4 => {
                v___x_4870_ = l_Lean_instBEqMVarId_beq(v_x_4843_, v_key_4865_);
                if v___x_4870_ == 0 {
                    crate::leanh::lean_del_object(v___x_4868_);
                    v___x_4871_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4865_,
                        v_val_4866_,
                        v_x_4843_,
                        v_x_4844_,
                    );
                    v___x_4872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4872_, 0, v___x_4871_);
                    v___y_4860_ = v___x_4872_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4866_);
                    crate::leanh::lean_dec(v_key_4865_);
                    if v_isShared_4869_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4868_, 1, v_x_4844_);
                        crate::leanh::lean_ctor_set(v___x_4868_, 0, v_x_4843_);
                        v___x_4874_ = v___x_4868_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_x_4843_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4875_, 1, v_x_4844_);
                        v___x_4874_ = v_reuseFailAlloc_4875_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4860_ = v___x_4874_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4881_ = lean_usize_shift_right(v_x_4841_, v___x_4846_);
                v___x_4882_ = lean_usize_add(v_x_4842_, v___x_4847_);
                v___x_4883_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_node_4877_, v___x_4881_, v___x_4882_, v_x_4843_, v_x_4844_);
                if v_isShared_4880_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4879_, 0, v___x_4883_);
                    v___x_4885_ = v___x_4879_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4886_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
                    v___x_4885_ = v_reuseFailAlloc_4886_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4860_ = v___x_4885_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4895_ == 0 {
                    v___x_4897_ = v___x_4894_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4911_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_ks_4891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 1, v_vs_4892_);
                    v___x_4897_ = v_reuseFailAlloc_4911_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4898_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v___x_4897_, v_x_4843_, v_x_4844_);
                v___x_4906_ = 7usize;
                v___x_4907_ = lean_usize_dec_le(v___x_4906_, v_x_4842_);
                if v___x_4907_ == 0 {
                    v___x_4908_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4898_);
                    v___x_4909_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4910_ = lean_nat_dec_lt(v___x_4908_, v___x_4909_);
                    crate::leanh::lean_dec(v___x_4908_);
                    v___y_4900_ = v___x_4910_;
                    state = 10;
                    continue;
                } else {
                    v___y_4900_ = v___x_4907_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4900_ == 0 {
                    v_ks_4901_ = crate::leanh::lean_ctor_get(v_newNode_4898_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4901_);
                    v_vs_4902_ = crate::leanh::lean_ctor_get(v_newNode_4898_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4902_);
                    crate::leanh::lean_dec_ref(v_newNode_4898_);
                    v___x_4903_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4904_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2);
                    v___x_4905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_x_4842_, v_ks_4901_, v_vs_4902_, v___x_4903_, v___x_4904_);
                    crate::leanh::lean_dec_ref(v_vs_4902_);
                    crate::leanh::lean_dec_ref(v_ks_4901_);
                    return v___x_4905_;
                } else {
                    return v_newNode_4898_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(
    mut v_depth_4913_: usize,
    mut v_keys_4914_: *mut crate::leanh::LeanObject,
    mut v_vals_4915_: *mut crate::leanh::LeanObject,
    mut v_i_4916_: *mut crate::leanh::LeanObject,
    mut v_entries_4917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: u8 = 0;
    let mut v_k_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: u64 = 0;
    let mut v_h_4923_: usize = 0;
    let mut v___x_4924_: usize = 0;
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: usize = 0;
    let mut v___x_4927_: usize = 0;
    let mut v___x_4928_: usize = 0;
    let mut v_h_4929_: usize = 0;
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4918_ = lean_array_get_size(v_keys_4914_);
                v___x_4919_ = lean_nat_dec_lt(v_i_4916_, v___x_4918_);
                if v___x_4919_ == 0 {
                    crate::leanh::lean_dec(v_i_4916_);
                    return v_entries_4917_;
                } else {
                    v_k_4920_ = lean_array_fget_borrowed(v_keys_4914_, v_i_4916_);
                    v_v_4921_ = lean_array_fget_borrowed(v_vals_4915_, v_i_4916_);
                    v___x_4922_ = l_Lean_instHashableMVarId_hash(v_k_4920_);
                    v_h_4923_ = lean_uint64_to_usize(v___x_4922_);
                    v___x_4924_ = 5usize;
                    v___x_4925_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4926_ = 1usize;
                    v___x_4927_ = lean_usize_sub(v_depth_4913_, v___x_4926_);
                    v___x_4928_ = lean_usize_mul(v___x_4924_, v___x_4927_);
                    v_h_4929_ = lean_usize_shift_right(v_h_4923_, v___x_4928_);
                    v___x_4930_ = lean_nat_add(v_i_4916_, v___x_4925_);
                    crate::leanh::lean_dec(v_i_4916_);
                    crate::leanh::lean_inc(v_v_4921_);
                    crate::leanh::lean_inc(v_k_4920_);
                    v___x_4931_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_entries_4917_, v_h_4929_, v_depth_4913_, v_k_4920_, v_v_4921_);
                    v_i_4916_ = v___x_4930_;
                    v_entries_4917_ = v___x_4931_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg___boxed(
    mut v_depth_4933_: *mut crate::leanh::LeanObject,
    mut v_keys_4934_: *mut crate::leanh::LeanObject,
    mut v_vals_4935_: *mut crate::leanh::LeanObject,
    mut v_i_4936_: *mut crate::leanh::LeanObject,
    mut v_entries_4937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4938_: usize = 0;
    let mut v_res_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4938_ = crate::leanh::lean_unbox_usize(v_depth_4933_);
    crate::leanh::lean_dec(v_depth_4933_);
    v_res_4939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_boxed_4938_, v_keys_4934_, v_vals_4935_, v_i_4936_, v_entries_4937_);
    crate::leanh::lean_dec_ref(v_vals_4935_);
    crate::leanh::lean_dec_ref(v_keys_4934_);
    return v_res_4939_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___boxed(
    mut v_x_4940_: *mut crate::leanh::LeanObject,
    mut v_x_4941_: *mut crate::leanh::LeanObject,
    mut v_x_4942_: *mut crate::leanh::LeanObject,
    mut v_x_4943_: *mut crate::leanh::LeanObject,
    mut v_x_4944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_22252__boxed_4945_: usize = 0;
    let mut v_x_22253__boxed_4946_: usize = 0;
    let mut v_res_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_22252__boxed_4945_ = crate::leanh::lean_unbox_usize(v_x_4941_);
    crate::leanh::lean_dec(v_x_4941_);
    v_x_22253__boxed_4946_ = crate::leanh::lean_unbox_usize(v_x_4942_);
    crate::leanh::lean_dec(v_x_4942_);
    v_res_4947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_4940_, v_x_22252__boxed_4945_, v_x_22253__boxed_4946_, v_x_4943_, v_x_4944_);
    return v_res_4947_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(
    mut v_x_4948_: *mut crate::leanh::LeanObject,
    mut v_x_4949_: *mut crate::leanh::LeanObject,
    mut v_x_4950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4951_: u64 = 0;
    let mut v___x_4952_: usize = 0;
    let mut v___x_4953_: usize = 0;
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4951_ = l_Lean_instHashableMVarId_hash(v_x_4949_);
    v___x_4952_ = lean_uint64_to_usize(v___x_4951_);
    v___x_4953_ = 1usize;
    v___x_4954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_4948_, v___x_4952_, v___x_4953_, v_x_4949_, v_x_4950_);
    return v___x_4954_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(
    mut v_mvarId_4955_: *mut crate::leanh::LeanObject,
    mut v_val_4956_: *mut crate::leanh::LeanObject,
    mut v___y_4957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4967_: u8 = 0;
    let mut v_depth_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4991_: u8 = 0;
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4959_ = lean_st_ref_take(v___y_4957_);
                v_mctx_4960_ = crate::leanh::lean_ctor_get(v___x_4959_, 0);
                v_cache_4961_ = crate::leanh::lean_ctor_get(v___x_4959_, 1);
                v_zetaDeltaFVarIds_4962_ = crate::leanh::lean_ctor_get(v___x_4959_, 2);
                v_postponed_4963_ = crate::leanh::lean_ctor_get(v___x_4959_, 3);
                v_diag_4964_ = crate::leanh::lean_ctor_get(v___x_4959_, 4);
                v_isSharedCheck_4992_ = (!crate::leanh::lean_is_exclusive(v___x_4959_)) as u8;
                if v_isSharedCheck_4992_ == 0 {
                    v___x_4966_ = v___x_4959_;
                    v_isShared_4967_ = v_isSharedCheck_4992_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4964_);
                    crate::leanh::lean_inc(v_postponed_4963_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4962_);
                    crate::leanh::lean_inc(v_cache_4961_);
                    crate::leanh::lean_inc(v_mctx_4960_);
                    crate::leanh::lean_dec(v___x_4959_);
                    v___x_4966_ = crate::leanh::lean_box(0);
                    v_isShared_4967_ = v_isSharedCheck_4992_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4968_ = crate::leanh::lean_ctor_get(v_mctx_4960_, 0);
                v_levelAssignDepth_4969_ = crate::leanh::lean_ctor_get(v_mctx_4960_, 1);
                v_lmvarCounter_4970_ = crate::leanh::lean_ctor_get(v_mctx_4960_, 2);
                v_mvarCounter_4971_ = crate::leanh::lean_ctor_get(v_mctx_4960_, 3);
                v_lDecls_4972_ = crate::leanh::lean_ctor_get(v_mctx_4960_, 4);
                v_decls_4973_ = crate::leanh::lean_ctor_get(v_mctx_4960_, 5);
                v_userNames_4974_ = crate::leanh::lean_ctor_get(v_mctx_4960_, 6);
                v_lAssignment_4975_ = crate::leanh::lean_ctor_get(v_mctx_4960_, 7);
                v_eAssignment_4976_ = crate::leanh::lean_ctor_get(v_mctx_4960_, 8);
                v_dAssignment_4977_ = crate::leanh::lean_ctor_get(v_mctx_4960_, 9);
                v_isSharedCheck_4991_ = (!crate::leanh::lean_is_exclusive(v_mctx_4960_)) as u8;
                if v_isSharedCheck_4991_ == 0 {
                    v___x_4979_ = v_mctx_4960_;
                    v_isShared_4980_ = v_isSharedCheck_4991_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_4977_);
                    crate::leanh::lean_inc(v_eAssignment_4976_);
                    crate::leanh::lean_inc(v_lAssignment_4975_);
                    crate::leanh::lean_inc(v_userNames_4974_);
                    crate::leanh::lean_inc(v_decls_4973_);
                    crate::leanh::lean_inc(v_lDecls_4972_);
                    crate::leanh::lean_inc(v_mvarCounter_4971_);
                    crate::leanh::lean_inc(v_lmvarCounter_4970_);
                    crate::leanh::lean_inc(v_levelAssignDepth_4969_);
                    crate::leanh::lean_inc(v_depth_4968_);
                    crate::leanh::lean_dec(v_mctx_4960_);
                    v___x_4979_ = crate::leanh::lean_box(0);
                    v_isShared_4980_ = v_isSharedCheck_4991_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4981_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_eAssignment_4976_, v_mvarId_4955_, v_val_4956_);
                if v_isShared_4980_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4979_, 8, v___x_4981_);
                    v___x_4983_ = v___x_4979_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4990_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_depth_4968_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4990_,
                        1,
                        v_levelAssignDepth_4969_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 2, v_lmvarCounter_4970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 3, v_mvarCounter_4971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 4, v_lDecls_4972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 5, v_decls_4973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 6, v_userNames_4974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 7, v_lAssignment_4975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 8, v___x_4981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4990_, 9, v_dAssignment_4977_);
                    v___x_4983_ = v_reuseFailAlloc_4990_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4967_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4966_, 0, v___x_4983_);
                    v___x_4985_ = v___x_4966_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4989_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4983_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 1, v_cache_4961_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4989_,
                        2,
                        v_zetaDeltaFVarIds_4962_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 3, v_postponed_4963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4989_, 4, v_diag_4964_);
                    v___x_4985_ = v_reuseFailAlloc_4989_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4986_ = lean_st_ref_set(v___y_4957_, v___x_4985_);
                v___x_4987_ = crate::leanh::lean_box(0);
                v___x_4988_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4988_, 0, v___x_4987_);
                return v___x_4988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg___boxed(
    mut v_mvarId_4993_: *mut crate::leanh::LeanObject,
    mut v_val_4994_: *mut crate::leanh::LeanObject,
    mut v___y_4995_: *mut crate::leanh::LeanObject,
    mut v___y_4996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4997_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_4993_, v_val_4994_, v___y_4995_);
    crate::leanh::lean_dec(v___y_4995_);
    return v_res_4997_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5004_ = crate::leanh::lean_box(0);
    v___x_5005_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3;
    v___x_5006_ = l_Lean_mkConst(v___x_5005_, v___x_5004_);
    return v___x_5006_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5011_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5012_ = l_Lean_Level_ofNat(v___x_5011_);
    return v___x_5012_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5013_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
    v___x_5014_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7);
    v___x_5015_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5015_, 0, v___x_5014_);
    crate::leanh::lean_ctor_set(v___x_5015_, 1, v___x_5013_);
    return v___x_5015_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5016_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8);
    v___x_5017_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6;
    v___x_5018_ = l_Lean_mkConst(v___x_5017_, v___x_5016_);
    return v___x_5018_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5019_ = crate::leanh::lean_box(0);
    v___x_5020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6;
    v___x_5021_ = l_Lean_mkConst(v___x_5020_, v___x_5019_);
    return v___x_5021_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5022_ = crate::leanh::lean_box(0);
    v___x_5023_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5024_ = lean_mk_array(v___x_5023_, v___x_5022_);
    return v___x_5024_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5025_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11);
    v___x_5026_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5027_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5027_, 0, v___x_5026_);
    crate::leanh::lean_ctor_set(v___x_5027_, 1, v___x_5025_);
    return v___x_5027_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5029_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13;
    v___x_5030_ = l_Lean_stringToMessageData(v___x_5029_);
    return v___x_5030_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4(
    mut v_fst_5031_: *mut crate::leanh::LeanObject,
    mut v_snd_5032_: *mut crate::leanh::LeanObject,
    mut v_goal_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
    mut v___y_5036_: *mut crate::leanh::LeanObject,
    mut v___y_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5041_: u8 = 0;
    let mut v___y_5042_: usize = 0;
    let mut v___y_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5045_: usize = 0;
    let mut v_a_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: u8 = 0;
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5077_: usize = 0;
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: u8 = 0;
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5090_: u8 = 0;
    let mut v_snd_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5095_: u8 = 0;
    let mut v_a_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5099_: u8 = 0;
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5103_: u8 = 0;
    let mut v_a_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5107_: u8 = 0;
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5111_: u8 = 0;
    let mut v_a_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5119_: u8 = 0;
    let mut v_a_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5123_: u8 = 0;
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5127_: u8 = 0;
    let mut v_a_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5131_: u8 = 0;
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5135_: u8 = 0;
    let mut v___y_5137_: usize = 0;
    let mut v___y_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: u8 = 0;
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5165_: u8 = 0;
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5184_: u8 = 0;
    let mut v_unused_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut v_unused_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5215_: u8 = 0;
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5224_: u8 = 0;
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5228_: u8 = 0;
    let mut v_reuseFailAlloc_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5230_: u8 = 0;
    let mut v_unused_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5234_: u8 = 0;
    let mut v_unused_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5243_: usize = 0;
    let mut v___x_5244_: usize = 0;
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: u8 = 0;
    let mut v___x_5250_: u8 = 0;
    let mut v___x_5251_: usize = 0;
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: usize = 0;
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: u8 = 0;
    let mut v___x_5262_: u8 = 0;
    let mut v___x_5263_: usize = 0;
    let mut v___x_5264_: usize = 0;
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: usize = 0;
    let mut v___x_5267_: usize = 0;
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5236_ = lean_st_ref_get(v___y_5034_);
                v_relevantHyps_5255_ = crate::leanh::lean_ctor_get(v___x_5236_, 1);
                crate::leanh::lean_inc_ref(v_relevantHyps_5255_);
                crate::leanh::lean_dec(v___x_5236_);
                v_size_5256_ = crate::leanh::lean_ctor_get(v_relevantHyps_5255_, 0);
                crate::leanh::lean_inc(v_size_5256_);
                v_buckets_5257_ = crate::leanh::lean_ctor_get(v_relevantHyps_5255_, 1);
                crate::leanh::lean_inc_ref(v_buckets_5257_);
                crate::leanh::lean_dec_ref(v_relevantHyps_5255_);
                v___x_5258_ = lean_mk_empty_array_with_capacity(v_size_5256_);
                crate::leanh::lean_dec(v_size_5256_);
                v___x_5259_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5260_ = lean_array_get_size(v_buckets_5257_);
                v___x_5261_ = lean_nat_dec_lt(v___x_5259_, v___x_5260_);
                if v___x_5261_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_5257_);
                    v___y_5238_ = v___x_5258_;
                    state = 25;
                    continue;
                } else {
                    v___x_5262_ = lean_nat_dec_le(v___x_5260_, v___x_5260_);
                    if v___x_5262_ == 0 {
                        if v___x_5261_ == 0 {
                            crate::leanh::lean_dec_ref(v_buckets_5257_);
                            v___y_5238_ = v___x_5258_;
                            state = 25;
                            continue;
                        } else {
                            v___x_5263_ = 0usize;
                            v___x_5264_ = lean_usize_of_nat(v___x_5260_);
                            v___x_5265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_5257_, v___x_5263_, v___x_5264_, v___x_5258_);
                            crate::leanh::lean_dec_ref(v_buckets_5257_);
                            v___y_5238_ = v___x_5265_;
                            state = 25;
                            continue;
                        }
                    } else {
                        v___x_5266_ = 0usize;
                        v___x_5267_ = lean_usize_of_nat(v___x_5260_);
                        v___x_5268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_5257_, v___x_5266_, v___x_5267_, v___x_5258_);
                        crate::leanh::lean_dec_ref(v_buckets_5257_);
                        v___y_5238_ = v___x_5268_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5047_ = crate::leanh::lean_ctor_get(v_a_5046_, 0);
                crate::leanh::lean_inc(v_fst_5047_);
                v_snd_5048_ = crate::leanh::lean_ctor_get(v_a_5046_, 1);
                crate::leanh::lean_inc(v_snd_5048_);
                crate::leanh::lean_dec_ref(v_a_5046_);
                v___x_5049_ = l_Lean_Expr_getAppFn(v_fst_5047_);
                crate::leanh::lean_dec(v_fst_5047_);
                v___x_5050_ = l_Lean_Expr_mvarId_x21(v___x_5049_);
                crate::leanh::lean_dec_ref(v___x_5049_);
                v___x_5051_ = l_Lean_MVarId_getType(
                    v___x_5050_,
                    v___y_5035_,
                    v___y_5036_,
                    v___y_5037_,
                    v___y_5038_,
                );
                if crate::leanh::lean_obj_tag(v___x_5051_) == 0 {
                    v_a_5052_ = crate::leanh::lean_ctor_get(v___x_5051_, 0);
                    crate::leanh::lean_inc(v_a_5052_);
                    crate::leanh::lean_dec_ref_known(v___x_5051_, 1);
                    v___x_5053_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1;
                    v___x_5054_ = crate::leanh::lean_box(0);
                    v___x_5055_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4);
                    v___x_5056_ = crate::leanh::lean_box_usize(v___y_5042_);
                    v___x_5057_ = crate::leanh::lean_box((v___y_5041_) as usize);
                    crate::leanh::lean_inc(v_fst_5031_);
                    v___f_5058_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___boxed as *mut core::ffi::c_void, 14, 7);
                    crate::leanh::lean_closure_set(v___f_5058_, 0, v___x_5054_);
                    crate::leanh::lean_closure_set(v___f_5058_, 1, v___y_5043_);
                    crate::leanh::lean_closure_set(v___f_5058_, 2, v___x_5056_);
                    crate::leanh::lean_closure_set(v___f_5058_, 3, v_a_5052_);
                    crate::leanh::lean_closure_set(v___f_5058_, 4, v___x_5057_);
                    crate::leanh::lean_closure_set(v___f_5058_, 5, v_fst_5031_);
                    crate::leanh::lean_closure_set(v___f_5058_, 6, v___x_5055_);
                    v___x_5059_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_5053_, v___x_5055_, v___f_5058_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
                    if crate::leanh::lean_obj_tag(v___x_5059_) == 0 {
                        v_a_5060_ = crate::leanh::lean_ctor_get(v___x_5059_, 0);
                        crate::leanh::lean_inc(v_a_5060_);
                        crate::leanh::lean_dec_ref_known(v___x_5059_, 1);
                        v_fst_5061_ = crate::leanh::lean_ctor_get(v_a_5060_, 0);
                        crate::leanh::lean_inc(v_fst_5061_);
                        v_snd_5062_ = crate::leanh::lean_ctor_get(v_a_5060_, 1);
                        crate::leanh::lean_inc(v_snd_5062_);
                        crate::leanh::lean_dec(v_a_5060_);
                        v___x_5063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5063_, 0, v_snd_5062_);
                        v___x_5064_ = 0;
                        v___x_5065_ = crate::leanh::lean_box(0);
                        v___x_5066_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_5063_,
                            v___x_5064_,
                            v___x_5065_,
                            v___y_5035_,
                            v___y_5036_,
                            v___y_5037_,
                            v___y_5038_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5066_) == 0 {
                            v_a_5067_ = crate::leanh::lean_ctor_get(v___x_5066_, 0);
                            crate::leanh::lean_inc(v_a_5067_);
                            crate::leanh::lean_dec_ref_known(v___x_5066_, 1);
                            v___x_5068_ = l_Lean_Expr_mvarId_x21(v_a_5067_);
                            crate::leanh::lean_dec(v_a_5067_);
                            v___x_5069_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9);
                            v___x_5070_ = l_Lean_mkNatLit(v_fst_5031_);
                            v___x_5071_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10);
                            crate::leanh::lean_inc(v___x_5068_);
                            v___x_5072_ = l_Lean_mkMVar(v___x_5068_);
                            v___x_5073_ = l_Lean_mkApp6(
                                v___x_5069_,
                                v___x_5055_,
                                v___x_5070_,
                                v_fst_5061_,
                                v___x_5071_,
                                v_snd_5032_,
                                v___x_5072_,
                            );
                            crate::leanh::lean_inc_ref(v___y_5044_);
                            v___x_5074_ = l_Array_append___redArg(v___y_5044_, v_snd_5048_);
                            v___x_5075_ = l_Lean_mkAppN(v___x_5073_, v___x_5074_);
                            crate::leanh::lean_dec_ref(v___x_5074_);
                            v___x_5076_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_goal_5033_, v___x_5075_, v___y_5036_);
                            crate::leanh::lean_dec_ref(v___x_5076_);
                            v_sz_5077_ = lean_array_size(v_snd_5048_);
                            crate::leanh::lean_inc(v_snd_5048_);
                            v___x_5078_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_5077_, v___y_5045_, v_snd_5048_);
                            v___x_5079_ = l_Lean_MVarId_tryClearMany_x27(
                                v___x_5068_,
                                v___x_5078_,
                                v___y_5035_,
                                v___y_5036_,
                                v___y_5037_,
                                v___y_5038_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5079_) == 0 {
                                v_a_5080_ = crate::leanh::lean_ctor_get(v___x_5079_, 0);
                                crate::leanh::lean_inc(v_a_5080_);
                                crate::leanh::lean_dec_ref_known(v___x_5079_, 1);
                                v_fst_5081_ = crate::leanh::lean_ctor_get(v_a_5080_, 0);
                                crate::leanh::lean_inc(v_fst_5081_);
                                crate::leanh::lean_dec(v_a_5080_);
                                v___x_5082_ = lean_array_get_size(v___y_5044_);
                                crate::leanh::lean_dec_ref(v___y_5044_);
                                v___x_5083_ = lean_array_get_size(v_snd_5048_);
                                crate::leanh::lean_dec(v_snd_5048_);
                                v___x_5084_ = lean_nat_add(v___x_5082_, v___x_5083_);
                                v___x_5085_ = 0;
                                v___x_5086_ = l_Lean_Meta_introNCore(
                                    v_fst_5081_,
                                    v___x_5084_,
                                    v___x_5054_,
                                    v___x_5085_,
                                    v___x_5085_,
                                    v___y_5035_,
                                    v___y_5036_,
                                    v___y_5037_,
                                    v___y_5038_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5086_) == 0 {
                                    v_a_5087_ = crate::leanh::lean_ctor_get(v___x_5086_, 0);
                                    v_isSharedCheck_5095_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5086_)) as u8;
                                    if v_isSharedCheck_5095_ == 0 {
                                        v___x_5089_ = v___x_5086_;
                                        v_isShared_5090_ = v_isSharedCheck_5095_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5087_);
                                        crate::leanh::lean_dec(v___x_5086_);
                                        v___x_5089_ = crate::leanh::lean_box(0);
                                        v_isShared_5090_ = v_isSharedCheck_5095_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_a_5096_ = crate::leanh::lean_ctor_get(v___x_5086_, 0);
                                    v_isSharedCheck_5103_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5086_)) as u8;
                                    if v_isSharedCheck_5103_ == 0 {
                                        v___x_5098_ = v___x_5086_;
                                        v_isShared_5099_ = v_isSharedCheck_5103_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5096_);
                                        crate::leanh::lean_dec(v___x_5086_);
                                        v___x_5098_ = crate::leanh::lean_box(0);
                                        v_isShared_5099_ = v_isSharedCheck_5103_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_5048_);
                                crate::leanh::lean_dec_ref(v___y_5044_);
                                v_a_5104_ = crate::leanh::lean_ctor_get(v___x_5079_, 0);
                                v_isSharedCheck_5111_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5079_)) as u8;
                                if v_isSharedCheck_5111_ == 0 {
                                    v___x_5106_ = v___x_5079_;
                                    v_isShared_5107_ = v_isSharedCheck_5111_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5104_);
                                    crate::leanh::lean_dec(v___x_5079_);
                                    v___x_5106_ = crate::leanh::lean_box(0);
                                    v_isShared_5107_ = v_isSharedCheck_5111_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_5061_);
                            crate::leanh::lean_dec(v_snd_5048_);
                            crate::leanh::lean_dec_ref(v___y_5044_);
                            crate::leanh::lean_dec(v_goal_5033_);
                            crate::leanh::lean_dec_ref(v_snd_5032_);
                            crate::leanh::lean_dec(v_fst_5031_);
                            v_a_5112_ = crate::leanh::lean_ctor_get(v___x_5066_, 0);
                            v_isSharedCheck_5119_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5066_)) as u8;
                            if v_isSharedCheck_5119_ == 0 {
                                v___x_5114_ = v___x_5066_;
                                v_isShared_5115_ = v_isSharedCheck_5119_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5112_);
                                crate::leanh::lean_dec(v___x_5066_);
                                v___x_5114_ = crate::leanh::lean_box(0);
                                v_isShared_5115_ = v_isSharedCheck_5119_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_5048_);
                        crate::leanh::lean_dec_ref(v___y_5044_);
                        crate::leanh::lean_dec(v_goal_5033_);
                        crate::leanh::lean_dec_ref(v_snd_5032_);
                        crate::leanh::lean_dec(v_fst_5031_);
                        v_a_5120_ = crate::leanh::lean_ctor_get(v___x_5059_, 0);
                        v_isSharedCheck_5127_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5059_)) as u8;
                        if v_isSharedCheck_5127_ == 0 {
                            v___x_5122_ = v___x_5059_;
                            v_isShared_5123_ = v_isSharedCheck_5127_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5120_);
                            crate::leanh::lean_dec(v___x_5059_);
                            v___x_5122_ = crate::leanh::lean_box(0);
                            v_isShared_5123_ = v_isSharedCheck_5127_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_5048_);
                    crate::leanh::lean_dec_ref(v___y_5044_);
                    crate::leanh::lean_dec_ref(v___y_5043_);
                    crate::leanh::lean_dec(v_goal_5033_);
                    crate::leanh::lean_dec_ref(v_snd_5032_);
                    crate::leanh::lean_dec(v_fst_5031_);
                    v_a_5128_ = crate::leanh::lean_ctor_get(v___x_5051_, 0);
                    v_isSharedCheck_5135_ = (!crate::leanh::lean_is_exclusive(v___x_5051_)) as u8;
                    if v_isSharedCheck_5135_ == 0 {
                        v___x_5130_ = v___x_5051_;
                        v_isShared_5131_ = v_isSharedCheck_5135_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5128_);
                        crate::leanh::lean_dec(v___x_5051_);
                        v___x_5130_ = crate::leanh::lean_box(0);
                        v_isShared_5131_ = v_isSharedCheck_5135_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_5091_ = crate::leanh::lean_ctor_get(v_a_5087_, 1);
                crate::leanh::lean_inc(v_snd_5091_);
                crate::leanh::lean_dec(v_a_5087_);
                if v_isShared_5090_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5089_, 0, v_snd_5091_);
                    v___x_5093_ = v___x_5089_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5094_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_snd_5091_);
                    v___x_5093_ = v_reuseFailAlloc_5094_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5093_;
            }
            4 => {
                if v_isShared_5099_ == 0 {
                    v___x_5101_ = v___x_5098_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5102_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5096_);
                    v___x_5101_ = v_reuseFailAlloc_5102_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5101_;
            }
            6 => {
                if v_isShared_5107_ == 0 {
                    v___x_5109_ = v___x_5106_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
                    v___x_5109_ = v_reuseFailAlloc_5110_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5109_;
            }
            8 => {
                if v_isShared_5115_ == 0 {
                    v___x_5117_ = v___x_5114_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
                    v___x_5117_ = v_reuseFailAlloc_5118_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5117_;
            }
            10 => {
                if v_isShared_5123_ == 0 {
                    v___x_5125_ = v___x_5122_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5120_);
                    v___x_5125_ = v_reuseFailAlloc_5126_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5125_;
            }
            12 => {
                if v_isShared_5131_ == 0 {
                    v___x_5133_ = v___x_5130_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5134_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_a_5128_);
                    v___x_5133_ = v_reuseFailAlloc_5134_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5133_;
            }
            14 => {
                v___x_5140_ = lean_st_ref_get(v___y_5036_);
                v___x_5141_ = lean_st_ref_get(v___y_5038_);
                v___x_5142_ = lean_st_ref_get(v___y_5038_);
                v_lctx_5143_ = crate::leanh::lean_ctor_get(v___y_5035_, 2);
                v_mctx_5144_ = crate::leanh::lean_ctor_get(v___x_5140_, 0);
                crate::leanh::lean_inc_ref(v_mctx_5144_);
                crate::leanh::lean_dec(v___x_5140_);
                v_ngen_5145_ = crate::leanh::lean_ctor_get(v___x_5141_, 2);
                crate::leanh::lean_inc_ref(v_ngen_5145_);
                crate::leanh::lean_dec(v___x_5141_);
                v_quotContext_5146_ = crate::leanh::lean_ctor_get(v___y_5037_, 10);
                v_nextMacroScope_5147_ = crate::leanh::lean_ctor_get(v___x_5142_, 1);
                crate::leanh::lean_inc(v_nextMacroScope_5147_);
                crate::leanh::lean_dec(v___x_5142_);
                v___x_5148_ = 1;
                crate::leanh::lean_inc_ref(v_lctx_5143_);
                crate::leanh::lean_inc(v_quotContext_5146_);
                v___x_5149_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5149_, 0, v_quotContext_5146_);
                crate::leanh::lean_ctor_set(v___x_5149_, 1, v_lctx_5143_);
                v___x_5150_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
                v___x_5151_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5151_, 0, v_mctx_5144_);
                crate::leanh::lean_ctor_set(v___x_5151_, 1, v_nextMacroScope_5147_);
                crate::leanh::lean_ctor_set(v___x_5151_, 2, v_ngen_5145_);
                crate::leanh::lean_ctor_set(v___x_5151_, 3, v___x_5150_);
                crate::leanh::lean_inc(v_goal_5033_);
                v___x_5152_ = l_Lean_MetavarContext_revert(
                    v___y_5138_,
                    v_goal_5033_,
                    v___x_5148_,
                    v___x_5149_,
                    v___x_5151_,
                );
                crate::leanh::lean_dec_ref_known(v___x_5149_, 2);
                crate::leanh::lean_dec_ref(v___y_5138_);
                if crate::leanh::lean_obj_tag(v___x_5152_) == 0 {
                    v_a_5153_ = crate::leanh::lean_ctor_get(v___x_5152_, 0);
                    crate::leanh::lean_inc(v_a_5153_);
                    v_a_5154_ = crate::leanh::lean_ctor_get(v___x_5152_, 1);
                    crate::leanh::lean_inc(v_a_5154_);
                    crate::leanh::lean_dec_ref_known(v___x_5152_, 2);
                    v___x_5155_ = lean_st_ref_take(v___y_5036_);
                    v_mctx_5156_ = crate::leanh::lean_ctor_get(v_a_5154_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5156_);
                    v_nextMacroScope_5157_ = crate::leanh::lean_ctor_get(v_a_5154_, 1);
                    crate::leanh::lean_inc(v_nextMacroScope_5157_);
                    v_ngen_5158_ = crate::leanh::lean_ctor_get(v_a_5154_, 2);
                    crate::leanh::lean_inc_ref(v_ngen_5158_);
                    crate::leanh::lean_dec(v_a_5154_);
                    v_cache_5159_ = crate::leanh::lean_ctor_get(v___x_5155_, 1);
                    v_zetaDeltaFVarIds_5160_ = crate::leanh::lean_ctor_get(v___x_5155_, 2);
                    v_postponed_5161_ = crate::leanh::lean_ctor_get(v___x_5155_, 3);
                    v_diag_5162_ = crate::leanh::lean_ctor_get(v___x_5155_, 4);
                    v_isSharedCheck_5188_ = (!crate::leanh::lean_is_exclusive(v___x_5155_)) as u8;
                    if v_isSharedCheck_5188_ == 0 {
                        v_unused_5189_ = crate::leanh::lean_ctor_get(v___x_5155_, 0);
                        crate::leanh::lean_dec(v_unused_5189_);
                        v___x_5164_ = v___x_5155_;
                        v_isShared_5165_ = v_isSharedCheck_5188_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5162_);
                        crate::leanh::lean_inc(v_postponed_5161_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5160_);
                        crate::leanh::lean_inc(v_cache_5159_);
                        crate::leanh::lean_dec(v___x_5155_);
                        v___x_5164_ = crate::leanh::lean_box(0);
                        v_isShared_5165_ = v_isSharedCheck_5188_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_5139_);
                    crate::leanh::lean_dec(v_goal_5033_);
                    crate::leanh::lean_dec_ref(v_snd_5032_);
                    crate::leanh::lean_dec(v_fst_5031_);
                    v_a_5190_ = crate::leanh::lean_ctor_get(v___x_5152_, 1);
                    crate::leanh::lean_inc(v_a_5190_);
                    crate::leanh::lean_dec_ref_known(v___x_5152_, 2);
                    v___x_5191_ = lean_st_ref_take(v___y_5036_);
                    v_mctx_5192_ = crate::leanh::lean_ctor_get(v_a_5190_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5192_);
                    v_nextMacroScope_5193_ = crate::leanh::lean_ctor_get(v_a_5190_, 1);
                    crate::leanh::lean_inc(v_nextMacroScope_5193_);
                    v_ngen_5194_ = crate::leanh::lean_ctor_get(v_a_5190_, 2);
                    crate::leanh::lean_inc_ref(v_ngen_5194_);
                    crate::leanh::lean_dec(v_a_5190_);
                    v_cache_5195_ = crate::leanh::lean_ctor_get(v___x_5191_, 1);
                    v_zetaDeltaFVarIds_5196_ = crate::leanh::lean_ctor_get(v___x_5191_, 2);
                    v_postponed_5197_ = crate::leanh::lean_ctor_get(v___x_5191_, 3);
                    v_diag_5198_ = crate::leanh::lean_ctor_get(v___x_5191_, 4);
                    v_isSharedCheck_5234_ = (!crate::leanh::lean_is_exclusive(v___x_5191_)) as u8;
                    if v_isSharedCheck_5234_ == 0 {
                        v_unused_5235_ = crate::leanh::lean_ctor_get(v___x_5191_, 0);
                        crate::leanh::lean_dec(v_unused_5235_);
                        v___x_5200_ = v___x_5191_;
                        v_isShared_5201_ = v_isSharedCheck_5234_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5198_);
                        crate::leanh::lean_inc(v_postponed_5197_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5196_);
                        crate::leanh::lean_inc(v_cache_5195_);
                        crate::leanh::lean_dec(v___x_5191_);
                        v___x_5200_ = crate::leanh::lean_box(0);
                        v_isShared_5201_ = v_isSharedCheck_5234_;
                        state = 19;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_5165_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5164_, 0, v_mctx_5156_);
                    v___x_5167_ = v___x_5164_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5187_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_mctx_5156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 1, v_cache_5159_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5187_,
                        2,
                        v_zetaDeltaFVarIds_5160_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 3, v_postponed_5161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 4, v_diag_5162_);
                    v___x_5167_ = v_reuseFailAlloc_5187_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_5168_ = lean_st_ref_set(v___y_5036_, v___x_5167_);
                v___x_5169_ = lean_st_ref_take(v___y_5038_);
                v_env_5170_ = crate::leanh::lean_ctor_get(v___x_5169_, 0);
                v_auxDeclNGen_5171_ = crate::leanh::lean_ctor_get(v___x_5169_, 3);
                v_traceState_5172_ = crate::leanh::lean_ctor_get(v___x_5169_, 4);
                v_cache_5173_ = crate::leanh::lean_ctor_get(v___x_5169_, 5);
                v_messages_5174_ = crate::leanh::lean_ctor_get(v___x_5169_, 6);
                v_infoState_5175_ = crate::leanh::lean_ctor_get(v___x_5169_, 7);
                v_snapshotTasks_5176_ = crate::leanh::lean_ctor_get(v___x_5169_, 8);
                v_isSharedCheck_5184_ = (!crate::leanh::lean_is_exclusive(v___x_5169_)) as u8;
                if v_isSharedCheck_5184_ == 0 {
                    v_unused_5185_ = crate::leanh::lean_ctor_get(v___x_5169_, 2);
                    crate::leanh::lean_dec(v_unused_5185_);
                    v_unused_5186_ = crate::leanh::lean_ctor_get(v___x_5169_, 1);
                    crate::leanh::lean_dec(v_unused_5186_);
                    v___x_5178_ = v___x_5169_;
                    v_isShared_5179_ = v_isSharedCheck_5184_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5176_);
                    crate::leanh::lean_inc(v_infoState_5175_);
                    crate::leanh::lean_inc(v_messages_5174_);
                    crate::leanh::lean_inc(v_cache_5173_);
                    crate::leanh::lean_inc(v_traceState_5172_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5171_);
                    crate::leanh::lean_inc(v_env_5170_);
                    crate::leanh::lean_dec(v___x_5169_);
                    v___x_5178_ = crate::leanh::lean_box(0);
                    v_isShared_5179_ = v_isSharedCheck_5184_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_5179_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5178_, 2, v_ngen_5158_);
                    crate::leanh::lean_ctor_set(v___x_5178_, 1, v_nextMacroScope_5157_);
                    v___x_5181_ = v___x_5178_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5183_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_env_5170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 1, v_nextMacroScope_5157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 2, v_ngen_5158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 3, v_auxDeclNGen_5171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 4, v_traceState_5172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 5, v_cache_5173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 6, v_messages_5174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 7, v_infoState_5175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 8, v_snapshotTasks_5176_);
                    v___x_5181_ = v_reuseFailAlloc_5183_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_5182_ = lean_st_ref_set(v___y_5038_, v___x_5181_);
                crate::leanh::lean_inc_ref(v___y_5139_);
                v___y_5041_ = v___x_5148_;
                v___y_5042_ = v___y_5137_;
                v___y_5043_ = v___y_5139_;
                v___y_5044_ = v___y_5139_;
                v___y_5045_ = v___y_5137_;
                v_a_5046_ = v_a_5153_;
                state = 1;
                continue;
            }
            19 => {
                if v_isShared_5201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5200_, 0, v_mctx_5192_);
                    v___x_5203_ = v___x_5200_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5233_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_mctx_5192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 1, v_cache_5195_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5233_,
                        2,
                        v_zetaDeltaFVarIds_5196_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 3, v_postponed_5197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5233_, 4, v_diag_5198_);
                    v___x_5203_ = v_reuseFailAlloc_5233_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_5204_ = lean_st_ref_set(v___y_5036_, v___x_5203_);
                v___x_5205_ = lean_st_ref_take(v___y_5038_);
                v_env_5206_ = crate::leanh::lean_ctor_get(v___x_5205_, 0);
                v_auxDeclNGen_5207_ = crate::leanh::lean_ctor_get(v___x_5205_, 3);
                v_traceState_5208_ = crate::leanh::lean_ctor_get(v___x_5205_, 4);
                v_cache_5209_ = crate::leanh::lean_ctor_get(v___x_5205_, 5);
                v_messages_5210_ = crate::leanh::lean_ctor_get(v___x_5205_, 6);
                v_infoState_5211_ = crate::leanh::lean_ctor_get(v___x_5205_, 7);
                v_snapshotTasks_5212_ = crate::leanh::lean_ctor_get(v___x_5205_, 8);
                v_isSharedCheck_5230_ = (!crate::leanh::lean_is_exclusive(v___x_5205_)) as u8;
                if v_isSharedCheck_5230_ == 0 {
                    v_unused_5231_ = crate::leanh::lean_ctor_get(v___x_5205_, 2);
                    crate::leanh::lean_dec(v_unused_5231_);
                    v_unused_5232_ = crate::leanh::lean_ctor_get(v___x_5205_, 1);
                    crate::leanh::lean_dec(v_unused_5232_);
                    v___x_5214_ = v___x_5205_;
                    v_isShared_5215_ = v_isSharedCheck_5230_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5212_);
                    crate::leanh::lean_inc(v_infoState_5211_);
                    crate::leanh::lean_inc(v_messages_5210_);
                    crate::leanh::lean_inc(v_cache_5209_);
                    crate::leanh::lean_inc(v_traceState_5208_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5207_);
                    crate::leanh::lean_inc(v_env_5206_);
                    crate::leanh::lean_dec(v___x_5205_);
                    v___x_5214_ = crate::leanh::lean_box(0);
                    v_isShared_5215_ = v_isSharedCheck_5230_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_5215_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5214_, 2, v_ngen_5194_);
                    crate::leanh::lean_ctor_set(v___x_5214_, 1, v_nextMacroScope_5193_);
                    v___x_5217_ = v___x_5214_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5229_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_env_5206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 1, v_nextMacroScope_5193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 2, v_ngen_5194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 3, v_auxDeclNGen_5207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 4, v_traceState_5208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 5, v_cache_5209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 6, v_messages_5210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 7, v_infoState_5211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 8, v_snapshotTasks_5212_);
                    v___x_5217_ = v_reuseFailAlloc_5229_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_5218_ = lean_st_ref_set(v___y_5038_, v___x_5217_);
                v___x_5219_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14);
                v___x_5220_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v___x_5219_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
                v_a_5221_ = crate::leanh::lean_ctor_get(v___x_5220_, 0);
                v_isSharedCheck_5228_ = (!crate::leanh::lean_is_exclusive(v___x_5220_)) as u8;
                if v_isSharedCheck_5228_ == 0 {
                    v___x_5223_ = v___x_5220_;
                    v_isShared_5224_ = v_isSharedCheck_5228_;
                    state = 23;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5221_);
                    crate::leanh::lean_dec(v___x_5220_);
                    v___x_5223_ = crate::leanh::lean_box(0);
                    v_isShared_5224_ = v_isSharedCheck_5228_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_5224_ == 0 {
                    v___x_5226_ = v___x_5223_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
                    v___x_5226_ = v_reuseFailAlloc_5227_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5226_;
            }
            25 => {
                v___x_5239_ = lean_st_ref_get(v___y_5034_);
                v_relevantTerms_5240_ = crate::leanh::lean_ctor_get(v___x_5239_, 0);
                crate::leanh::lean_inc_ref(v_relevantTerms_5240_);
                crate::leanh::lean_dec(v___x_5239_);
                v_size_5241_ = crate::leanh::lean_ctor_get(v_relevantTerms_5240_, 0);
                crate::leanh::lean_inc(v_size_5241_);
                v_buckets_5242_ = crate::leanh::lean_ctor_get(v_relevantTerms_5240_, 1);
                crate::leanh::lean_inc_ref(v_buckets_5242_);
                crate::leanh::lean_dec_ref(v_relevantTerms_5240_);
                v_sz_5243_ = lean_array_size(v___y_5238_);
                v___x_5244_ = 0usize;
                v___x_5245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_5243_, v___x_5244_, v___y_5238_);
                v___x_5246_ = lean_mk_empty_array_with_capacity(v_size_5241_);
                crate::leanh::lean_dec(v_size_5241_);
                v___x_5247_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5248_ = lean_array_get_size(v_buckets_5242_);
                v___x_5249_ = lean_nat_dec_lt(v___x_5247_, v___x_5248_);
                if v___x_5249_ == 0 {
                    crate::leanh::lean_dec_ref(v_buckets_5242_);
                    v___y_5137_ = v___x_5244_;
                    v___y_5138_ = v___x_5245_;
                    v___y_5139_ = v___x_5246_;
                    state = 14;
                    continue;
                } else {
                    v___x_5250_ = lean_nat_dec_le(v___x_5248_, v___x_5248_);
                    if v___x_5250_ == 0 {
                        if v___x_5249_ == 0 {
                            crate::leanh::lean_dec_ref(v_buckets_5242_);
                            v___y_5137_ = v___x_5244_;
                            v___y_5138_ = v___x_5245_;
                            v___y_5139_ = v___x_5246_;
                            state = 14;
                            continue;
                        } else {
                            v___x_5251_ = lean_usize_of_nat(v___x_5248_);
                            v___x_5252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_5242_, v___x_5244_, v___x_5251_, v___x_5246_);
                            crate::leanh::lean_dec_ref(v_buckets_5242_);
                            v___y_5137_ = v___x_5244_;
                            v___y_5138_ = v___x_5245_;
                            v___y_5139_ = v___x_5252_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___x_5253_ = lean_usize_of_nat(v___x_5248_);
                        v___x_5254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_5242_, v___x_5244_, v___x_5253_, v___x_5246_);
                        crate::leanh::lean_dec_ref(v_buckets_5242_);
                        v___y_5137_ = v___x_5244_;
                        v___y_5138_ = v___x_5245_;
                        v___y_5139_ = v___x_5254_;
                        state = 14;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___boxed(
    mut v_fst_5269_: *mut crate::leanh::LeanObject,
    mut v_snd_5270_: *mut crate::leanh::LeanObject,
    mut v_goal_5271_: *mut crate::leanh::LeanObject,
    mut v___y_5272_: *mut crate::leanh::LeanObject,
    mut v___y_5273_: *mut crate::leanh::LeanObject,
    mut v___y_5274_: *mut crate::leanh::LeanObject,
    mut v___y_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5278_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4(v_fst_5269_, v_snd_5270_, v_goal_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
    crate::leanh::lean_dec(v___y_5276_);
    crate::leanh::lean_dec_ref(v___y_5275_);
    crate::leanh::lean_dec(v___y_5274_);
    crate::leanh::lean_dec_ref(v___y_5273_);
    crate::leanh::lean_dec(v___y_5272_);
    return v_res_5278_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(
    mut v___y_5287_: u8,
    mut v_suppressElabErrors_5288_: u8,
    mut v_x_5289_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5289_) == 1 {
        let mut v_pre_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_5290_ = crate::leanh::lean_ctor_get(v_x_5289_, 0);
        match crate::leanh::lean_obj_tag(v_pre_5290_) {
            1 => {
                let mut v_pre_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_5291_ = crate::leanh::lean_ctor_get(v_pre_5290_, 0);
                match crate::leanh::lean_obj_tag(v_pre_5291_) {
                    0 => {
                        let mut v_str_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5295_: u8 = 0;
                        v_str_5292_ = crate::leanh::lean_ctor_get(v_x_5289_, 1);
                        v_str_5293_ = crate::leanh::lean_ctor_get(v_pre_5290_, 1);
                        v___x_5294_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0;
                        v___x_5295_ = lean_string_dec_eq(v_str_5293_, v___x_5294_);
                        if v___x_5295_ == 0 {
                            let mut v___x_5296_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5297_: u8 = 0;
                            v___x_5296_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1;
                            v___x_5297_ = lean_string_dec_eq(v_str_5293_, v___x_5296_);
                            if v___x_5297_ == 0 {
                                return v___y_5287_;
                            } else {
                                let mut v___x_5298_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5299_: u8 = 0;
                                v___x_5298_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2;
                                v___x_5299_ = lean_string_dec_eq(v_str_5292_, v___x_5298_);
                                if v___x_5299_ == 0 {
                                    return v___y_5287_;
                                } else {
                                    return v_suppressElabErrors_5288_;
                                }
                            }
                        } else {
                            let mut v___x_5300_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5301_: u8 = 0;
                            v___x_5300_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3;
                            v___x_5301_ = lean_string_dec_eq(v_str_5292_, v___x_5300_);
                            if v___x_5301_ == 0 {
                                return v___y_5287_;
                            } else {
                                return v_suppressElabErrors_5288_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_5302_ = crate::leanh::lean_ctor_get(v_pre_5291_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_5302_) == 0 {
                            let mut v_str_5303_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5304_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5305_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5306_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5307_: u8 = 0;
                            v_str_5303_ = crate::leanh::lean_ctor_get(v_x_5289_, 1);
                            v_str_5304_ = crate::leanh::lean_ctor_get(v_pre_5290_, 1);
                            v_str_5305_ = crate::leanh::lean_ctor_get(v_pre_5291_, 1);
                            v___x_5306_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4;
                            v___x_5307_ = lean_string_dec_eq(v_str_5305_, v___x_5306_);
                            if v___x_5307_ == 0 {
                                return v___y_5287_;
                            } else {
                                let mut v___x_5308_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5309_: u8 = 0;
                                v___x_5308_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5;
                                v___x_5309_ = lean_string_dec_eq(v_str_5304_, v___x_5308_);
                                if v___x_5309_ == 0 {
                                    return v___y_5287_;
                                } else {
                                    let mut v___x_5310_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_5311_: u8 = 0;
                                    v___x_5310_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6;
                                    v___x_5311_ = lean_string_dec_eq(v_str_5303_, v___x_5310_);
                                    if v___x_5311_ == 0 {
                                        return v___y_5287_;
                                    } else {
                                        return v_suppressElabErrors_5288_;
                                    }
                                }
                            }
                        } else {
                            return v___y_5287_;
                        }
                    }
                    _ => {
                        return v___y_5287_;
                    }
                }
            }
            0 => {
                let mut v_str_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5314_: u8 = 0;
                v_str_5312_ = crate::leanh::lean_ctor_get(v_x_5289_, 1);
                v___x_5313_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7;
                v___x_5314_ = lean_string_dec_eq(v_str_5312_, v___x_5313_);
                if v___x_5314_ == 0 {
                    return v___y_5287_;
                } else {
                    return v_suppressElabErrors_5288_;
                }
            }
            _ => {
                return v___y_5287_;
            }
        }
    } else {
        return v___y_5287_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed(
    mut v___y_5315_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_5316_: *mut crate::leanh::LeanObject,
    mut v_x_5317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_23009__boxed_5318_: u8 = 0;
    let mut v_suppressElabErrors_boxed_5319_: u8 = 0;
    let mut v_res_5320_: u8 = 0;
    let mut v_r_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_23009__boxed_5318_ = (crate::leanh::lean_unbox(v___y_5315_) as u8);
    v_suppressElabErrors_boxed_5319_ = (crate::leanh::lean_unbox(v_suppressElabErrors_5316_) as u8);
    v_res_5320_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(v___y_23009__boxed_5318_, v_suppressElabErrors_boxed_5319_, v_x_5317_);
    crate::leanh::lean_dec(v_x_5317_);
    v_r_5321_ = crate::leanh::lean_box((v_res_5320_) as usize);
    return v_r_5321_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(
    mut v_opts_5322_: *mut crate::leanh::LeanObject,
    mut v_opt_5323_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5324_ = crate::leanh::lean_ctor_get(v_opt_5323_, 0);
    v_defValue_5325_ = crate::leanh::lean_ctor_get(v_opt_5323_, 1);
    v_map_5326_ = crate::leanh::lean_ctor_get(v_opts_5322_, 0);
    v___x_5327_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5326_,
            v_name_5324_,
        );
    if crate::leanh::lean_obj_tag(v___x_5327_) == 0 {
        let mut v___x_5328_: u8 = 0;
        v___x_5328_ = (crate::leanh::lean_unbox(v_defValue_5325_) as u8);
        return v___x_5328_;
    } else {
        let mut v_val_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5329_ = crate::leanh::lean_ctor_get(v___x_5327_, 0);
        crate::leanh::lean_inc(v_val_5329_);
        crate::leanh::lean_dec_ref_known(v___x_5327_, 1);
        if crate::leanh::lean_obj_tag(v_val_5329_) == 1 {
            let mut v_v_5330_: u8 = 0;
            v_v_5330_ = crate::leanh::lean_ctor_get_uint8(v_val_5329_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_5329_, 0);
            return v_v_5330_;
        } else {
            let mut v___x_5331_: u8 = 0;
            crate::leanh::lean_dec(v_val_5329_);
            v___x_5331_ = (crate::leanh::lean_unbox(v_defValue_5325_) as u8);
            return v___x_5331_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34___boxed(
    mut v_opts_5332_: *mut crate::leanh::LeanObject,
    mut v_opt_5333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5334_: u8 = 0;
    let mut v_r_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5334_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_opts_5332_, v_opt_5333_);
    crate::leanh::lean_dec_ref(v_opt_5333_);
    crate::leanh::lean_dec_ref(v_opts_5332_);
    v_r_5335_ = crate::leanh::lean_box((v_res_5334_) as usize);
    return v_r_5335_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(
    mut v_ref_5337_: *mut crate::leanh::LeanObject,
    mut v_msgData_5338_: *mut crate::leanh::LeanObject,
    mut v_severity_5339_: u8,
    mut v_isSilent_5340_: u8,
    mut v___y_5341_: *mut crate::leanh::LeanObject,
    mut v___y_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5350_: u8 = 0;
    let mut v___y_5351_: u8 = 0;
    let mut v___y_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5370_: u8 = 0;
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5381_: u8 = 0;
    let mut v___y_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5385_: u8 = 0;
    let mut v___y_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5388_: u8 = 0;
    let mut v___y_5389_: u8 = 0;
    let mut v___y_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: u8 = 0;
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5406_: u8 = 0;
    let mut v___y_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5410_: u8 = 0;
    let mut v___y_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5413_: u8 = 0;
    let mut v___y_5414_: u8 = 0;
    let mut v___y_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5421_: u8 = 0;
    let mut v___y_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5424_: u8 = 0;
    let mut v___y_5425_: u8 = 0;
    let mut v_ref_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: u8 = 0;
    let mut v___y_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5433_: u8 = 0;
    let mut v___y_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5437_: u8 = 0;
    let mut v___y_5438_: u8 = 0;
    let mut v___y_5440_: u8 = 0;
    let mut v_fileName_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5445_: u8 = 0;
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: u8 = 0;
    let mut v___x_5450_: u8 = 0;
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: u8 = 0;
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: u8 = 0;
    let mut v___x_5456_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5430_ = 2;
                v___x_5455_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5339_, v___x_5430_);
                if v___x_5455_ == 0 {
                    v___y_5440_ = v___x_5455_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_5338_);
                    v___x_5456_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5338_);
                    v___y_5440_ = v___x_5456_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5356_ = lean_st_ref_take(v___y_5355_);
                v_currNamespace_5357_ = crate::leanh::lean_ctor_get(v___y_5354_, 6);
                v_openDecls_5358_ = crate::leanh::lean_ctor_get(v___y_5354_, 7);
                v_env_5359_ = crate::leanh::lean_ctor_get(v___x_5356_, 0);
                v_nextMacroScope_5360_ = crate::leanh::lean_ctor_get(v___x_5356_, 1);
                v_ngen_5361_ = crate::leanh::lean_ctor_get(v___x_5356_, 2);
                v_auxDeclNGen_5362_ = crate::leanh::lean_ctor_get(v___x_5356_, 3);
                v_traceState_5363_ = crate::leanh::lean_ctor_get(v___x_5356_, 4);
                v_cache_5364_ = crate::leanh::lean_ctor_get(v___x_5356_, 5);
                v_messages_5365_ = crate::leanh::lean_ctor_get(v___x_5356_, 6);
                v_infoState_5366_ = crate::leanh::lean_ctor_get(v___x_5356_, 7);
                v_snapshotTasks_5367_ = crate::leanh::lean_ctor_get(v___x_5356_, 8);
                v_isSharedCheck_5381_ = (!crate::leanh::lean_is_exclusive(v___x_5356_)) as u8;
                if v_isSharedCheck_5381_ == 0 {
                    v___x_5369_ = v___x_5356_;
                    v_isShared_5370_ = v_isSharedCheck_5381_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5367_);
                    crate::leanh::lean_inc(v_infoState_5366_);
                    crate::leanh::lean_inc(v_messages_5365_);
                    crate::leanh::lean_inc(v_cache_5364_);
                    crate::leanh::lean_inc(v_traceState_5363_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5362_);
                    crate::leanh::lean_inc(v_ngen_5361_);
                    crate::leanh::lean_inc(v_nextMacroScope_5360_);
                    crate::leanh::lean_inc(v_env_5359_);
                    crate::leanh::lean_dec(v___x_5356_);
                    v___x_5369_ = crate::leanh::lean_box(0);
                    v_isShared_5370_ = v_isSharedCheck_5381_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_5358_);
                crate::leanh::lean_inc(v_currNamespace_5357_);
                v___x_5371_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5371_, 0, v_currNamespace_5357_);
                crate::leanh::lean_ctor_set(v___x_5371_, 1, v_openDecls_5358_);
                v___x_5372_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5372_, 0, v___x_5371_);
                crate::leanh::lean_ctor_set(v___x_5372_, 1, v___y_5353_);
                crate::leanh::lean_inc_ref(v___y_5347_);
                crate::leanh::lean_inc_ref(v___y_5348_);
                v___x_5373_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_5373_, 0, v___y_5348_);
                crate::leanh::lean_ctor_set(v___x_5373_, 1, v___y_5352_);
                crate::leanh::lean_ctor_set(v___x_5373_, 2, v___y_5349_);
                crate::leanh::lean_ctor_set(v___x_5373_, 3, v___y_5347_);
                crate::leanh::lean_ctor_set(v___x_5373_, 4, v___x_5372_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5373_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_5350_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5373_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_5351_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5373_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5340_,
                );
                v___x_5374_ = l_Lean_MessageLog_add(v___x_5373_, v_messages_5365_);
                if v_isShared_5370_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5369_, 6, v___x_5374_);
                    v___x_5376_ = v___x_5369_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5380_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_env_5359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 1, v_nextMacroScope_5360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 2, v_ngen_5361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 3, v_auxDeclNGen_5362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 4, v_traceState_5363_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 5, v_cache_5364_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 6, v___x_5374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 7, v_infoState_5366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 8, v_snapshotTasks_5367_);
                    v___x_5376_ = v_reuseFailAlloc_5380_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5377_ = lean_st_ref_set(v___y_5355_, v___x_5376_);
                v___x_5378_ = crate::leanh::lean_box(0);
                v___x_5379_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5379_, 0, v___x_5378_);
                return v___x_5379_;
            }
            4 => {
                v___x_5391_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5338_,
                    );
                v___x_5392_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v___x_5391_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_);
                v_a_5393_ = crate::leanh::lean_ctor_get(v___x_5392_, 0);
                v_isSharedCheck_5406_ = (!crate::leanh::lean_is_exclusive(v___x_5392_)) as u8;
                if v_isSharedCheck_5406_ == 0 {
                    v___x_5395_ = v___x_5392_;
                    v_isShared_5396_ = v_isSharedCheck_5406_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5393_);
                    crate::leanh::lean_dec(v___x_5392_);
                    v___x_5395_ = crate::leanh::lean_box(0);
                    v_isShared_5396_ = v_isSharedCheck_5406_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_5387_, 2);
                v___x_5397_ = l_Lean_FileMap_toPosition(v___y_5387_, v___y_5384_);
                crate::leanh::lean_dec(v___y_5384_);
                v___x_5398_ = l_Lean_FileMap_toPosition(v___y_5387_, v___y_5390_);
                crate::leanh::lean_dec(v___y_5390_);
                v___x_5399_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5399_, 0, v___x_5398_);
                v___x_5400_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0;
                if v___y_5385_ == 0 {
                    crate::leanh::lean_del_object(v___x_5395_);
                    crate::leanh::lean_dec_ref(v___y_5383_);
                    v___y_5347_ = v___x_5400_;
                    v___y_5348_ = v___y_5386_;
                    v___y_5349_ = v___x_5399_;
                    v___y_5350_ = v___y_5388_;
                    v___y_5351_ = v___y_5389_;
                    v___y_5352_ = v___x_5397_;
                    v___y_5353_ = v_a_5393_;
                    v___y_5354_ = v___y_5343_;
                    v___y_5355_ = v___y_5344_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5393_);
                    v___x_5401_ = l_Lean_MessageData_hasTag(v___y_5383_, v_a_5393_);
                    if v___x_5401_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5399_, 1);
                        crate::leanh::lean_dec_ref(v___x_5397_);
                        crate::leanh::lean_dec(v_a_5393_);
                        v___x_5402_ = crate::leanh::lean_box(0);
                        if v_isShared_5396_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5395_, 0, v___x_5402_);
                            v___x_5404_ = v___x_5395_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5405_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5402_);
                            v___x_5404_ = v_reuseFailAlloc_5405_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5395_);
                        v___y_5347_ = v___x_5400_;
                        v___y_5348_ = v___y_5386_;
                        v___y_5349_ = v___x_5399_;
                        v___y_5350_ = v___y_5388_;
                        v___y_5351_ = v___y_5389_;
                        v___y_5352_ = v___x_5397_;
                        v___y_5353_ = v_a_5393_;
                        v___y_5354_ = v___y_5343_;
                        v___y_5355_ = v___y_5344_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_5404_;
            }
            7 => {
                v___x_5416_ = l_Lean_Syntax_getTailPos_x3f(v___y_5409_, v___y_5413_);
                crate::leanh::lean_dec(v___y_5409_);
                if crate::leanh::lean_obj_tag(v___x_5416_) == 0 {
                    crate::leanh::lean_inc(v___y_5415_);
                    v___y_5383_ = v___y_5408_;
                    v___y_5384_ = v___y_5415_;
                    v___y_5385_ = v___y_5410_;
                    v___y_5386_ = v___y_5412_;
                    v___y_5387_ = v___y_5411_;
                    v___y_5388_ = v___y_5413_;
                    v___y_5389_ = v___y_5414_;
                    v___y_5390_ = v___y_5415_;
                    state = 4;
                    continue;
                } else {
                    v_val_5417_ = crate::leanh::lean_ctor_get(v___x_5416_, 0);
                    crate::leanh::lean_inc(v_val_5417_);
                    crate::leanh::lean_dec_ref_known(v___x_5416_, 1);
                    v___y_5383_ = v___y_5408_;
                    v___y_5384_ = v___y_5415_;
                    v___y_5385_ = v___y_5410_;
                    v___y_5386_ = v___y_5412_;
                    v___y_5387_ = v___y_5411_;
                    v___y_5388_ = v___y_5413_;
                    v___y_5389_ = v___y_5414_;
                    v___y_5390_ = v_val_5417_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_5426_ = l_Lean_replaceRef(v_ref_5337_, v___y_5420_);
                v___x_5427_ = l_Lean_Syntax_getPos_x3f(v_ref_5426_, v___y_5424_);
                if crate::leanh::lean_obj_tag(v___x_5427_) == 0 {
                    v___x_5428_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5408_ = v___y_5419_;
                    v___y_5409_ = v_ref_5426_;
                    v___y_5410_ = v___y_5421_;
                    v___y_5411_ = v___y_5423_;
                    v___y_5412_ = v___y_5422_;
                    v___y_5413_ = v___y_5424_;
                    v___y_5414_ = v___y_5425_;
                    v___y_5415_ = v___x_5428_;
                    state = 7;
                    continue;
                } else {
                    v_val_5429_ = crate::leanh::lean_ctor_get(v___x_5427_, 0);
                    crate::leanh::lean_inc(v_val_5429_);
                    crate::leanh::lean_dec_ref_known(v___x_5427_, 1);
                    v___y_5408_ = v___y_5419_;
                    v___y_5409_ = v_ref_5426_;
                    v___y_5410_ = v___y_5421_;
                    v___y_5411_ = v___y_5423_;
                    v___y_5412_ = v___y_5422_;
                    v___y_5413_ = v___y_5424_;
                    v___y_5414_ = v___y_5425_;
                    v___y_5415_ = v_val_5429_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_5438_ == 0 {
                    v___y_5419_ = v___y_5436_;
                    v___y_5420_ = v___y_5432_;
                    v___y_5421_ = v___y_5433_;
                    v___y_5422_ = v___y_5435_;
                    v___y_5423_ = v___y_5434_;
                    v___y_5424_ = v___y_5437_;
                    v___y_5425_ = v_severity_5339_;
                    state = 8;
                    continue;
                } else {
                    v___y_5419_ = v___y_5436_;
                    v___y_5420_ = v___y_5432_;
                    v___y_5421_ = v___y_5433_;
                    v___y_5422_ = v___y_5435_;
                    v___y_5423_ = v___y_5434_;
                    v___y_5424_ = v___y_5437_;
                    v___y_5425_ = v___x_5430_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_5440_ == 0 {
                    v_fileName_5441_ = crate::leanh::lean_ctor_get(v___y_5343_, 0);
                    v_fileMap_5442_ = crate::leanh::lean_ctor_get(v___y_5343_, 1);
                    v_options_5443_ = crate::leanh::lean_ctor_get(v___y_5343_, 2);
                    v_ref_5444_ = crate::leanh::lean_ctor_get(v___y_5343_, 5);
                    v_suppressElabErrors_5445_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_5343_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5446_ = crate::leanh::lean_box((v___y_5440_) as usize);
                    v___x_5447_ = crate::leanh::lean_box((v_suppressElabErrors_5445_) as usize);
                    v___f_5448_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_5448_, 0, v___x_5446_);
                    crate::leanh::lean_closure_set(v___f_5448_, 1, v___x_5447_);
                    v___x_5449_ = 1;
                    v___x_5450_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5339_, v___x_5449_);
                    if v___x_5450_ == 0 {
                        v___y_5432_ = v_ref_5444_;
                        v___y_5433_ = v_suppressElabErrors_5445_;
                        v___y_5434_ = v_fileMap_5442_;
                        v___y_5435_ = v_fileName_5441_;
                        v___y_5436_ = v___f_5448_;
                        v___y_5437_ = v___y_5440_;
                        v___y_5438_ = v___x_5450_;
                        state = 9;
                        continue;
                    } else {
                        v___x_5451_ = l_Lean_warningAsError;
                        v___x_5452_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_options_5443_, v___x_5451_);
                        v___y_5432_ = v_ref_5444_;
                        v___y_5433_ = v_suppressElabErrors_5445_;
                        v___y_5434_ = v_fileMap_5442_;
                        v___y_5435_ = v_fileName_5441_;
                        v___y_5436_ = v___f_5448_;
                        v___y_5437_ = v___y_5440_;
                        v___y_5438_ = v___x_5452_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_5338_);
                    v___x_5453_ = crate::leanh::lean_box(0);
                    v___x_5454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5454_, 0, v___x_5453_);
                    return v___x_5454_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___boxed(
    mut v_ref_5457_: *mut crate::leanh::LeanObject,
    mut v_msgData_5458_: *mut crate::leanh::LeanObject,
    mut v_severity_5459_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5460_: *mut crate::leanh::LeanObject,
    mut v___y_5461_: *mut crate::leanh::LeanObject,
    mut v___y_5462_: *mut crate::leanh::LeanObject,
    mut v___y_5463_: *mut crate::leanh::LeanObject,
    mut v___y_5464_: *mut crate::leanh::LeanObject,
    mut v___y_5465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5466_: u8 = 0;
    let mut v_isSilent_boxed_5467_: u8 = 0;
    let mut v_res_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5466_ = (crate::leanh::lean_unbox(v_severity_5459_) as u8);
    v_isSilent_boxed_5467_ = (crate::leanh::lean_unbox(v_isSilent_5460_) as u8);
    v_res_5468_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_5457_, v_msgData_5458_, v_severity_boxed_5466_, v_isSilent_boxed_5467_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
    crate::leanh::lean_dec(v___y_5464_);
    crate::leanh::lean_dec_ref(v___y_5463_);
    crate::leanh::lean_dec(v___y_5462_);
    crate::leanh::lean_dec_ref(v___y_5461_);
    crate::leanh::lean_dec(v_ref_5457_);
    return v_res_5468_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(
    mut v_msgData_5469_: *mut crate::leanh::LeanObject,
    mut v_severity_5470_: u8,
    mut v_isSilent_5471_: u8,
    mut v___y_5472_: *mut crate::leanh::LeanObject,
    mut v___y_5473_: *mut crate::leanh::LeanObject,
    mut v___y_5474_: *mut crate::leanh::LeanObject,
    mut v___y_5475_: *mut crate::leanh::LeanObject,
    mut v___y_5476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5478_ = crate::leanh::lean_ctor_get(v___y_5475_, 5);
    v___x_5479_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_5478_, v_msgData_5469_, v_severity_5470_, v_isSilent_5471_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
    return v___x_5479_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24___boxed(
    mut v_msgData_5480_: *mut crate::leanh::LeanObject,
    mut v_severity_5481_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
    mut v___y_5484_: *mut crate::leanh::LeanObject,
    mut v___y_5485_: *mut crate::leanh::LeanObject,
    mut v___y_5486_: *mut crate::leanh::LeanObject,
    mut v___y_5487_: *mut crate::leanh::LeanObject,
    mut v___y_5488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5489_: u8 = 0;
    let mut v_isSilent_boxed_5490_: u8 = 0;
    let mut v_res_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5489_ = (crate::leanh::lean_unbox(v_severity_5481_) as u8);
    v_isSilent_boxed_5490_ = (crate::leanh::lean_unbox(v_isSilent_5482_) as u8);
    v_res_5491_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_5480_, v_severity_boxed_5489_, v_isSilent_boxed_5490_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_);
    crate::leanh::lean_dec(v___y_5487_);
    crate::leanh::lean_dec_ref(v___y_5486_);
    crate::leanh::lean_dec(v___y_5485_);
    crate::leanh::lean_dec_ref(v___y_5484_);
    crate::leanh::lean_dec(v___y_5483_);
    return v_res_5491_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15(
    mut v_msgData_5492_: *mut crate::leanh::LeanObject,
    mut v___y_5493_: *mut crate::leanh::LeanObject,
    mut v___y_5494_: *mut crate::leanh::LeanObject,
    mut v___y_5495_: *mut crate::leanh::LeanObject,
    mut v___y_5496_: *mut crate::leanh::LeanObject,
    mut v___y_5497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5499_: u8 = 0;
    let mut v___x_5500_: u8 = 0;
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5499_ = 1;
    v___x_5500_ = 0;
    v___x_5501_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_5492_, v___x_5499_, v___x_5500_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_);
    return v___x_5501_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15___boxed(
    mut v_msgData_5502_: *mut crate::leanh::LeanObject,
    mut v___y_5503_: *mut crate::leanh::LeanObject,
    mut v___y_5504_: *mut crate::leanh::LeanObject,
    mut v___y_5505_: *mut crate::leanh::LeanObject,
    mut v___y_5506_: *mut crate::leanh::LeanObject,
    mut v___y_5507_: *mut crate::leanh::LeanObject,
    mut v___y_5508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5509_ = l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15(v_msgData_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_);
    crate::leanh::lean_dec(v___y_5507_);
    crate::leanh::lean_dec_ref(v___y_5506_);
    crate::leanh::lean_dec(v___y_5505_);
    crate::leanh::lean_dec_ref(v___y_5504_);
    crate::leanh::lean_dec(v___y_5503_);
    return v_res_5509_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5511_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0;
    v___x_5512_ = l_Lean_stringToMessageData(v___x_5511_);
    return v___x_5512_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5518_ = crate::leanh::lean_box(0);
    v___x_5519_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3;
    v___x_5520_ = l_Lean_mkConst(v___x_5519_, v___x_5518_);
    return v___x_5520_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5521_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4);
    v___x_5522_ = l_Lean_MessageData_ofExpr(v___x_5521_);
    return v___x_5522_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5523_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5);
    v___x_5524_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1);
    v___x_5525_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5525_, 0, v___x_5524_);
    crate::leanh::lean_ctor_set(v___x_5525_, 1, v___x_5523_);
    return v___x_5525_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize(
    mut v_goal_5526_: *mut crate::leanh::LeanObject,
    mut v_a_5527_: *mut crate::leanh::LeanObject,
    mut v_a_5528_: *mut crate::leanh::LeanObject,
    mut v_a_5529_: *mut crate::leanh::LeanObject,
    mut v_a_5530_: *mut crate::leanh::LeanObject,
    mut v_a_5531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5544_: u8 = 0;
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5548_: u8 = 0;
    let mut v_unused_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5553_: u8 = 0;
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5557_: u8 = 0;
    let mut v_a_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5561_: u8 = 0;
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_goal_5526_);
                v___x_5533_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(v_goal_5526_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
                if crate::leanh::lean_obj_tag(v___x_5533_) == 0 {
                    v_a_5534_ = crate::leanh::lean_ctor_get(v___x_5533_, 0);
                    crate::leanh::lean_inc(v_a_5534_);
                    crate::leanh::lean_dec_ref_known(v___x_5533_, 1);
                    if crate::leanh::lean_obj_tag(v_a_5534_) == 1 {
                        v_val_5535_ = crate::leanh::lean_ctor_get(v_a_5534_, 0);
                        crate::leanh::lean_inc(v_val_5535_);
                        crate::leanh::lean_dec_ref_known(v_a_5534_, 1);
                        v_fst_5536_ = crate::leanh::lean_ctor_get(v_val_5535_, 0);
                        crate::leanh::lean_inc(v_fst_5536_);
                        v_snd_5537_ = crate::leanh::lean_ctor_get(v_val_5535_, 1);
                        crate::leanh::lean_inc(v_snd_5537_);
                        crate::leanh::lean_dec(v_val_5535_);
                        crate::leanh::lean_inc(v_goal_5526_);
                        v___f_5538_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___boxed as *mut core::ffi::c_void, 9, 3);
                        crate::leanh::lean_closure_set(v___f_5538_, 0, v_fst_5536_);
                        crate::leanh::lean_closure_set(v___f_5538_, 1, v_snd_5537_);
                        crate::leanh::lean_closure_set(v___f_5538_, 2, v_goal_5526_);
                        v___x_5539_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_5526_, v___f_5538_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
                        return v___x_5539_;
                    } else {
                        crate::leanh::lean_dec(v_a_5534_);
                        v___x_5540_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6);
                        v___x_5541_ = l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15(v___x_5540_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
                        if crate::leanh::lean_obj_tag(v___x_5541_) == 0 {
                            v_isSharedCheck_5548_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5541_)) as u8;
                            if v_isSharedCheck_5548_ == 0 {
                                v_unused_5549_ = crate::leanh::lean_ctor_get(v___x_5541_, 0);
                                crate::leanh::lean_dec(v_unused_5549_);
                                v___x_5543_ = v___x_5541_;
                                v_isShared_5544_ = v_isSharedCheck_5548_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5541_);
                                v___x_5543_ = crate::leanh::lean_box(0);
                                v_isShared_5544_ = v_isSharedCheck_5548_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_goal_5526_);
                            v_a_5550_ = crate::leanh::lean_ctor_get(v___x_5541_, 0);
                            v_isSharedCheck_5557_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5541_)) as u8;
                            if v_isSharedCheck_5557_ == 0 {
                                v___x_5552_ = v___x_5541_;
                                v_isShared_5553_ = v_isSharedCheck_5557_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5550_);
                                crate::leanh::lean_dec(v___x_5541_);
                                v___x_5552_ = crate::leanh::lean_box(0);
                                v_isShared_5553_ = v_isSharedCheck_5557_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_5526_);
                    v_a_5558_ = crate::leanh::lean_ctor_get(v___x_5533_, 0);
                    v_isSharedCheck_5565_ = (!crate::leanh::lean_is_exclusive(v___x_5533_)) as u8;
                    if v_isSharedCheck_5565_ == 0 {
                        v___x_5560_ = v___x_5533_;
                        v_isShared_5561_ = v_isSharedCheck_5565_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5558_);
                        crate::leanh::lean_dec(v___x_5533_);
                        v___x_5560_ = crate::leanh::lean_box(0);
                        v_isShared_5561_ = v_isSharedCheck_5565_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5544_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5543_, 0, v_goal_5526_);
                    v___x_5546_ = v___x_5543_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_goal_5526_);
                    v___x_5546_ = v_reuseFailAlloc_5547_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5546_;
            }
            3 => {
                if v_isShared_5553_ == 0 {
                    v___x_5555_ = v___x_5552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5556_, 0, v_a_5550_);
                    v___x_5555_ = v_reuseFailAlloc_5556_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5555_;
            }
            5 => {
                if v_isShared_5561_ == 0 {
                    v___x_5563_ = v___x_5560_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5564_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_a_5558_);
                    v___x_5563_ = v_reuseFailAlloc_5564_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___boxed(
    mut v_goal_5566_: *mut crate::leanh::LeanObject,
    mut v_a_5567_: *mut crate::leanh::LeanObject,
    mut v_a_5568_: *mut crate::leanh::LeanObject,
    mut v_a_5569_: *mut crate::leanh::LeanObject,
    mut v_a_5570_: *mut crate::leanh::LeanObject,
    mut v_a_5571_: *mut crate::leanh::LeanObject,
    mut v_a_5572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5573_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize(v_goal_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_);
    crate::leanh::lean_dec(v_a_5571_);
    crate::leanh::lean_dec_ref(v_a_5570_);
    crate::leanh::lean_dec(v_a_5569_);
    crate::leanh::lean_dec_ref(v_a_5568_);
    crate::leanh::lean_dec(v_a_5567_);
    return v_res_5573_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0(
    mut v_00_u03b2_5574_: *mut crate::leanh::LeanObject,
    mut v_m_5575_: *mut crate::leanh::LeanObject,
    mut v_a_5576_: *mut crate::leanh::LeanObject,
    mut v_b_5577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5578_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_m_5575_, v_a_5576_, v_b_5577_);
    return v___x_5578_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2(
    mut v_as_5579_: *mut crate::leanh::LeanObject,
    mut v_sz_5580_: usize,
    mut v_i_5581_: usize,
    mut v_b_5582_: *mut crate::leanh::LeanObject,
    mut v___y_5583_: *mut crate::leanh::LeanObject,
    mut v___y_5584_: *mut crate::leanh::LeanObject,
    mut v___y_5585_: *mut crate::leanh::LeanObject,
    mut v___y_5586_: *mut crate::leanh::LeanObject,
    mut v___y_5587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_5579_, v_sz_5580_, v_i_5581_, v_b_5582_);
    return v___x_5589_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___boxed(
    mut v_as_5590_: *mut crate::leanh::LeanObject,
    mut v_sz_5591_: *mut crate::leanh::LeanObject,
    mut v_i_5592_: *mut crate::leanh::LeanObject,
    mut v_b_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
    mut v___y_5595_: *mut crate::leanh::LeanObject,
    mut v___y_5596_: *mut crate::leanh::LeanObject,
    mut v___y_5597_: *mut crate::leanh::LeanObject,
    mut v___y_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5600_: usize = 0;
    let mut v_i_boxed_5601_: usize = 0;
    let mut v_res_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5600_ = crate::leanh::lean_unbox_usize(v_sz_5591_);
    crate::leanh::lean_dec(v_sz_5591_);
    v_i_boxed_5601_ = crate::leanh::lean_unbox_usize(v_i_5592_);
    crate::leanh::lean_dec(v_i_5592_);
    v_res_5602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2(v_as_5590_, v_sz_boxed_5600_, v_i_boxed_5601_, v_b_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
    crate::leanh::lean_dec(v___y_5598_);
    crate::leanh::lean_dec_ref(v___y_5597_);
    crate::leanh::lean_dec(v___y_5596_);
    crate::leanh::lean_dec_ref(v___y_5595_);
    crate::leanh::lean_dec(v___y_5594_);
    crate::leanh::lean_dec_ref(v_as_5590_);
    return v_res_5602_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3(
    mut v_00_u03b2_5603_: *mut crate::leanh::LeanObject,
    mut v_m_5604_: *mut crate::leanh::LeanObject,
    mut v_a_5605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_5604_, v_a_5605_);
    return v___x_5606_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___boxed(
    mut v_00_u03b2_5607_: *mut crate::leanh::LeanObject,
    mut v_m_5608_: *mut crate::leanh::LeanObject,
    mut v_a_5609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3(v_00_u03b2_5607_, v_m_5608_, v_a_5609_);
    crate::leanh::lean_dec_ref(v_a_5609_);
    crate::leanh::lean_dec_ref(v_m_5608_);
    return v_res_5610_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(
    mut v_00_u03b1_5611_: *mut crate::leanh::LeanObject,
    mut v_name_5612_: *mut crate::leanh::LeanObject,
    mut v_bi_5613_: u8,
    mut v_type_5614_: *mut crate::leanh::LeanObject,
    mut v_k_5615_: *mut crate::leanh::LeanObject,
    mut v_kind_5616_: u8,
    mut v___y_5617_: *mut crate::leanh::LeanObject,
    mut v___y_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
    mut v___y_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5623_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_5612_, v_bi_5613_, v_type_5614_, v_k_5615_, v_kind_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    return v___x_5623_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___boxed(
    mut v_00_u03b1_5624_: *mut crate::leanh::LeanObject,
    mut v_name_5625_: *mut crate::leanh::LeanObject,
    mut v_bi_5626_: *mut crate::leanh::LeanObject,
    mut v_type_5627_: *mut crate::leanh::LeanObject,
    mut v_k_5628_: *mut crate::leanh::LeanObject,
    mut v_kind_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
    mut v___y_5631_: *mut crate::leanh::LeanObject,
    mut v___y_5632_: *mut crate::leanh::LeanObject,
    mut v___y_5633_: *mut crate::leanh::LeanObject,
    mut v___y_5634_: *mut crate::leanh::LeanObject,
    mut v___y_5635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_5636_: u8 = 0;
    let mut v_kind_boxed_5637_: u8 = 0;
    let mut v_res_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_5636_ = (crate::leanh::lean_unbox(v_bi_5626_) as u8);
    v_kind_boxed_5637_ = (crate::leanh::lean_unbox(v_kind_5629_) as u8);
    v_res_5638_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(v_00_u03b1_5624_, v_name_5625_, v_bi_boxed_5636_, v_type_5627_, v_k_5628_, v_kind_boxed_5637_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_);
    crate::leanh::lean_dec(v___y_5634_);
    crate::leanh::lean_dec_ref(v___y_5633_);
    crate::leanh::lean_dec(v___y_5632_);
    crate::leanh::lean_dec_ref(v___y_5631_);
    crate::leanh::lean_dec(v___y_5630_);
    return v_res_5638_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6(
    mut v_00_u03b1_5639_: *mut crate::leanh::LeanObject,
    mut v_name_5640_: *mut crate::leanh::LeanObject,
    mut v_type_5641_: *mut crate::leanh::LeanObject,
    mut v_k_5642_: *mut crate::leanh::LeanObject,
    mut v___y_5643_: *mut crate::leanh::LeanObject,
    mut v___y_5644_: *mut crate::leanh::LeanObject,
    mut v___y_5645_: *mut crate::leanh::LeanObject,
    mut v___y_5646_: *mut crate::leanh::LeanObject,
    mut v___y_5647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5649_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_5640_, v_type_5641_, v_k_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
    return v___x_5649_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___boxed(
    mut v_00_u03b1_5650_: *mut crate::leanh::LeanObject,
    mut v_name_5651_: *mut crate::leanh::LeanObject,
    mut v_type_5652_: *mut crate::leanh::LeanObject,
    mut v_k_5653_: *mut crate::leanh::LeanObject,
    mut v___y_5654_: *mut crate::leanh::LeanObject,
    mut v___y_5655_: *mut crate::leanh::LeanObject,
    mut v___y_5656_: *mut crate::leanh::LeanObject,
    mut v___y_5657_: *mut crate::leanh::LeanObject,
    mut v___y_5658_: *mut crate::leanh::LeanObject,
    mut v___y_5659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5660_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6(v_00_u03b1_5650_, v_name_5651_, v_type_5652_, v_k_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
    crate::leanh::lean_dec(v___y_5658_);
    crate::leanh::lean_dec_ref(v___y_5657_);
    crate::leanh::lean_dec(v___y_5656_);
    crate::leanh::lean_dec_ref(v___y_5655_);
    crate::leanh::lean_dec(v___y_5654_);
    return v_res_5660_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7(
    mut v_mvarId_5661_: *mut crate::leanh::LeanObject,
    mut v_val_5662_: *mut crate::leanh::LeanObject,
    mut v___y_5663_: *mut crate::leanh::LeanObject,
    mut v___y_5664_: *mut crate::leanh::LeanObject,
    mut v___y_5665_: *mut crate::leanh::LeanObject,
    mut v___y_5666_: *mut crate::leanh::LeanObject,
    mut v___y_5667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5669_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_5661_, v_val_5662_, v___y_5665_);
    return v___x_5669_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___boxed(
    mut v_mvarId_5670_: *mut crate::leanh::LeanObject,
    mut v_val_5671_: *mut crate::leanh::LeanObject,
    mut v___y_5672_: *mut crate::leanh::LeanObject,
    mut v___y_5673_: *mut crate::leanh::LeanObject,
    mut v___y_5674_: *mut crate::leanh::LeanObject,
    mut v___y_5675_: *mut crate::leanh::LeanObject,
    mut v___y_5676_: *mut crate::leanh::LeanObject,
    mut v___y_5677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5678_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7(v_mvarId_5670_, v_val_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_);
    crate::leanh::lean_dec(v___y_5676_);
    crate::leanh::lean_dec_ref(v___y_5675_);
    crate::leanh::lean_dec(v___y_5674_);
    crate::leanh::lean_dec_ref(v___y_5673_);
    crate::leanh::lean_dec(v___y_5672_);
    return v_res_5678_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9(
    mut v_00_u03b1_5679_: *mut crate::leanh::LeanObject,
    mut v_msg_5680_: *mut crate::leanh::LeanObject,
    mut v___y_5681_: *mut crate::leanh::LeanObject,
    mut v___y_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5686_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
    return v___x_5686_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___boxed(
    mut v_00_u03b1_5687_: *mut crate::leanh::LeanObject,
    mut v_msg_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
    mut v___y_5690_: *mut crate::leanh::LeanObject,
    mut v___y_5691_: *mut crate::leanh::LeanObject,
    mut v___y_5692_: *mut crate::leanh::LeanObject,
    mut v___y_5693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5694_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9(v_00_u03b1_5687_, v_msg_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
    crate::leanh::lean_dec(v___y_5692_);
    crate::leanh::lean_dec_ref(v___y_5691_);
    crate::leanh::lean_dec(v___y_5690_);
    crate::leanh::lean_dec_ref(v___y_5689_);
    return v_res_5694_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(
    mut v_00_u03b2_5695_: *mut crate::leanh::LeanObject,
    mut v_a_5696_: *mut crate::leanh::LeanObject,
    mut v_x_5697_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5698_: u8 = 0;
    v___x_5698_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_5696_, v_x_5697_);
    return v___x_5698_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___boxed(
    mut v_00_u03b2_5699_: *mut crate::leanh::LeanObject,
    mut v_a_5700_: *mut crate::leanh::LeanObject,
    mut v_x_5701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5702_: u8 = 0;
    let mut v_r_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5702_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(v_00_u03b2_5699_, v_a_5700_, v_x_5701_);
    crate::leanh::lean_dec(v_x_5701_);
    crate::leanh::lean_dec_ref(v_a_5700_);
    v_r_5703_ = crate::leanh::lean_box((v_res_5702_) as usize);
    return v_r_5703_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1(
    mut v_00_u03b2_5704_: *mut crate::leanh::LeanObject,
    mut v_data_5705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5706_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_data_5705_);
    return v___x_5706_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2(
    mut v_00_u03b2_5707_: *mut crate::leanh::LeanObject,
    mut v_a_5708_: *mut crate::leanh::LeanObject,
    mut v_b_5709_: *mut crate::leanh::LeanObject,
    mut v_x_5710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5711_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_5708_, v_b_5709_, v_x_5710_);
    return v___x_5711_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(
    mut v_00_u03b2_5712_: *mut crate::leanh::LeanObject,
    mut v_a_5713_: *mut crate::leanh::LeanObject,
    mut v_x_5714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5715_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_5713_, v_x_5714_);
    return v___x_5715_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___boxed(
    mut v_00_u03b2_5716_: *mut crate::leanh::LeanObject,
    mut v_a_5717_: *mut crate::leanh::LeanObject,
    mut v_x_5718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5719_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(v_00_u03b2_5716_, v_a_5717_, v_x_5718_);
    crate::leanh::lean_dec(v_x_5718_);
    crate::leanh::lean_dec_ref(v_a_5717_);
    return v_res_5719_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14(
    mut v_00_u03b2_5720_: *mut crate::leanh::LeanObject,
    mut v_x_5721_: *mut crate::leanh::LeanObject,
    mut v_x_5722_: *mut crate::leanh::LeanObject,
    mut v_x_5723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5724_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_x_5721_, v_x_5722_, v_x_5723_);
    return v___x_5724_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3(
    mut v_00_u03b2_5725_: *mut crate::leanh::LeanObject,
    mut v_i_5726_: *mut crate::leanh::LeanObject,
    mut v_source_5727_: *mut crate::leanh::LeanObject,
    mut v_target_5728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5729_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v_i_5726_, v_source_5727_, v_target_5728_);
    return v___x_5729_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(
    mut v_00_u03b2_5730_: *mut crate::leanh::LeanObject,
    mut v_x_5731_: *mut crate::leanh::LeanObject,
    mut v_x_5732_: usize,
    mut v_x_5733_: usize,
    mut v_x_5734_: *mut crate::leanh::LeanObject,
    mut v_x_5735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5736_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_5731_, v_x_5732_, v_x_5733_, v_x_5734_, v_x_5735_);
    return v___x_5736_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___boxed(
    mut v_00_u03b2_5737_: *mut crate::leanh::LeanObject,
    mut v_x_5738_: *mut crate::leanh::LeanObject,
    mut v_x_5739_: *mut crate::leanh::LeanObject,
    mut v_x_5740_: *mut crate::leanh::LeanObject,
    mut v_x_5741_: *mut crate::leanh::LeanObject,
    mut v_x_5742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_23590__boxed_5743_: usize = 0;
    let mut v_x_23591__boxed_5744_: usize = 0;
    let mut v_res_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_23590__boxed_5743_ = crate::leanh::lean_unbox_usize(v_x_5739_);
    crate::leanh::lean_dec(v_x_5739_);
    v_x_23591__boxed_5744_ = crate::leanh::lean_unbox_usize(v_x_5740_);
    crate::leanh::lean_dec(v_x_5740_);
    v_res_5745_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(v_00_u03b2_5737_, v_x_5738_, v_x_23590__boxed_5743_, v_x_23591__boxed_5744_, v_x_5741_, v_x_5742_);
    return v_res_5745_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(
    mut v_ref_5746_: *mut crate::leanh::LeanObject,
    mut v_msgData_5747_: *mut crate::leanh::LeanObject,
    mut v_severity_5748_: u8,
    mut v_isSilent_5749_: u8,
    mut v___y_5750_: *mut crate::leanh::LeanObject,
    mut v___y_5751_: *mut crate::leanh::LeanObject,
    mut v___y_5752_: *mut crate::leanh::LeanObject,
    mut v___y_5753_: *mut crate::leanh::LeanObject,
    mut v___y_5754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5756_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_5746_, v_msgData_5747_, v_severity_5748_, v_isSilent_5749_, v___y_5751_, v___y_5752_, v___y_5753_, v___y_5754_);
    return v___x_5756_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___boxed(
    mut v_ref_5757_: *mut crate::leanh::LeanObject,
    mut v_msgData_5758_: *mut crate::leanh::LeanObject,
    mut v_severity_5759_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5760_: *mut crate::leanh::LeanObject,
    mut v___y_5761_: *mut crate::leanh::LeanObject,
    mut v___y_5762_: *mut crate::leanh::LeanObject,
    mut v___y_5763_: *mut crate::leanh::LeanObject,
    mut v___y_5764_: *mut crate::leanh::LeanObject,
    mut v___y_5765_: *mut crate::leanh::LeanObject,
    mut v___y_5766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5767_: u8 = 0;
    let mut v_isSilent_boxed_5768_: u8 = 0;
    let mut v_res_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5767_ = (crate::leanh::lean_unbox(v_severity_5759_) as u8);
    v_isSilent_boxed_5768_ = (crate::leanh::lean_unbox(v_isSilent_5760_) as u8);
    v_res_5769_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(v_ref_5757_, v_msgData_5758_, v_severity_boxed_5767_, v_isSilent_boxed_5768_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_);
    crate::leanh::lean_dec(v___y_5765_);
    crate::leanh::lean_dec_ref(v___y_5764_);
    crate::leanh::lean_dec(v___y_5763_);
    crate::leanh::lean_dec_ref(v___y_5762_);
    crate::leanh::lean_dec(v___y_5761_);
    crate::leanh::lean_dec(v_ref_5757_);
    return v_res_5769_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20(
    mut v_00_u03b2_5770_: *mut crate::leanh::LeanObject,
    mut v_x_5771_: *mut crate::leanh::LeanObject,
    mut v_x_5772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5773_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_x_5771_, v_x_5772_);
    return v___x_5773_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30(
    mut v_00_u03b2_5774_: *mut crate::leanh::LeanObject,
    mut v_n_5775_: *mut crate::leanh::LeanObject,
    mut v_k_5776_: *mut crate::leanh::LeanObject,
    mut v_v_5777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5778_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v_n_5775_, v_k_5776_, v_v_5777_);
    return v___x_5778_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(
    mut v_00_u03b2_5779_: *mut crate::leanh::LeanObject,
    mut v_depth_5780_: usize,
    mut v_keys_5781_: *mut crate::leanh::LeanObject,
    mut v_vals_5782_: *mut crate::leanh::LeanObject,
    mut v_heq_5783_: *mut crate::leanh::LeanObject,
    mut v_i_5784_: *mut crate::leanh::LeanObject,
    mut v_entries_5785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5786_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_5780_, v_keys_5781_, v_vals_5782_, v_i_5784_, v_entries_5785_);
    return v___x_5786_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___boxed(
    mut v_00_u03b2_5787_: *mut crate::leanh::LeanObject,
    mut v_depth_5788_: *mut crate::leanh::LeanObject,
    mut v_keys_5789_: *mut crate::leanh::LeanObject,
    mut v_vals_5790_: *mut crate::leanh::LeanObject,
    mut v_heq_5791_: *mut crate::leanh::LeanObject,
    mut v_i_5792_: *mut crate::leanh::LeanObject,
    mut v_entries_5793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5794_: usize = 0;
    let mut v_res_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5794_ = crate::leanh::lean_unbox_usize(v_depth_5788_);
    crate::leanh::lean_dec(v_depth_5788_);
    v_res_5795_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(v_00_u03b2_5787_, v_depth_boxed_5794_, v_keys_5789_, v_vals_5790_, v_heq_5791_, v_i_5792_, v_entries_5793_);
    crate::leanh::lean_dec_ref(v_vals_5790_);
    crate::leanh::lean_dec_ref(v_keys_5789_);
    return v_res_5795_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32(
    mut v_00_u03b2_5796_: *mut crate::leanh::LeanObject,
    mut v_x_5797_: *mut crate::leanh::LeanObject,
    mut v_x_5798_: *mut crate::leanh::LeanObject,
    mut v_x_5799_: *mut crate::leanh::LeanObject,
    mut v_x_5800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5801_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_x_5797_, v_x_5798_, v_x_5799_, v_x_5800_);
    return v___x_5801_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(
    mut v_e_5802_: *mut crate::leanh::LeanObject,
    mut v___y_5803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5805_: u8 = 0;
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5825_: u8 = 0;
    let mut v_unused_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5805_ = l_Lean_Expr_hasMVar(v_e_5802_);
                if v___x_5805_ == 0 {
                    v___x_5806_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5806_, 0, v_e_5802_);
                    return v___x_5806_;
                } else {
                    v___x_5807_ = lean_st_ref_get(v___y_5803_);
                    v_mctx_5808_ = crate::leanh::lean_ctor_get(v___x_5807_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5808_);
                    crate::leanh::lean_dec(v___x_5807_);
                    v___x_5809_ = l_Lean_instantiateMVarsCore(v_mctx_5808_, v_e_5802_);
                    v_fst_5810_ = crate::leanh::lean_ctor_get(v___x_5809_, 0);
                    crate::leanh::lean_inc(v_fst_5810_);
                    v_snd_5811_ = crate::leanh::lean_ctor_get(v___x_5809_, 1);
                    crate::leanh::lean_inc(v_snd_5811_);
                    crate::leanh::lean_dec_ref(v___x_5809_);
                    v___x_5812_ = lean_st_ref_take(v___y_5803_);
                    v_cache_5813_ = crate::leanh::lean_ctor_get(v___x_5812_, 1);
                    v_zetaDeltaFVarIds_5814_ = crate::leanh::lean_ctor_get(v___x_5812_, 2);
                    v_postponed_5815_ = crate::leanh::lean_ctor_get(v___x_5812_, 3);
                    v_diag_5816_ = crate::leanh::lean_ctor_get(v___x_5812_, 4);
                    v_isSharedCheck_5825_ = (!crate::leanh::lean_is_exclusive(v___x_5812_)) as u8;
                    if v_isSharedCheck_5825_ == 0 {
                        v_unused_5826_ = crate::leanh::lean_ctor_get(v___x_5812_, 0);
                        crate::leanh::lean_dec(v_unused_5826_);
                        v___x_5818_ = v___x_5812_;
                        v_isShared_5819_ = v_isSharedCheck_5825_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5816_);
                        crate::leanh::lean_inc(v_postponed_5815_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5814_);
                        crate::leanh::lean_inc(v_cache_5813_);
                        crate::leanh::lean_dec(v___x_5812_);
                        v___x_5818_ = crate::leanh::lean_box(0);
                        v_isShared_5819_ = v_isSharedCheck_5825_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5819_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5818_, 0, v_snd_5811_);
                    v___x_5821_ = v___x_5818_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5824_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_snd_5811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5824_, 1, v_cache_5813_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5824_,
                        2,
                        v_zetaDeltaFVarIds_5814_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5824_, 3, v_postponed_5815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5824_, 4, v_diag_5816_);
                    v___x_5821_ = v_reuseFailAlloc_5824_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5822_ = lean_st_ref_set(v___y_5803_, v___x_5821_);
                v___x_5823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5823_, 0, v_fst_5810_);
                return v___x_5823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg___boxed(
    mut v_e_5827_: *mut crate::leanh::LeanObject,
    mut v___y_5828_: *mut crate::leanh::LeanObject,
    mut v___y_5829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5830_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_5827_, v___y_5828_);
    crate::leanh::lean_dec(v___y_5828_);
    return v_res_5830_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2(
    mut v_e_5831_: *mut crate::leanh::LeanObject,
    mut v___y_5832_: *mut crate::leanh::LeanObject,
    mut v___y_5833_: *mut crate::leanh::LeanObject,
    mut v___y_5834_: *mut crate::leanh::LeanObject,
    mut v___y_5835_: *mut crate::leanh::LeanObject,
    mut v___y_5836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5838_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_5831_, v___y_5834_);
    return v___x_5838_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___boxed(
    mut v_e_5839_: *mut crate::leanh::LeanObject,
    mut v___y_5840_: *mut crate::leanh::LeanObject,
    mut v___y_5841_: *mut crate::leanh::LeanObject,
    mut v___y_5842_: *mut crate::leanh::LeanObject,
    mut v___y_5843_: *mut crate::leanh::LeanObject,
    mut v___y_5844_: *mut crate::leanh::LeanObject,
    mut v___y_5845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5846_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2(v_e_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
    crate::leanh::lean_dec(v___y_5844_);
    crate::leanh::lean_dec_ref(v___y_5843_);
    crate::leanh::lean_dec(v___y_5842_);
    crate::leanh::lean_dec_ref(v___y_5841_);
    crate::leanh::lean_dec(v___y_5840_);
    return v_res_5846_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(
    mut v_m_5847_: *mut crate::leanh::LeanObject,
    mut v_a_5848_: *mut crate::leanh::LeanObject,
    mut v_b_5849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: u64 = 0;
    let mut v___x_5854_: u64 = 0;
    let mut v___x_5855_: u64 = 0;
    let mut v_fold_5856_: u64 = 0;
    let mut v___x_5857_: u64 = 0;
    let mut v___x_5858_: u64 = 0;
    let mut v___x_5859_: u64 = 0;
    let mut v___x_5860_: usize = 0;
    let mut v___x_5861_: usize = 0;
    let mut v___x_5862_: usize = 0;
    let mut v___x_5863_: usize = 0;
    let mut v___x_5864_: usize = 0;
    let mut v_bkt_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: u8 = 0;
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5869_: u8 = 0;
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: u8 = 0;
    let mut v_val_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5887_: u8 = 0;
    let mut v_unused_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5850_ = crate::leanh::lean_ctor_get(v_m_5847_, 0);
                v_buckets_5851_ = crate::leanh::lean_ctor_get(v_m_5847_, 1);
                v___x_5852_ = lean_array_get_size(v_buckets_5851_);
                v___x_5853_ = l_Lean_Expr_hash(v_a_5848_);
                v___x_5854_ = 32u64;
                v___x_5855_ = lean_uint64_shift_right(v___x_5853_, v___x_5854_);
                v_fold_5856_ = lean_uint64_xor(v___x_5853_, v___x_5855_);
                v___x_5857_ = 16u64;
                v___x_5858_ = lean_uint64_shift_right(v_fold_5856_, v___x_5857_);
                v___x_5859_ = lean_uint64_xor(v_fold_5856_, v___x_5858_);
                v___x_5860_ = lean_uint64_to_usize(v___x_5859_);
                v___x_5861_ = lean_usize_of_nat(v___x_5852_);
                v___x_5862_ = 1usize;
                v___x_5863_ = lean_usize_sub(v___x_5861_, v___x_5862_);
                v___x_5864_ = lean_usize_land(v___x_5860_, v___x_5863_);
                v_bkt_5865_ = lean_array_uget_borrowed(v_buckets_5851_, v___x_5864_);
                v___x_5866_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_5848_, v_bkt_5865_);
                if v___x_5866_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_5851_);
                    crate::leanh::lean_inc(v_size_5850_);
                    v_isSharedCheck_5887_ = (!crate::leanh::lean_is_exclusive(v_m_5847_)) as u8;
                    if v_isSharedCheck_5887_ == 0 {
                        v_unused_5888_ = crate::leanh::lean_ctor_get(v_m_5847_, 1);
                        crate::leanh::lean_dec(v_unused_5888_);
                        v_unused_5889_ = crate::leanh::lean_ctor_get(v_m_5847_, 0);
                        crate::leanh::lean_dec(v_unused_5889_);
                        v___x_5868_ = v_m_5847_;
                        v_isShared_5869_ = v_isSharedCheck_5887_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_5847_);
                        v___x_5868_ = crate::leanh::lean_box(0);
                        v_isShared_5869_ = v_isSharedCheck_5887_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_5849_);
                    crate::leanh::lean_dec_ref(v_a_5848_);
                    return v_m_5847_;
                }
            }
            1 => {
                v___x_5870_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_5871_ = lean_nat_add(v_size_5850_, v___x_5870_);
                crate::leanh::lean_dec(v_size_5850_);
                crate::leanh::lean_inc(v_bkt_5865_);
                v___x_5872_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5872_, 0, v_a_5848_);
                crate::leanh::lean_ctor_set(v___x_5872_, 1, v_b_5849_);
                crate::leanh::lean_ctor_set(v___x_5872_, 2, v_bkt_5865_);
                v_buckets_x27_5873_ = lean_array_uset(v_buckets_5851_, v___x_5864_, v___x_5872_);
                v___x_5874_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_5875_ = lean_nat_mul(v_size_x27_5871_, v___x_5874_);
                v___x_5876_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_5877_ = lean_nat_div(v___x_5875_, v___x_5876_);
                crate::leanh::lean_dec(v___x_5875_);
                v___x_5878_ = lean_array_get_size(v_buckets_x27_5873_);
                v___x_5879_ = lean_nat_dec_le(v___x_5877_, v___x_5878_);
                crate::leanh::lean_dec(v___x_5877_);
                if v___x_5879_ == 0 {
                    v_val_5880_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_5873_);
                    if v_isShared_5869_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5868_, 1, v_val_5880_);
                        crate::leanh::lean_ctor_set(v___x_5868_, 0, v_size_x27_5871_);
                        v___x_5882_ = v___x_5868_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5883_, 0, v_size_x27_5871_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5883_, 1, v_val_5880_);
                        v___x_5882_ = v_reuseFailAlloc_5883_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_5869_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5868_, 1, v_buckets_x27_5873_);
                        crate::leanh::lean_ctor_set(v___x_5868_, 0, v_size_x27_5871_);
                        v___x_5885_ = v___x_5868_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5886_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_size_x27_5871_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5886_, 1, v_buckets_x27_5873_);
                        v___x_5885_ = v_reuseFailAlloc_5886_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5882_;
            }
            3 => {
                return v___x_5885_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(
    mut v_a_5890_: *mut crate::leanh::LeanObject,
    mut v_x_5891_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5892_: u8 = 0;
    let mut v_key_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5891_) == 0 {
                    v___x_5892_ = 0;
                    return v___x_5892_;
                } else {
                    v_key_5893_ = crate::leanh::lean_ctor_get(v_x_5891_, 0);
                    v_tail_5894_ = crate::leanh::lean_ctor_get(v_x_5891_, 2);
                    v___x_5895_ = l_Lean_instBEqFVarId_beq(v_key_5893_, v_a_5890_);
                    if v___x_5895_ == 0 {
                        v_x_5891_ = v_tail_5894_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5895_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg___boxed(
    mut v_a_5897_: *mut crate::leanh::LeanObject,
    mut v_x_5898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5899_: u8 = 0;
    let mut v_r_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5899_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_5897_, v_x_5898_);
    crate::leanh::lean_dec(v_x_5898_);
    crate::leanh::lean_dec(v_a_5897_);
    v_r_5900_ = crate::leanh::lean_box((v_res_5899_) as usize);
    return v_r_5900_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(
    mut v_x_5901_: *mut crate::leanh::LeanObject,
    mut v_x_5902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5908_: u8 = 0;
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: u64 = 0;
    let mut v___x_5911_: u64 = 0;
    let mut v___x_5912_: u64 = 0;
    let mut v_fold_5913_: u64 = 0;
    let mut v___x_5914_: u64 = 0;
    let mut v___x_5915_: u64 = 0;
    let mut v___x_5916_: u64 = 0;
    let mut v___x_5917_: usize = 0;
    let mut v___x_5918_: usize = 0;
    let mut v___x_5919_: usize = 0;
    let mut v___x_5920_: usize = 0;
    let mut v___x_5921_: usize = 0;
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5902_) == 0 {
                    return v_x_5901_;
                } else {
                    v_key_5903_ = crate::leanh::lean_ctor_get(v_x_5902_, 0);
                    v_value_5904_ = crate::leanh::lean_ctor_get(v_x_5902_, 1);
                    v_tail_5905_ = crate::leanh::lean_ctor_get(v_x_5902_, 2);
                    v_isSharedCheck_5928_ = (!crate::leanh::lean_is_exclusive(v_x_5902_)) as u8;
                    if v_isSharedCheck_5928_ == 0 {
                        v___x_5907_ = v_x_5902_;
                        v_isShared_5908_ = v_isSharedCheck_5928_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5905_);
                        crate::leanh::lean_inc(v_value_5904_);
                        crate::leanh::lean_inc(v_key_5903_);
                        crate::leanh::lean_dec(v_x_5902_);
                        v___x_5907_ = crate::leanh::lean_box(0);
                        v_isShared_5908_ = v_isSharedCheck_5928_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5909_ = lean_array_get_size(v_x_5901_);
                v___x_5910_ = l_Lean_instHashableFVarId_hash(v_key_5903_);
                v___x_5911_ = 32u64;
                v___x_5912_ = lean_uint64_shift_right(v___x_5910_, v___x_5911_);
                v_fold_5913_ = lean_uint64_xor(v___x_5910_, v___x_5912_);
                v___x_5914_ = 16u64;
                v___x_5915_ = lean_uint64_shift_right(v_fold_5913_, v___x_5914_);
                v___x_5916_ = lean_uint64_xor(v_fold_5913_, v___x_5915_);
                v___x_5917_ = lean_uint64_to_usize(v___x_5916_);
                v___x_5918_ = lean_usize_of_nat(v___x_5909_);
                v___x_5919_ = 1usize;
                v___x_5920_ = lean_usize_sub(v___x_5918_, v___x_5919_);
                v___x_5921_ = lean_usize_land(v___x_5917_, v___x_5920_);
                v___x_5922_ = lean_array_uget_borrowed(v_x_5901_, v___x_5921_);
                crate::leanh::lean_inc(v___x_5922_);
                if v_isShared_5908_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5907_, 2, v___x_5922_);
                    v___x_5924_ = v___x_5907_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5927_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_key_5903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5927_, 1, v_value_5904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5927_, 2, v___x_5922_);
                    v___x_5924_ = v_reuseFailAlloc_5927_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5925_ = lean_array_uset(v_x_5901_, v___x_5921_, v___x_5924_);
                v_x_5901_ = v___x_5925_;
                v_x_5902_ = v_tail_5905_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(
    mut v_i_5929_: *mut crate::leanh::LeanObject,
    mut v_source_5930_: *mut crate::leanh::LeanObject,
    mut v_target_5931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: u8 = 0;
    let mut v_es_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5932_ = lean_array_get_size(v_source_5930_);
                v___x_5933_ = lean_nat_dec_lt(v_i_5929_, v___x_5932_);
                if v___x_5933_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_5930_);
                    crate::leanh::lean_dec(v_i_5929_);
                    return v_target_5931_;
                } else {
                    v_es_5934_ = lean_array_fget(v_source_5930_, v_i_5929_);
                    v___x_5935_ = crate::leanh::lean_box(0);
                    v_source_5936_ = lean_array_fset(v_source_5930_, v_i_5929_, v___x_5935_);
                    v_target_5937_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_target_5931_, v_es_5934_);
                    v___x_5938_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5939_ = lean_nat_add(v_i_5929_, v___x_5938_);
                    crate::leanh::lean_dec(v_i_5929_);
                    v_i_5929_ = v___x_5939_;
                    v_source_5930_ = v_source_5936_;
                    v_target_5931_ = v_target_5937_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(
    mut v_data_5941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5942_ = lean_array_get_size(v_data_5941_);
    v___x_5943_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5944_ = lean_nat_mul(v___x_5942_, v___x_5943_);
    v___x_5945_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5946_ = crate::leanh::lean_box(0);
    v___x_5947_ = lean_mk_array(v_nbuckets_5944_, v___x_5946_);
    v___x_5948_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v___x_5945_, v_data_5941_, v___x_5947_);
    return v___x_5948_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1___redArg(
    mut v_m_5949_: *mut crate::leanh::LeanObject,
    mut v_a_5950_: *mut crate::leanh::LeanObject,
    mut v_b_5951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: u64 = 0;
    let mut v___x_5956_: u64 = 0;
    let mut v___x_5957_: u64 = 0;
    let mut v_fold_5958_: u64 = 0;
    let mut v___x_5959_: u64 = 0;
    let mut v___x_5960_: u64 = 0;
    let mut v___x_5961_: u64 = 0;
    let mut v___x_5962_: usize = 0;
    let mut v___x_5963_: usize = 0;
    let mut v___x_5964_: usize = 0;
    let mut v___x_5965_: usize = 0;
    let mut v___x_5966_: usize = 0;
    let mut v_bkt_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: u8 = 0;
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5971_: u8 = 0;
    let mut v___x_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: u8 = 0;
    let mut v_val_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5989_: u8 = 0;
    let mut v_unused_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5952_ = crate::leanh::lean_ctor_get(v_m_5949_, 0);
                v_buckets_5953_ = crate::leanh::lean_ctor_get(v_m_5949_, 1);
                v___x_5954_ = lean_array_get_size(v_buckets_5953_);
                v___x_5955_ = l_Lean_instHashableFVarId_hash(v_a_5950_);
                v___x_5956_ = 32u64;
                v___x_5957_ = lean_uint64_shift_right(v___x_5955_, v___x_5956_);
                v_fold_5958_ = lean_uint64_xor(v___x_5955_, v___x_5957_);
                v___x_5959_ = 16u64;
                v___x_5960_ = lean_uint64_shift_right(v_fold_5958_, v___x_5959_);
                v___x_5961_ = lean_uint64_xor(v_fold_5958_, v___x_5960_);
                v___x_5962_ = lean_uint64_to_usize(v___x_5961_);
                v___x_5963_ = lean_usize_of_nat(v___x_5954_);
                v___x_5964_ = 1usize;
                v___x_5965_ = lean_usize_sub(v___x_5963_, v___x_5964_);
                v___x_5966_ = lean_usize_land(v___x_5962_, v___x_5965_);
                v_bkt_5967_ = lean_array_uget_borrowed(v_buckets_5953_, v___x_5966_);
                v___x_5968_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_5950_, v_bkt_5967_);
                if v___x_5968_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_5953_);
                    crate::leanh::lean_inc(v_size_5952_);
                    v_isSharedCheck_5989_ = (!crate::leanh::lean_is_exclusive(v_m_5949_)) as u8;
                    if v_isSharedCheck_5989_ == 0 {
                        v_unused_5990_ = crate::leanh::lean_ctor_get(v_m_5949_, 1);
                        crate::leanh::lean_dec(v_unused_5990_);
                        v_unused_5991_ = crate::leanh::lean_ctor_get(v_m_5949_, 0);
                        crate::leanh::lean_dec(v_unused_5991_);
                        v___x_5970_ = v_m_5949_;
                        v_isShared_5971_ = v_isSharedCheck_5989_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_5949_);
                        v___x_5970_ = crate::leanh::lean_box(0);
                        v_isShared_5971_ = v_isSharedCheck_5989_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_5951_);
                    crate::leanh::lean_dec(v_a_5950_);
                    return v_m_5949_;
                }
            }
            1 => {
                v___x_5972_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_5973_ = lean_nat_add(v_size_5952_, v___x_5972_);
                crate::leanh::lean_dec(v_size_5952_);
                crate::leanh::lean_inc(v_bkt_5967_);
                v___x_5974_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5974_, 0, v_a_5950_);
                crate::leanh::lean_ctor_set(v___x_5974_, 1, v_b_5951_);
                crate::leanh::lean_ctor_set(v___x_5974_, 2, v_bkt_5967_);
                v_buckets_x27_5975_ = lean_array_uset(v_buckets_5953_, v___x_5966_, v___x_5974_);
                v___x_5976_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_5977_ = lean_nat_mul(v_size_x27_5973_, v___x_5976_);
                v___x_5978_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_5979_ = lean_nat_div(v___x_5977_, v___x_5978_);
                crate::leanh::lean_dec(v___x_5977_);
                v___x_5980_ = lean_array_get_size(v_buckets_x27_5975_);
                v___x_5981_ = lean_nat_dec_le(v___x_5979_, v___x_5980_);
                crate::leanh::lean_dec(v___x_5979_);
                if v___x_5981_ == 0 {
                    v_val_5982_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_buckets_x27_5975_);
                    if v_isShared_5971_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5970_, 1, v_val_5982_);
                        crate::leanh::lean_ctor_set(v___x_5970_, 0, v_size_x27_5973_);
                        v___x_5984_ = v___x_5970_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5985_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_size_x27_5973_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_val_5982_);
                        v___x_5984_ = v_reuseFailAlloc_5985_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_5971_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5970_, 1, v_buckets_x27_5975_);
                        crate::leanh::lean_ctor_set(v___x_5970_, 0, v_size_x27_5973_);
                        v___x_5987_ = v___x_5970_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5988_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5988_, 0, v_size_x27_5973_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5988_, 1, v_buckets_x27_5975_);
                        v___x_5987_ = v_reuseFailAlloc_5988_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5984_;
            }
            3 => {
                return v___x_5987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(
    mut v___x_5992_: *mut crate::leanh::LeanObject,
    mut v_a_5993_: *mut crate::leanh::LeanObject,
    mut v_e_5994_: *mut crate::leanh::LeanObject,
    mut v___y_5995_: *mut crate::leanh::LeanObject,
    mut v___y_5996_: *mut crate::leanh::LeanObject,
    mut v___y_5997_: *mut crate::leanh::LeanObject,
    mut v___y_5998_: *mut crate::leanh::LeanObject,
    mut v___y_5999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6006_: u8 = 0;
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6016_: u8 = 0;
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6023_: u8 = 0;
    let mut v_reuseFailAlloc_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6001_ = lean_st_ref_take(v___y_5995_);
                v_relevantTerms_6002_ = crate::leanh::lean_ctor_get(v___x_6001_, 0);
                v_relevantHyps_6003_ = crate::leanh::lean_ctor_get(v___x_6001_, 1);
                v_isSharedCheck_6025_ = (!crate::leanh::lean_is_exclusive(v___x_6001_)) as u8;
                if v_isSharedCheck_6025_ == 0 {
                    v___x_6005_ = v___x_6001_;
                    v_isShared_6006_ = v_isSharedCheck_6025_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_relevantHyps_6003_);
                    crate::leanh::lean_inc(v_relevantTerms_6002_);
                    crate::leanh::lean_dec(v___x_6001_);
                    v___x_6005_ = crate::leanh::lean_box(0);
                    v_isShared_6006_ = v_isSharedCheck_6025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6007_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_relevantTerms_6002_, v_e_5994_, v___x_5992_);
                if v_isShared_6006_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6005_, 0, v___x_6007_);
                    v___x_6009_ = v___x_6005_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6024_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6024_, 0, v___x_6007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6024_, 1, v_relevantHyps_6003_);
                    v___x_6009_ = v_reuseFailAlloc_6024_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6010_ = lean_st_ref_set(v___y_5995_, v___x_6009_);
                v___x_6011_ = lean_st_ref_take(v___y_5995_);
                v_relevantTerms_6012_ = crate::leanh::lean_ctor_get(v___x_6011_, 0);
                v_relevantHyps_6013_ = crate::leanh::lean_ctor_get(v___x_6011_, 1);
                v_isSharedCheck_6023_ = (!crate::leanh::lean_is_exclusive(v___x_6011_)) as u8;
                if v_isSharedCheck_6023_ == 0 {
                    v___x_6015_ = v___x_6011_;
                    v_isShared_6016_ = v_isSharedCheck_6023_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_relevantHyps_6013_);
                    crate::leanh::lean_inc(v_relevantTerms_6012_);
                    crate::leanh::lean_dec(v___x_6011_);
                    v___x_6015_ = crate::leanh::lean_box(0);
                    v_isShared_6016_ = v_isSharedCheck_6023_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6017_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_relevantHyps_6013_, v_a_5993_, v___x_5992_);
                if v_isShared_6016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6015_, 1, v___x_6017_);
                    v___x_6019_ = v___x_6015_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6022_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_relevantTerms_6012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 1, v___x_6017_);
                    v___x_6019_ = v_reuseFailAlloc_6022_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6020_ = lean_st_ref_set(v___y_5995_, v___x_6019_);
                v___x_6021_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6021_, 0, v___x_5992_);
                return v___x_6021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed(
    mut v___x_6026_: *mut crate::leanh::LeanObject,
    mut v_a_6027_: *mut crate::leanh::LeanObject,
    mut v_e_6028_: *mut crate::leanh::LeanObject,
    mut v___y_6029_: *mut crate::leanh::LeanObject,
    mut v___y_6030_: *mut crate::leanh::LeanObject,
    mut v___y_6031_: *mut crate::leanh::LeanObject,
    mut v___y_6032_: *mut crate::leanh::LeanObject,
    mut v___y_6033_: *mut crate::leanh::LeanObject,
    mut v___y_6034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(v___x_6026_, v_a_6027_, v_e_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_);
    crate::leanh::lean_dec(v___y_6033_);
    crate::leanh::lean_dec_ref(v___y_6032_);
    crate::leanh::lean_dec(v___y_6031_);
    crate::leanh::lean_dec_ref(v___y_6030_);
    crate::leanh::lean_dec(v___y_6029_);
    return v_res_6035_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(
    mut v_e_6045_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_6047_: u8 = 0;
    let mut v___x_6048_: u8 = 0;
    let mut v___x_6049_: u8 = 0;
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: u8 = 0;
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2;
                v___x_6051_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6052_ = l_Lean_Expr_isAppOfArity(v_e_6045_, v___x_6050_, v___x_6051_);
                if v___x_6052_ == 0 {
                    v___x_6053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4;
                    v___x_6054_ = l_Lean_Expr_isAppOfArity(v_e_6045_, v___x_6053_, v___x_6051_);
                    v___y_6047_ = v___x_6054_;
                    state = 1;
                    continue;
                } else {
                    v___y_6047_ = v___x_6052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_6047_ == 0 {
                    return v___y_6047_;
                } else {
                    v___x_6048_ = l_Lean_Expr_hasLooseBVars(v_e_6045_);
                    if v___x_6048_ == 0 {
                        return v___y_6047_;
                    } else {
                        v___x_6049_ = 0;
                        return v___x_6049_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed(
    mut v_e_6055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6056_: u8 = 0;
    let mut v_r_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(v_e_6055_);
    crate::leanh::lean_dec_ref(v_e_6055_);
    v_r_6057_ = crate::leanh::lean_box((v_res_6056_) as usize);
    return v_r_6057_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0()
-> usize {
    let mut v___x_6058_: usize = 0;
    let mut v___x_6059_: usize = 0;
    let mut v___x_6060_: usize = 0;
    v___x_6058_ = 1usize;
    v___x_6059_ = 8192usize;
    v___x_6060_ = lean_usize_sub(v___x_6059_, v___x_6058_);
    return v___x_6060_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(
    mut v_e_6061_: *mut crate::leanh::LeanObject,
    mut v_a_6062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: usize = 0;
    let mut v___x_6067_: usize = 0;
    let mut v___x_6068_: usize = 0;
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: usize = 0;
    let mut v___x_6071_: u8 = 0;
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6077_: u8 = 0;
    let mut v___x_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6085_: u8 = 0;
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6064_ = lean_st_ref_get(v_a_6062_);
                v_visited_6065_ = crate::leanh::lean_ctor_get(v___x_6064_, 0);
                crate::leanh::lean_inc_ref(v_visited_6065_);
                crate::leanh::lean_dec(v___x_6064_);
                v___x_6066_ = lean_ptr_addr(v_e_6061_);
                v___x_6067_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0_once), _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0);
                v___x_6068_ = lean_usize_mod(v___x_6066_, v___x_6067_);
                v___x_6069_ = lean_array_uget(v_visited_6065_, v___x_6068_);
                crate::leanh::lean_dec_ref(v_visited_6065_);
                v___x_6070_ = lean_ptr_addr(v___x_6069_);
                crate::leanh::lean_dec(v___x_6069_);
                v___x_6071_ = lean_usize_dec_eq(v___x_6070_, v___x_6066_);
                if v___x_6071_ == 0 {
                    v___x_6072_ = lean_st_ref_take(v_a_6062_);
                    v_visited_6073_ = crate::leanh::lean_ctor_get(v___x_6072_, 0);
                    v_checked_6074_ = crate::leanh::lean_ctor_get(v___x_6072_, 1);
                    v_isSharedCheck_6085_ = (!crate::leanh::lean_is_exclusive(v___x_6072_)) as u8;
                    if v_isSharedCheck_6085_ == 0 {
                        v___x_6076_ = v___x_6072_;
                        v_isShared_6077_ = v_isSharedCheck_6085_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_checked_6074_);
                        crate::leanh::lean_inc(v_visited_6073_);
                        crate::leanh::lean_dec(v___x_6072_);
                        v___x_6076_ = crate::leanh::lean_box(0);
                        v_isShared_6077_ = v_isSharedCheck_6085_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6061_);
                    v___x_6086_ = crate::leanh::lean_box((v___x_6071_) as usize);
                    v___x_6087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6087_, 0, v___x_6086_);
                    return v___x_6087_;
                }
            }
            1 => {
                v___x_6078_ = lean_array_uset(v_visited_6073_, v___x_6068_, v_e_6061_);
                if v_isShared_6077_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6076_, 0, v___x_6078_);
                    v___x_6080_ = v___x_6076_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6084_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6084_, 0, v___x_6078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6084_, 1, v_checked_6074_);
                    v___x_6080_ = v_reuseFailAlloc_6084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6081_ = lean_st_ref_set(v_a_6062_, v___x_6080_);
                v___x_6082_ = crate::leanh::lean_box((v___x_6071_) as usize);
                v___x_6083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6083_, 0, v___x_6082_);
                return v___x_6083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_e_6088_: *mut crate::leanh::LeanObject,
    mut v_a_6089_: *mut crate::leanh::LeanObject,
    mut v___y_6090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6091_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_6088_, v_a_6089_);
    crate::leanh::lean_dec(v_a_6089_);
    return v_res_6091_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(
    mut v_m_6092_: *mut crate::leanh::LeanObject,
    mut v_a_6093_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: u64 = 0;
    let mut v___x_6097_: u64 = 0;
    let mut v___x_6098_: u64 = 0;
    let mut v_fold_6099_: u64 = 0;
    let mut v___x_6100_: u64 = 0;
    let mut v___x_6101_: u64 = 0;
    let mut v___x_6102_: u64 = 0;
    let mut v___x_6103_: usize = 0;
    let mut v___x_6104_: usize = 0;
    let mut v___x_6105_: usize = 0;
    let mut v___x_6106_: usize = 0;
    let mut v___x_6107_: usize = 0;
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: u8 = 0;
    v_buckets_6094_ = crate::leanh::lean_ctor_get(v_m_6092_, 1);
    v___x_6095_ = lean_array_get_size(v_buckets_6094_);
    v___x_6096_ = l_Lean_Expr_hash(v_a_6093_);
    v___x_6097_ = 32u64;
    v___x_6098_ = lean_uint64_shift_right(v___x_6096_, v___x_6097_);
    v_fold_6099_ = lean_uint64_xor(v___x_6096_, v___x_6098_);
    v___x_6100_ = 16u64;
    v___x_6101_ = lean_uint64_shift_right(v_fold_6099_, v___x_6100_);
    v___x_6102_ = lean_uint64_xor(v_fold_6099_, v___x_6101_);
    v___x_6103_ = lean_uint64_to_usize(v___x_6102_);
    v___x_6104_ = lean_usize_of_nat(v___x_6095_);
    v___x_6105_ = 1usize;
    v___x_6106_ = lean_usize_sub(v___x_6104_, v___x_6105_);
    v___x_6107_ = lean_usize_land(v___x_6103_, v___x_6106_);
    v___x_6108_ = lean_array_uget_borrowed(v_buckets_6094_, v___x_6107_);
    v___x_6109_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_6093_, v___x_6108_);
    return v___x_6109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg___boxed(
    mut v_m_6110_: *mut crate::leanh::LeanObject,
    mut v_a_6111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6112_: u8 = 0;
    let mut v_r_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6112_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_6110_, v_a_6111_);
    crate::leanh::lean_dec_ref(v_a_6111_);
    crate::leanh::lean_dec_ref(v_m_6110_);
    v_r_6113_ = crate::leanh::lean_box((v_res_6112_) as usize);
    return v_r_6113_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(
    mut v_e_6114_: *mut crate::leanh::LeanObject,
    mut v_a_6115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: u8 = 0;
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6125_: u8 = 0;
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6134_: u8 = 0;
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6117_ = lean_st_ref_get(v_a_6115_);
                v_checked_6118_ = crate::leanh::lean_ctor_get(v___x_6117_, 1);
                crate::leanh::lean_inc_ref(v_checked_6118_);
                crate::leanh::lean_dec(v___x_6117_);
                v___x_6119_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_checked_6118_, v_e_6114_);
                crate::leanh::lean_dec_ref(v_checked_6118_);
                if v___x_6119_ == 0 {
                    v___x_6120_ = lean_st_ref_take(v_a_6115_);
                    v_visited_6121_ = crate::leanh::lean_ctor_get(v___x_6120_, 0);
                    v_checked_6122_ = crate::leanh::lean_ctor_get(v___x_6120_, 1);
                    v_isSharedCheck_6134_ = (!crate::leanh::lean_is_exclusive(v___x_6120_)) as u8;
                    if v_isSharedCheck_6134_ == 0 {
                        v___x_6124_ = v___x_6120_;
                        v_isShared_6125_ = v_isSharedCheck_6134_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_checked_6122_);
                        crate::leanh::lean_inc(v_visited_6121_);
                        crate::leanh::lean_dec(v___x_6120_);
                        v___x_6124_ = crate::leanh::lean_box(0);
                        v_isShared_6125_ = v_isSharedCheck_6134_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6114_);
                    v___x_6135_ = crate::leanh::lean_box((v___x_6119_) as usize);
                    v___x_6136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6136_, 0, v___x_6135_);
                    return v___x_6136_;
                }
            }
            1 => {
                v___x_6126_ = crate::leanh::lean_box(0);
                v___x_6127_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_checked_6122_, v_e_6114_, v___x_6126_);
                if v_isShared_6125_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6124_, 1, v___x_6127_);
                    v___x_6129_ = v___x_6124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6133_, 0, v_visited_6121_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6133_, 1, v___x_6127_);
                    v___x_6129_ = v_reuseFailAlloc_6133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6130_ = lean_st_ref_set(v_a_6115_, v___x_6129_);
                v___x_6131_ = crate::leanh::lean_box((v___x_6119_) as usize);
                v___x_6132_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6132_, 0, v___x_6131_);
                return v___x_6132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg___boxed(
    mut v_e_6137_: *mut crate::leanh::LeanObject,
    mut v_a_6138_: *mut crate::leanh::LeanObject,
    mut v___y_6139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6140_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_6137_, v_a_6138_);
    crate::leanh::lean_dec(v_a_6138_);
    return v_res_6140_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(
    mut v_p_6141_: *mut crate::leanh::LeanObject,
    mut v_f_6142_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_6143_: u8,
    mut v_e_6144_: *mut crate::leanh::LeanObject,
    mut v_a_6145_: *mut crate::leanh::LeanObject,
    mut v___y_6146_: *mut crate::leanh::LeanObject,
    mut v___y_6147_: *mut crate::leanh::LeanObject,
    mut v___y_6148_: *mut crate::leanh::LeanObject,
    mut v___y_6149_: *mut crate::leanh::LeanObject,
    mut v___y_6150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6194_: u8 = 0;
    let mut v___x_6195_: u8 = 0;
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: u8 = 0;
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: u8 = 0;
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6204_: u8 = 0;
    let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6209_: u8 = 0;
    let mut v_unused_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6214_: u8 = 0;
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6218_: u8 = 0;
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6223_: u8 = 0;
    let mut v_a_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6227_: u8 = 0;
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_6144_);
                v___x_6190_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_6144_, v_a_6145_);
                if crate::leanh::lean_obj_tag(v___x_6190_) == 0 {
                    v_a_6191_ = crate::leanh::lean_ctor_get(v___x_6190_, 0);
                    v_isSharedCheck_6223_ = (!crate::leanh::lean_is_exclusive(v___x_6190_)) as u8;
                    if v_isSharedCheck_6223_ == 0 {
                        v___x_6193_ = v___x_6190_;
                        v_isShared_6194_ = v_isSharedCheck_6223_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6191_);
                        crate::leanh::lean_dec(v___x_6190_);
                        v___x_6193_ = crate::leanh::lean_box(0);
                        v_isShared_6194_ = v_isSharedCheck_6223_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6144_);
                    crate::leanh::lean_dec_ref(v_f_6142_);
                    crate::leanh::lean_dec_ref(v_p_6141_);
                    v_a_6224_ = crate::leanh::lean_ctor_get(v___x_6190_, 0);
                    v_isSharedCheck_6231_ = (!crate::leanh::lean_is_exclusive(v___x_6190_)) as u8;
                    if v_isSharedCheck_6231_ == 0 {
                        v___x_6226_ = v___x_6190_;
                        v_isShared_6227_ = v_isSharedCheck_6231_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6224_);
                        crate::leanh::lean_dec(v___x_6190_);
                        v___x_6226_ = crate::leanh::lean_box(0);
                        v_isShared_6227_ = v_isSharedCheck_6231_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_f_6142_);
                crate::leanh::lean_inc_ref(v_p_6141_);
                v___x_6161_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6141_, v_f_6142_, v_stopWhenVisited_6143_, v_d_6158_, v___y_6160_, v___y_6157_, v___y_6153_, v___y_6155_, v___y_6156_, v___y_6154_);
                if crate::leanh::lean_obj_tag(v___x_6161_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6161_, 1);
                    v_e_6144_ = v_b_6159_;
                    v_a_6145_ = v___y_6160_;
                    v___y_6146_ = v___y_6157_;
                    v___y_6147_ = v___y_6153_;
                    v___y_6148_ = v___y_6155_;
                    v___y_6149_ = v___y_6156_;
                    v___y_6150_ = v___y_6154_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_6159_);
                    crate::leanh::lean_dec_ref(v_f_6142_);
                    crate::leanh::lean_dec_ref(v_p_6141_);
                    return v___x_6161_;
                }
            }
            2 => match crate::leanh::lean_obj_tag(v_e_6144_) {
                7 => {
                    v_binderType_6170_ = crate::leanh::lean_ctor_get(v_e_6144_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_6170_);
                    v_body_6171_ = crate::leanh::lean_ctor_get(v_e_6144_, 2);
                    crate::leanh::lean_inc_ref(v_body_6171_);
                    crate::leanh::lean_dec_ref_known(v_e_6144_, 3);
                    v___y_6153_ = v___y_6166_;
                    v___y_6154_ = v___y_6169_;
                    v___y_6155_ = v___y_6167_;
                    v___y_6156_ = v___y_6168_;
                    v___y_6157_ = v___y_6165_;
                    v_d_6158_ = v_binderType_6170_;
                    v_b_6159_ = v_body_6171_;
                    v___y_6160_ = v___y_6164_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_6172_ = crate::leanh::lean_ctor_get(v_e_6144_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_6172_);
                    v_body_6173_ = crate::leanh::lean_ctor_get(v_e_6144_, 2);
                    crate::leanh::lean_inc_ref(v_body_6173_);
                    crate::leanh::lean_dec_ref_known(v_e_6144_, 3);
                    v___y_6153_ = v___y_6166_;
                    v___y_6154_ = v___y_6169_;
                    v___y_6155_ = v___y_6167_;
                    v___y_6156_ = v___y_6168_;
                    v___y_6157_ = v___y_6165_;
                    v_d_6158_ = v_binderType_6172_;
                    v_b_6159_ = v_body_6173_;
                    v___y_6160_ = v___y_6164_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_6174_ = crate::leanh::lean_ctor_get(v_e_6144_, 1);
                    crate::leanh::lean_inc_ref(v_type_6174_);
                    v_value_6175_ = crate::leanh::lean_ctor_get(v_e_6144_, 2);
                    crate::leanh::lean_inc_ref(v_value_6175_);
                    v_body_6176_ = crate::leanh::lean_ctor_get(v_e_6144_, 3);
                    crate::leanh::lean_inc_ref(v_body_6176_);
                    crate::leanh::lean_dec_ref_known(v_e_6144_, 4);
                    crate::leanh::lean_inc_ref(v_f_6142_);
                    crate::leanh::lean_inc_ref(v_p_6141_);
                    v___x_6177_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6141_, v_f_6142_, v_stopWhenVisited_6143_, v_type_6174_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
                    if crate::leanh::lean_obj_tag(v___x_6177_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6177_, 1);
                        crate::leanh::lean_inc_ref(v_f_6142_);
                        crate::leanh::lean_inc_ref(v_p_6141_);
                        v___x_6178_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6141_, v_f_6142_, v_stopWhenVisited_6143_, v_value_6175_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
                        if crate::leanh::lean_obj_tag(v___x_6178_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6178_, 1);
                            v_e_6144_ = v_body_6176_;
                            v_a_6145_ = v___y_6164_;
                            v___y_6146_ = v___y_6165_;
                            v___y_6147_ = v___y_6166_;
                            v___y_6148_ = v___y_6167_;
                            v___y_6149_ = v___y_6168_;
                            v___y_6150_ = v___y_6169_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_body_6176_);
                            crate::leanh::lean_dec_ref(v_f_6142_);
                            crate::leanh::lean_dec_ref(v_p_6141_);
                            return v___x_6178_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_6176_);
                        crate::leanh::lean_dec_ref(v_value_6175_);
                        crate::leanh::lean_dec_ref(v_f_6142_);
                        crate::leanh::lean_dec_ref(v_p_6141_);
                        return v___x_6177_;
                    }
                }
                5 => {
                    v_fn_6180_ = crate::leanh::lean_ctor_get(v_e_6144_, 0);
                    crate::leanh::lean_inc_ref(v_fn_6180_);
                    v_arg_6181_ = crate::leanh::lean_ctor_get(v_e_6144_, 1);
                    crate::leanh::lean_inc_ref(v_arg_6181_);
                    crate::leanh::lean_dec_ref_known(v_e_6144_, 2);
                    crate::leanh::lean_inc_ref(v_f_6142_);
                    crate::leanh::lean_inc_ref(v_p_6141_);
                    v___x_6182_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6141_, v_f_6142_, v_stopWhenVisited_6143_, v_fn_6180_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
                    if crate::leanh::lean_obj_tag(v___x_6182_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6182_, 1);
                        v_e_6144_ = v_arg_6181_;
                        v_a_6145_ = v___y_6164_;
                        v___y_6146_ = v___y_6165_;
                        v___y_6147_ = v___y_6166_;
                        v___y_6148_ = v___y_6167_;
                        v___y_6149_ = v___y_6168_;
                        v___y_6150_ = v___y_6169_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_6181_);
                        crate::leanh::lean_dec_ref(v_f_6142_);
                        crate::leanh::lean_dec_ref(v_p_6141_);
                        return v___x_6182_;
                    }
                }
                10 => {
                    v_expr_6184_ = crate::leanh::lean_ctor_get(v_e_6144_, 1);
                    crate::leanh::lean_inc_ref(v_expr_6184_);
                    crate::leanh::lean_dec_ref_known(v_e_6144_, 2);
                    v_e_6144_ = v_expr_6184_;
                    v_a_6145_ = v___y_6164_;
                    v___y_6146_ = v___y_6165_;
                    v___y_6147_ = v___y_6166_;
                    v___y_6148_ = v___y_6167_;
                    v___y_6149_ = v___y_6168_;
                    v___y_6150_ = v___y_6169_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_struct_6186_ = crate::leanh::lean_ctor_get(v_e_6144_, 2);
                    crate::leanh::lean_inc_ref(v_struct_6186_);
                    crate::leanh::lean_dec_ref_known(v_e_6144_, 3);
                    v_e_6144_ = v_struct_6186_;
                    v_a_6145_ = v___y_6164_;
                    v___y_6146_ = v___y_6165_;
                    v___y_6147_ = v___y_6166_;
                    v___y_6148_ = v___y_6167_;
                    v___y_6149_ = v___y_6168_;
                    v___y_6150_ = v___y_6169_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_6144_);
                    crate::leanh::lean_dec_ref(v_f_6142_);
                    crate::leanh::lean_dec_ref(v_p_6141_);
                    v___x_6188_ = crate::leanh::lean_box(0);
                    v___x_6189_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6189_, 0, v___x_6188_);
                    return v___x_6189_;
                }
            },
            3 => {
                v___x_6195_ = (crate::leanh::lean_unbox(v_a_6191_) as u8);
                crate::leanh::lean_dec(v_a_6191_);
                if v___x_6195_ == 0 {
                    crate::leanh::lean_del_object(v___x_6193_);
                    crate::leanh::lean_inc_ref(v_p_6141_);
                    crate::leanh::lean_inc_ref(v_e_6144_);
                    v___x_6196_ = crate::leanh::lean_apply_1(v_p_6141_, v_e_6144_);
                    v___x_6197_ = (crate::leanh::lean_unbox(v___x_6196_) as u8);
                    if v___x_6197_ == 0 {
                        v___y_6164_ = v_a_6145_;
                        v___y_6165_ = v___y_6146_;
                        v___y_6166_ = v___y_6147_;
                        v___y_6167_ = v___y_6148_;
                        v___y_6168_ = v___y_6149_;
                        v___y_6169_ = v___y_6150_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_e_6144_);
                        v___x_6198_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_6144_, v_a_6145_);
                        if crate::leanh::lean_obj_tag(v___x_6198_) == 0 {
                            v_a_6199_ = crate::leanh::lean_ctor_get(v___x_6198_, 0);
                            crate::leanh::lean_inc(v_a_6199_);
                            crate::leanh::lean_dec_ref_known(v___x_6198_, 1);
                            v___x_6200_ = (crate::leanh::lean_unbox(v_a_6199_) as u8);
                            crate::leanh::lean_dec(v_a_6199_);
                            if v___x_6200_ == 0 {
                                crate::leanh::lean_inc_ref(v_f_6142_);
                                crate::leanh::lean_inc(v___y_6150_);
                                crate::leanh::lean_inc_ref(v___y_6149_);
                                crate::leanh::lean_inc(v___y_6148_);
                                crate::leanh::lean_inc_ref(v___y_6147_);
                                crate::leanh::lean_inc(v___y_6146_);
                                crate::leanh::lean_inc_ref(v_e_6144_);
                                v___x_6201_ = crate::leanh::lean_apply_7(
                                    v_f_6142_,
                                    v_e_6144_,
                                    v___y_6146_,
                                    v___y_6147_,
                                    v___y_6148_,
                                    v___y_6149_,
                                    v___y_6150_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_6201_) == 0 {
                                    v_isSharedCheck_6209_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6201_)) as u8;
                                    if v_isSharedCheck_6209_ == 0 {
                                        v_unused_6210_ =
                                            crate::leanh::lean_ctor_get(v___x_6201_, 0);
                                        crate::leanh::lean_dec(v_unused_6210_);
                                        v___x_6203_ = v___x_6201_;
                                        v_isShared_6204_ = v_isSharedCheck_6209_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_6201_);
                                        v___x_6203_ = crate::leanh::lean_box(0);
                                        v_isShared_6204_ = v_isSharedCheck_6209_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_e_6144_);
                                    crate::leanh::lean_dec_ref(v_f_6142_);
                                    crate::leanh::lean_dec_ref(v_p_6141_);
                                    return v___x_6201_;
                                }
                            } else {
                                v___y_6164_ = v_a_6145_;
                                v___y_6165_ = v___y_6146_;
                                v___y_6166_ = v___y_6147_;
                                v___y_6167_ = v___y_6148_;
                                v___y_6168_ = v___y_6149_;
                                v___y_6169_ = v___y_6150_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_6144_);
                            crate::leanh::lean_dec_ref(v_f_6142_);
                            crate::leanh::lean_dec_ref(v_p_6141_);
                            v_a_6211_ = crate::leanh::lean_ctor_get(v___x_6198_, 0);
                            v_isSharedCheck_6218_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6198_)) as u8;
                            if v_isSharedCheck_6218_ == 0 {
                                v___x_6213_ = v___x_6198_;
                                v_isShared_6214_ = v_isSharedCheck_6218_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6211_);
                                crate::leanh::lean_dec(v___x_6198_);
                                v___x_6213_ = crate::leanh::lean_box(0);
                                v_isShared_6214_ = v_isSharedCheck_6218_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_6144_);
                    crate::leanh::lean_dec_ref(v_f_6142_);
                    crate::leanh::lean_dec_ref(v_p_6141_);
                    v___x_6219_ = crate::leanh::lean_box(0);
                    if v_isShared_6194_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6193_, 0, v___x_6219_);
                        v___x_6221_ = v___x_6193_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6222_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6222_, 0, v___x_6219_);
                        v___x_6221_ = v_reuseFailAlloc_6222_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_stopWhenVisited_6143_ == 0 {
                    crate::leanh::lean_del_object(v___x_6203_);
                    v___y_6164_ = v_a_6145_;
                    v___y_6165_ = v___y_6146_;
                    v___y_6166_ = v___y_6147_;
                    v___y_6167_ = v___y_6148_;
                    v___y_6168_ = v___y_6149_;
                    v___y_6169_ = v___y_6150_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_6144_);
                    crate::leanh::lean_dec_ref(v_f_6142_);
                    crate::leanh::lean_dec_ref(v_p_6141_);
                    v___x_6205_ = crate::leanh::lean_box(0);
                    if v_isShared_6204_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6203_, 0, v___x_6205_);
                        v___x_6207_ = v___x_6203_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6208_, 0, v___x_6205_);
                        v___x_6207_ = v_reuseFailAlloc_6208_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_6207_;
            }
            6 => {
                if v_isShared_6214_ == 0 {
                    v___x_6216_ = v___x_6213_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6217_, 0, v_a_6211_);
                    v___x_6216_ = v_reuseFailAlloc_6217_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6216_;
            }
            8 => {
                return v___x_6221_;
            }
            9 => {
                if v_isShared_6227_ == 0 {
                    v___x_6229_ = v___x_6226_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6230_, 0, v_a_6224_);
                    v___x_6229_ = v_reuseFailAlloc_6230_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6229_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5___boxed(
    mut v_p_6232_: *mut crate::leanh::LeanObject,
    mut v_f_6233_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_6234_: *mut crate::leanh::LeanObject,
    mut v_e_6235_: *mut crate::leanh::LeanObject,
    mut v_a_6236_: *mut crate::leanh::LeanObject,
    mut v___y_6237_: *mut crate::leanh::LeanObject,
    mut v___y_6238_: *mut crate::leanh::LeanObject,
    mut v___y_6239_: *mut crate::leanh::LeanObject,
    mut v___y_6240_: *mut crate::leanh::LeanObject,
    mut v___y_6241_: *mut crate::leanh::LeanObject,
    mut v___y_6242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_6243_: u8 = 0;
    let mut v_res_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_6243_ = (crate::leanh::lean_unbox(v_stopWhenVisited_6234_) as u8);
    v_res_6244_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6232_, v_f_6233_, v_stopWhenVisited_boxed_6243_, v_e_6235_, v_a_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
    crate::leanh::lean_dec(v___y_6241_);
    crate::leanh::lean_dec_ref(v___y_6240_);
    crate::leanh::lean_dec(v___y_6239_);
    crate::leanh::lean_dec_ref(v___y_6238_);
    crate::leanh::lean_dec(v___y_6237_);
    crate::leanh::lean_dec(v_a_6236_);
    return v_res_6244_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3(
    mut v_p_6245_: *mut crate::leanh::LeanObject,
    mut v_f_6246_: *mut crate::leanh::LeanObject,
    mut v_e_6247_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_6248_: u8,
    mut v___y_6249_: *mut crate::leanh::LeanObject,
    mut v___y_6250_: *mut crate::leanh::LeanObject,
    mut v___y_6251_: *mut crate::leanh::LeanObject,
    mut v___y_6252_: *mut crate::leanh::LeanObject,
    mut v___y_6253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6261_: u8 = 0;
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6255_ = l_Lean_ForEachExprWhere_initCache;
                v___x_6256_ = lean_st_mk_ref(v___x_6255_);
                v___x_6257_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6245_, v_f_6246_, v_stopWhenVisited_6248_, v_e_6247_, v___x_6256_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
                if crate::leanh::lean_obj_tag(v___x_6257_) == 0 {
                    v_a_6258_ = crate::leanh::lean_ctor_get(v___x_6257_, 0);
                    v_isSharedCheck_6266_ = (!crate::leanh::lean_is_exclusive(v___x_6257_)) as u8;
                    if v_isSharedCheck_6266_ == 0 {
                        v___x_6260_ = v___x_6257_;
                        v_isShared_6261_ = v_isSharedCheck_6266_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6258_);
                        crate::leanh::lean_dec(v___x_6257_);
                        v___x_6260_ = crate::leanh::lean_box(0);
                        v_isShared_6261_ = v_isSharedCheck_6266_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6256_);
                    return v___x_6257_;
                }
            }
            1 => {
                v___x_6262_ = lean_st_ref_get(v___x_6256_);
                crate::leanh::lean_dec(v___x_6256_);
                crate::leanh::lean_dec(v___x_6262_);
                if v_isShared_6261_ == 0 {
                    v___x_6264_ = v___x_6260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6265_, 0, v_a_6258_);
                    v___x_6264_ = v_reuseFailAlloc_6265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3___boxed(
    mut v_p_6267_: *mut crate::leanh::LeanObject,
    mut v_f_6268_: *mut crate::leanh::LeanObject,
    mut v_e_6269_: *mut crate::leanh::LeanObject,
    mut v_stopWhenVisited_6270_: *mut crate::leanh::LeanObject,
    mut v___y_6271_: *mut crate::leanh::LeanObject,
    mut v___y_6272_: *mut crate::leanh::LeanObject,
    mut v___y_6273_: *mut crate::leanh::LeanObject,
    mut v___y_6274_: *mut crate::leanh::LeanObject,
    mut v___y_6275_: *mut crate::leanh::LeanObject,
    mut v___y_6276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stopWhenVisited_boxed_6277_: u8 = 0;
    let mut v_res_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_6277_ = (crate::leanh::lean_unbox(v_stopWhenVisited_6270_) as u8);
    v_res_6278_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3(v_p_6267_, v_f_6268_, v_e_6269_, v_stopWhenVisited_boxed_6277_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
    crate::leanh::lean_dec(v___y_6275_);
    crate::leanh::lean_dec_ref(v___y_6274_);
    crate::leanh::lean_dec(v___y_6273_);
    crate::leanh::lean_dec_ref(v___y_6272_);
    crate::leanh::lean_dec(v___y_6271_);
    return v_res_6278_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4(
    mut v_as_6280_: *mut crate::leanh::LeanObject,
    mut v_sz_6281_: usize,
    mut v_i_6282_: usize,
    mut v_b_6283_: *mut crate::leanh::LeanObject,
    mut v___y_6284_: *mut crate::leanh::LeanObject,
    mut v___y_6285_: *mut crate::leanh::LeanObject,
    mut v___y_6286_: *mut crate::leanh::LeanObject,
    mut v___y_6287_: *mut crate::leanh::LeanObject,
    mut v___y_6288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6290_: u8 = 0;
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: usize = 0;
    let mut v___x_6302_: usize = 0;
    let mut v_a_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6307_: u8 = 0;
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6311_: u8 = 0;
    let mut v_a_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6315_: u8 = 0;
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6290_ = lean_usize_dec_lt(v_i_6282_, v_sz_6281_);
                if v___x_6290_ == 0 {
                    v___x_6291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6291_, 0, v_b_6283_);
                    return v___x_6291_;
                } else {
                    v_a_6292_ = lean_array_uget_borrowed(v_as_6280_, v_i_6282_);
                    crate::leanh::lean_inc(v_a_6292_);
                    v___x_6293_ = l_Lean_FVarId_getType___redArg(
                        v_a_6292_,
                        v___y_6285_,
                        v___y_6287_,
                        v___y_6288_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6293_) == 0 {
                        v_a_6294_ = crate::leanh::lean_ctor_get(v___x_6293_, 0);
                        crate::leanh::lean_inc(v_a_6294_);
                        crate::leanh::lean_dec_ref_known(v___x_6293_, 1);
                        v___x_6295_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_a_6294_, v___y_6286_);
                        if crate::leanh::lean_obj_tag(v___x_6295_) == 0 {
                            v_a_6296_ = crate::leanh::lean_ctor_get(v___x_6295_, 0);
                            crate::leanh::lean_inc(v_a_6296_);
                            crate::leanh::lean_dec_ref_known(v___x_6295_, 1);
                            v___f_6297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0;
                            v___x_6298_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v_a_6292_);
                            v___f_6299_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed as *mut core::ffi::c_void, 9, 2);
                            crate::leanh::lean_closure_set(v___f_6299_, 0, v___x_6298_);
                            crate::leanh::lean_closure_set(v___f_6299_, 1, v_a_6292_);
                            v___x_6300_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3(v___f_6297_, v___f_6299_, v_a_6296_, v___x_6290_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_);
                            if crate::leanh::lean_obj_tag(v___x_6300_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6300_, 1);
                                v___x_6301_ = 1usize;
                                v___x_6302_ = lean_usize_add(v_i_6282_, v___x_6301_);
                                v_i_6282_ = v___x_6302_;
                                v_b_6283_ = v___x_6298_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_6300_;
                            }
                        } else {
                            v_a_6304_ = crate::leanh::lean_ctor_get(v___x_6295_, 0);
                            v_isSharedCheck_6311_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6295_)) as u8;
                            if v_isSharedCheck_6311_ == 0 {
                                v___x_6306_ = v___x_6295_;
                                v_isShared_6307_ = v_isSharedCheck_6311_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6304_);
                                crate::leanh::lean_dec(v___x_6295_);
                                v___x_6306_ = crate::leanh::lean_box(0);
                                v_isShared_6307_ = v_isSharedCheck_6311_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_6312_ = crate::leanh::lean_ctor_get(v___x_6293_, 0);
                        v_isSharedCheck_6319_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6293_)) as u8;
                        if v_isSharedCheck_6319_ == 0 {
                            v___x_6314_ = v___x_6293_;
                            v_isShared_6315_ = v_isSharedCheck_6319_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6312_);
                            crate::leanh::lean_dec(v___x_6293_);
                            v___x_6314_ = crate::leanh::lean_box(0);
                            v_isShared_6315_ = v_isSharedCheck_6319_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6307_ == 0 {
                    v___x_6309_ = v___x_6306_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_a_6304_);
                    v___x_6309_ = v_reuseFailAlloc_6310_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6309_;
            }
            3 => {
                if v_isShared_6315_ == 0 {
                    v___x_6317_ = v___x_6314_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6318_, 0, v_a_6312_);
                    v___x_6317_ = v_reuseFailAlloc_6318_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___boxed(
    mut v_as_6320_: *mut crate::leanh::LeanObject,
    mut v_sz_6321_: *mut crate::leanh::LeanObject,
    mut v_i_6322_: *mut crate::leanh::LeanObject,
    mut v_b_6323_: *mut crate::leanh::LeanObject,
    mut v___y_6324_: *mut crate::leanh::LeanObject,
    mut v___y_6325_: *mut crate::leanh::LeanObject,
    mut v___y_6326_: *mut crate::leanh::LeanObject,
    mut v___y_6327_: *mut crate::leanh::LeanObject,
    mut v___y_6328_: *mut crate::leanh::LeanObject,
    mut v___y_6329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6330_: usize = 0;
    let mut v_i_boxed_6331_: usize = 0;
    let mut v_res_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6330_ = crate::leanh::lean_unbox_usize(v_sz_6321_);
    crate::leanh::lean_dec(v_sz_6321_);
    v_i_boxed_6331_ = crate::leanh::lean_unbox_usize(v_i_6322_);
    crate::leanh::lean_dec(v_i_6322_);
    v_res_6332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4(v_as_6320_, v_sz_boxed_6330_, v_i_boxed_6331_, v_b_6323_, v___y_6324_, v___y_6325_, v___y_6326_, v___y_6327_, v___y_6328_);
    crate::leanh::lean_dec(v___y_6328_);
    crate::leanh::lean_dec_ref(v___y_6327_);
    crate::leanh::lean_dec(v___y_6326_);
    crate::leanh::lean_dec_ref(v___y_6325_);
    crate::leanh::lean_dec(v___y_6324_);
    crate::leanh::lean_dec_ref(v_as_6320_);
    return v_res_6332_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0(
    mut v___y_6333_: *mut crate::leanh::LeanObject,
    mut v___y_6334_: *mut crate::leanh::LeanObject,
    mut v___y_6335_: *mut crate::leanh::LeanObject,
    mut v___y_6336_: *mut crate::leanh::LeanObject,
    mut v___y_6337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6342_: usize = 0;
    let mut v___x_6343_: usize = 0;
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6347_: u8 = 0;
    let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: u8 = 0;
    let mut v___x_6353_: u8 = 0;
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: u8 = 0;
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6363_: u8 = 0;
    let mut v_unused_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6368_: u8 = 0;
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6372_: u8 = 0;
    let mut v_a_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6376_: u8 = 0;
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6339_ =
                    l_Lean_Meta_getPropHyps(v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_);
                if crate::leanh::lean_obj_tag(v___x_6339_) == 0 {
                    v_a_6340_ = crate::leanh::lean_ctor_get(v___x_6339_, 0);
                    crate::leanh::lean_inc(v_a_6340_);
                    crate::leanh::lean_dec_ref_known(v___x_6339_, 1);
                    v___x_6341_ = crate::leanh::lean_box(0);
                    v_sz_6342_ = lean_array_size(v_a_6340_);
                    v___x_6343_ = 0usize;
                    v___x_6344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4(v_a_6340_, v_sz_6342_, v___x_6343_, v___x_6341_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_);
                    crate::leanh::lean_dec(v_a_6340_);
                    if crate::leanh::lean_obj_tag(v___x_6344_) == 0 {
                        v_isSharedCheck_6363_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6344_)) as u8;
                        if v_isSharedCheck_6363_ == 0 {
                            v_unused_6364_ = crate::leanh::lean_ctor_get(v___x_6344_, 0);
                            crate::leanh::lean_dec(v_unused_6364_);
                            v___x_6346_ = v___x_6344_;
                            v_isShared_6347_ = v_isSharedCheck_6363_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6344_);
                            v___x_6346_ = crate::leanh::lean_box(0);
                            v_isShared_6347_ = v_isSharedCheck_6363_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6365_ = crate::leanh::lean_ctor_get(v___x_6344_, 0);
                        v_isSharedCheck_6372_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6344_)) as u8;
                        if v_isSharedCheck_6372_ == 0 {
                            v___x_6367_ = v___x_6344_;
                            v_isShared_6368_ = v_isSharedCheck_6372_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6365_);
                            crate::leanh::lean_dec(v___x_6344_);
                            v___x_6367_ = crate::leanh::lean_box(0);
                            v_isShared_6368_ = v_isSharedCheck_6372_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_6373_ = crate::leanh::lean_ctor_get(v___x_6339_, 0);
                    v_isSharedCheck_6380_ = (!crate::leanh::lean_is_exclusive(v___x_6339_)) as u8;
                    if v_isSharedCheck_6380_ == 0 {
                        v___x_6375_ = v___x_6339_;
                        v_isShared_6376_ = v_isSharedCheck_6380_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6373_);
                        crate::leanh::lean_dec(v___x_6339_);
                        v___x_6375_ = crate::leanh::lean_box(0);
                        v_isShared_6376_ = v_isSharedCheck_6380_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6348_ = lean_st_ref_get(v___y_6333_);
                v_relevantTerms_6349_ = crate::leanh::lean_ctor_get(v___x_6348_, 0);
                crate::leanh::lean_inc_ref(v_relevantTerms_6349_);
                crate::leanh::lean_dec(v___x_6348_);
                v_size_6350_ = crate::leanh::lean_ctor_get(v_relevantTerms_6349_, 0);
                crate::leanh::lean_inc(v_size_6350_);
                crate::leanh::lean_dec_ref(v_relevantTerms_6349_);
                v___x_6351_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6352_ = lean_nat_dec_eq(v_size_6350_, v___x_6351_);
                crate::leanh::lean_dec(v_size_6350_);
                if v___x_6352_ == 0 {
                    v___x_6353_ = 1;
                    v___x_6354_ = crate::leanh::lean_box((v___x_6353_) as usize);
                    if v_isShared_6347_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6346_, 0, v___x_6354_);
                        v___x_6356_ = v___x_6346_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6357_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6357_, 0, v___x_6354_);
                        v___x_6356_ = v_reuseFailAlloc_6357_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6358_ = 0;
                    v___x_6359_ = crate::leanh::lean_box((v___x_6358_) as usize);
                    if v_isShared_6347_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6346_, 0, v___x_6359_);
                        v___x_6361_ = v___x_6346_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6362_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6362_, 0, v___x_6359_);
                        v___x_6361_ = v_reuseFailAlloc_6362_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6356_;
            }
            3 => {
                return v___x_6361_;
            }
            4 => {
                if v_isShared_6368_ == 0 {
                    v___x_6370_ = v___x_6367_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6371_, 0, v_a_6365_);
                    v___x_6370_ = v_reuseFailAlloc_6371_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6370_;
            }
            6 => {
                if v_isShared_6376_ == 0 {
                    v___x_6378_ = v___x_6375_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6379_, 0, v_a_6373_);
                    v___x_6378_ = v_reuseFailAlloc_6379_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0___boxed(
    mut v___y_6381_: *mut crate::leanh::LeanObject,
    mut v___y_6382_: *mut crate::leanh::LeanObject,
    mut v___y_6383_: *mut crate::leanh::LeanObject,
    mut v___y_6384_: *mut crate::leanh::LeanObject,
    mut v___y_6385_: *mut crate::leanh::LeanObject,
    mut v___y_6386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6387_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0(v___y_6381_, v___y_6382_, v___y_6383_, v___y_6384_, v___y_6385_);
    crate::leanh::lean_dec(v___y_6385_);
    crate::leanh::lean_dec_ref(v___y_6384_);
    crate::leanh::lean_dec(v___y_6383_);
    crate::leanh::lean_dec_ref(v___y_6382_);
    crate::leanh::lean_dec(v___y_6381_);
    return v_res_6387_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize(
    mut v_goal_6389_: *mut crate::leanh::LeanObject,
    mut v_a_6390_: *mut crate::leanh::LeanObject,
    mut v_a_6391_: *mut crate::leanh::LeanObject,
    mut v_a_6392_: *mut crate::leanh::LeanObject,
    mut v_a_6393_: *mut crate::leanh::LeanObject,
    mut v_a_6394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6396_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0;
    v___x_6397_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_6389_, v___f_6396_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_);
    return v___x_6397_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___boxed(
    mut v_goal_6398_: *mut crate::leanh::LeanObject,
    mut v_a_6399_: *mut crate::leanh::LeanObject,
    mut v_a_6400_: *mut crate::leanh::LeanObject,
    mut v_a_6401_: *mut crate::leanh::LeanObject,
    mut v_a_6402_: *mut crate::leanh::LeanObject,
    mut v_a_6403_: *mut crate::leanh::LeanObject,
    mut v_a_6404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6405_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize(v_goal_6398_, v_a_6399_, v_a_6400_, v_a_6401_, v_a_6402_, v_a_6403_);
    crate::leanh::lean_dec(v_a_6403_);
    crate::leanh::lean_dec_ref(v_a_6402_);
    crate::leanh::lean_dec(v_a_6401_);
    crate::leanh::lean_dec_ref(v_a_6400_);
    crate::leanh::lean_dec(v_a_6399_);
    return v_res_6405_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0(
    mut v_00_u03b2_6406_: *mut crate::leanh::LeanObject,
    mut v_m_6407_: *mut crate::leanh::LeanObject,
    mut v_a_6408_: *mut crate::leanh::LeanObject,
    mut v_b_6409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6410_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_m_6407_, v_a_6408_, v_b_6409_);
    return v___x_6410_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1(
    mut v_00_u03b2_6411_: *mut crate::leanh::LeanObject,
    mut v_m_6412_: *mut crate::leanh::LeanObject,
    mut v_a_6413_: *mut crate::leanh::LeanObject,
    mut v_b_6414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6415_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_m_6412_, v_a_6413_, v_b_6414_);
    return v___x_6415_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(
    mut v_00_u03b2_6416_: *mut crate::leanh::LeanObject,
    mut v_a_6417_: *mut crate::leanh::LeanObject,
    mut v_x_6418_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6419_: u8 = 0;
    v___x_6419_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_6417_, v_x_6418_);
    return v___x_6419_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___boxed(
    mut v_00_u03b2_6420_: *mut crate::leanh::LeanObject,
    mut v_a_6421_: *mut crate::leanh::LeanObject,
    mut v_x_6422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6423_: u8 = 0;
    let mut v_r_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6423_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(v_00_u03b2_6420_, v_a_6421_, v_x_6422_);
    crate::leanh::lean_dec(v_x_6422_);
    crate::leanh::lean_dec(v_a_6421_);
    v_r_6424_ = crate::leanh::lean_box((v_res_6423_) as usize);
    return v_r_6424_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2(
    mut v_00_u03b2_6425_: *mut crate::leanh::LeanObject,
    mut v_data_6426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6427_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_data_6426_);
    return v___x_6427_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(
    mut v_e_6428_: *mut crate::leanh::LeanObject,
    mut v_a_6429_: *mut crate::leanh::LeanObject,
    mut v___y_6430_: *mut crate::leanh::LeanObject,
    mut v___y_6431_: *mut crate::leanh::LeanObject,
    mut v___y_6432_: *mut crate::leanh::LeanObject,
    mut v___y_6433_: *mut crate::leanh::LeanObject,
    mut v___y_6434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6436_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_6428_, v_a_6429_);
    return v___x_6436_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___boxed(
    mut v_e_6437_: *mut crate::leanh::LeanObject,
    mut v_a_6438_: *mut crate::leanh::LeanObject,
    mut v___y_6439_: *mut crate::leanh::LeanObject,
    mut v___y_6440_: *mut crate::leanh::LeanObject,
    mut v___y_6441_: *mut crate::leanh::LeanObject,
    mut v___y_6442_: *mut crate::leanh::LeanObject,
    mut v___y_6443_: *mut crate::leanh::LeanObject,
    mut v___y_6444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6445_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(v_e_6437_, v_a_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_, v___y_6443_);
    crate::leanh::lean_dec(v___y_6443_);
    crate::leanh::lean_dec_ref(v___y_6442_);
    crate::leanh::lean_dec(v___y_6441_);
    crate::leanh::lean_dec_ref(v___y_6440_);
    crate::leanh::lean_dec(v___y_6439_);
    crate::leanh::lean_dec(v_a_6438_);
    return v_res_6445_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4(
    mut v_00_u03b2_6446_: *mut crate::leanh::LeanObject,
    mut v_i_6447_: *mut crate::leanh::LeanObject,
    mut v_source_6448_: *mut crate::leanh::LeanObject,
    mut v_target_6449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6450_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v_i_6447_, v_source_6448_, v_target_6449_);
    return v___x_6450_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(
    mut v_e_6451_: *mut crate::leanh::LeanObject,
    mut v_a_6452_: *mut crate::leanh::LeanObject,
    mut v___y_6453_: *mut crate::leanh::LeanObject,
    mut v___y_6454_: *mut crate::leanh::LeanObject,
    mut v___y_6455_: *mut crate::leanh::LeanObject,
    mut v___y_6456_: *mut crate::leanh::LeanObject,
    mut v___y_6457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6459_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_6451_, v_a_6452_);
    return v___x_6459_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___boxed(
    mut v_e_6460_: *mut crate::leanh::LeanObject,
    mut v_a_6461_: *mut crate::leanh::LeanObject,
    mut v___y_6462_: *mut crate::leanh::LeanObject,
    mut v___y_6463_: *mut crate::leanh::LeanObject,
    mut v___y_6464_: *mut crate::leanh::LeanObject,
    mut v___y_6465_: *mut crate::leanh::LeanObject,
    mut v___y_6466_: *mut crate::leanh::LeanObject,
    mut v___y_6467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6468_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(v_e_6460_, v_a_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_);
    crate::leanh::lean_dec(v___y_6466_);
    crate::leanh::lean_dec_ref(v___y_6465_);
    crate::leanh::lean_dec(v___y_6464_);
    crate::leanh::lean_dec_ref(v___y_6463_);
    crate::leanh::lean_dec(v___y_6462_);
    crate::leanh::lean_dec(v_a_6461_);
    return v_res_6468_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7(
    mut v_00_u03b2_6469_: *mut crate::leanh::LeanObject,
    mut v_x_6470_: *mut crate::leanh::LeanObject,
    mut v_x_6471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6472_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_x_6470_, v_x_6471_);
    return v___x_6472_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(
    mut v_00_u03b2_6473_: *mut crate::leanh::LeanObject,
    mut v_m_6474_: *mut crate::leanh::LeanObject,
    mut v_a_6475_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6476_: u8 = 0;
    v___x_6476_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_6474_, v_a_6475_);
    return v___x_6476_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___boxed(
    mut v_00_u03b2_6477_: *mut crate::leanh::LeanObject,
    mut v_m_6478_: *mut crate::leanh::LeanObject,
    mut v_a_6479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6480_: u8 = 0;
    let mut v_r_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6480_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_6477_, v_m_6478_, v_a_6479_);
    crate::leanh::lean_dec_ref(v_a_6479_);
    crate::leanh::lean_dec_ref(v_m_6478_);
    v_r_6481_ = crate::leanh::lean_box((v_res_6480_) as usize);
    return v_r_6481_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize(
    mut v_goal_6482_: *mut crate::leanh::LeanObject,
    mut v_a_6483_: *mut crate::leanh::LeanObject,
    mut v_a_6484_: *mut crate::leanh::LeanObject,
    mut v_a_6485_: *mut crate::leanh::LeanObject,
    mut v_a_6486_: *mut crate::leanh::LeanObject,
    mut v_a_6487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6493_: u8 = 0;
    let mut v___x_6494_: u8 = 0;
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6499_: u8 = 0;
    let mut v_a_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6503_: u8 = 0;
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_goal_6482_);
                v___x_6489_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize(v_goal_6482_, v_a_6483_, v_a_6484_, v_a_6485_, v_a_6486_, v_a_6487_);
                if crate::leanh::lean_obj_tag(v___x_6489_) == 0 {
                    v_a_6490_ = crate::leanh::lean_ctor_get(v___x_6489_, 0);
                    v_isSharedCheck_6499_ = (!crate::leanh::lean_is_exclusive(v___x_6489_)) as u8;
                    if v_isSharedCheck_6499_ == 0 {
                        v___x_6492_ = v___x_6489_;
                        v_isShared_6493_ = v_isSharedCheck_6499_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6490_);
                        crate::leanh::lean_dec(v___x_6489_);
                        v___x_6492_ = crate::leanh::lean_box(0);
                        v_isShared_6493_ = v_isSharedCheck_6499_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_6482_);
                    v_a_6500_ = crate::leanh::lean_ctor_get(v___x_6489_, 0);
                    v_isSharedCheck_6507_ = (!crate::leanh::lean_is_exclusive(v___x_6489_)) as u8;
                    if v_isSharedCheck_6507_ == 0 {
                        v___x_6502_ = v___x_6489_;
                        v_isShared_6503_ = v_isSharedCheck_6507_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6500_);
                        crate::leanh::lean_dec(v___x_6489_);
                        v___x_6502_ = crate::leanh::lean_box(0);
                        v_isShared_6503_ = v_isSharedCheck_6507_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6494_ = (crate::leanh::lean_unbox(v_a_6490_) as u8);
                crate::leanh::lean_dec(v_a_6490_);
                if v___x_6494_ == 0 {
                    if v_isShared_6493_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6492_, 0, v_goal_6482_);
                        v___x_6496_ = v___x_6492_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6497_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6497_, 0, v_goal_6482_);
                        v___x_6496_ = v_reuseFailAlloc_6497_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6492_);
                    v___x_6498_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize(v_goal_6482_, v_a_6483_, v_a_6484_, v_a_6485_, v_a_6486_, v_a_6487_);
                    return v___x_6498_;
                }
            }
            2 => {
                return v___x_6496_;
            }
            3 => {
                if v_isShared_6503_ == 0 {
                    v___x_6505_ = v___x_6502_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6506_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6506_, 0, v_a_6500_);
                    v___x_6505_ = v_reuseFailAlloc_6506_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize___boxed(
    mut v_goal_6508_: *mut crate::leanh::LeanObject,
    mut v_a_6509_: *mut crate::leanh::LeanObject,
    mut v_a_6510_: *mut crate::leanh::LeanObject,
    mut v_a_6511_: *mut crate::leanh::LeanObject,
    mut v_a_6512_: *mut crate::leanh::LeanObject,
    mut v_a_6513_: *mut crate::leanh::LeanObject,
    mut v_a_6514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6515_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize(v_goal_6508_, v_a_6509_, v_a_6510_, v_a_6511_, v_a_6512_, v_a_6513_);
    crate::leanh::lean_dec(v_a_6513_);
    crate::leanh::lean_dec_ref(v_a_6512_);
    crate::leanh::lean_dec(v_a_6511_);
    crate::leanh::lean_dec_ref(v_a_6510_);
    crate::leanh::lean_dec(v_a_6509_);
    return v_res_6515_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6518_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6518_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6519_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1,
    );
    v___x_6520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6520_, 0, v___x_6519_);
    return v___x_6520_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6521_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6522_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2,
    );
    v___x_6523_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6523_, 0, v___x_6522_);
    crate::leanh::lean_ctor_set(v___x_6523_, 1, v___x_6521_);
    return v___x_6523_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6524_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6525_ = lean_mk_empty_array_with_capacity(v___x_6524_);
    v___x_6526_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6526_, 0, v___x_6525_);
    return v___x_6526_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6527_: usize = 0;
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6527_ = 5usize;
    v___x_6528_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6529_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6530_ = lean_mk_empty_array_with_capacity(v___x_6529_);
    v___x_6531_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4,
    );
    v___x_6532_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_6532_, 0, v___x_6531_);
    crate::leanh::lean_ctor_set(v___x_6532_, 1, v___x_6530_);
    crate::leanh::lean_ctor_set(v___x_6532_, 2, v___x_6528_);
    crate::leanh::lean_ctor_set(v___x_6532_, 3, v___x_6528_);
    crate::leanh::lean_ctor_set_usize(v___x_6532_, 4, v___x_6527_);
    return v___x_6532_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6533_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5,
    );
    v___x_6534_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2,
    );
    v___x_6535_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6535_, 0, v___x_6534_);
    crate::leanh::lean_ctor_set(v___x_6535_, 1, v___x_6534_);
    crate::leanh::lean_ctor_set(v___x_6535_, 2, v___x_6534_);
    crate::leanh::lean_ctor_set(v___x_6535_, 3, v___x_6533_);
    return v___x_6535_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6536_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6,
    );
    v___x_6537_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3,
    );
    v___x_6538_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6538_, 0, v___x_6537_);
    crate::leanh::lean_ctor_set(v___x_6538_, 1, v___x_6536_);
    return v___x_6538_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6539_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
    v___x_6540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6540_, 0, v___x_6539_);
    crate::leanh::lean_ctor_set(v___x_6540_, 1, v___x_6539_);
    return v___x_6540_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(
    mut v_goal_6541_: *mut crate::leanh::LeanObject,
    mut v___y_6542_: *mut crate::leanh::LeanObject,
    mut v___y_6543_: *mut crate::leanh::LeanObject,
    mut v___y_6544_: *mut crate::leanh::LeanObject,
    mut v___y_6545_: *mut crate::leanh::LeanObject,
    mut v___y_6546_: *mut crate::leanh::LeanObject,
    mut v___y_6547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: u8 = 0;
    let mut v___x_6557_: u8 = 0;
    let mut v___x_6558_: u8 = 0;
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6575_: u8 = 0;
    let mut v_fst_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6580_: u8 = 0;
    let mut v_snd_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6588_: u8 = 0;
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6596_: u8 = 0;
    let mut v_a_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6600_: u8 = 0;
    let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6604_: u8 = 0;
    let mut v_isSharedCheck_6605_: u8 = 0;
    let mut v___x_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6609_: u8 = 0;
    let mut v_a_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6613_: u8 = 0;
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6617_: u8 = 0;
    let mut v_a_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6621_: u8 = 0;
    let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6625_: u8 = 0;
    let mut v_a_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6629_: u8 = 0;
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6633_: u8 = 0;
    let mut v_a_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6637_: u8 = 0;
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6641_: u8 = 0;
    let mut v_a_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6645_: u8 = 0;
    let mut v___x_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6549_ = l_Lean_Meta_Tactic_BVDecide_intToBitVecExt;
                v___x_6550_ =
                    l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_6549_, v___y_6547_);
                if crate::leanh::lean_obj_tag(v___x_6550_) == 0 {
                    v_a_6551_ = crate::leanh::lean_ctor_get(v___x_6550_, 0);
                    crate::leanh::lean_inc(v_a_6551_);
                    crate::leanh::lean_dec_ref_known(v___x_6550_, 1);
                    v___x_6552_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_6547_);
                    if crate::leanh::lean_obj_tag(v___x_6552_) == 0 {
                        v_a_6553_ = crate::leanh::lean_ctor_get(v___x_6552_, 0);
                        crate::leanh::lean_inc(v_a_6553_);
                        crate::leanh::lean_dec_ref_known(v___x_6552_, 1);
                        v_maxSteps_6554_ = crate::leanh::lean_ctor_get(v___y_6542_, 1);
                        v___x_6555_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_6556_ = 0;
                        v___x_6557_ = 1;
                        v___x_6558_ = 0;
                        v___x_6559_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_maxSteps_6554_);
                        v___x_6560_ = crate::leanh::lean_alloc_ctor(0, 3, (29) as u32);
                        crate::leanh::lean_ctor_set(v___x_6560_, 0, v_maxSteps_6554_);
                        crate::leanh::lean_ctor_set(v___x_6560_, 1, v___x_6555_);
                        crate::leanh::lean_ctor_set(v___x_6560_, 2, v___x_6559_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 3) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 4) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 5) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 6) as u32,
                            v___x_6558_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 7) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 9) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 10) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 11) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 12) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 13) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 14) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 15) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 17) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 18) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 19) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 20) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 21) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 22) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 23) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 24) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 25) as u32,
                            v___x_6557_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 26) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 27) as u32,
                            v___x_6556_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 28) as u32,
                            v___x_6557_,
                        );
                        v___x_6561_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6562_ = lean_mk_empty_array_with_capacity(v___x_6561_);
                        v___x_6563_ = lean_array_push(v___x_6562_, v_a_6551_);
                        v___x_6564_ = l_Lean_Options_empty;
                        v___x_6565_ = l_Lean_Meta_Simp_mkContext___redArg(
                            v___x_6560_,
                            v___x_6563_,
                            v_a_6553_,
                            v___x_6564_,
                            v___y_6544_,
                            v___y_6546_,
                            v___y_6547_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6565_) == 0 {
                            v_a_6566_ = crate::leanh::lean_ctor_get(v___x_6565_, 0);
                            crate::leanh::lean_inc(v_a_6566_);
                            crate::leanh::lean_dec_ref_known(v___x_6565_, 1);
                            crate::leanh::lean_inc(v_goal_6541_);
                            v___x_6567_ = l_Lean_MVarId_getNondepPropHyps(
                                v_goal_6541_,
                                v___y_6544_,
                                v___y_6545_,
                                v___y_6546_,
                                v___y_6547_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6567_) == 0 {
                                v_a_6568_ = crate::leanh::lean_ctor_get(v___x_6567_, 0);
                                crate::leanh::lean_inc(v_a_6568_);
                                crate::leanh::lean_dec_ref_known(v___x_6567_, 1);
                                v___x_6569_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0;
                                v___x_6570_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7);
                                v___x_6571_ = l_Lean_Meta_simpGoal(
                                    v_goal_6541_,
                                    v_a_6566_,
                                    v___x_6569_,
                                    v___x_6559_,
                                    v___x_6557_,
                                    v_a_6568_,
                                    v___x_6570_,
                                    v___y_6544_,
                                    v___y_6545_,
                                    v___y_6546_,
                                    v___y_6547_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_6571_) == 0 {
                                    v_a_6572_ = crate::leanh::lean_ctor_get(v___x_6571_, 0);
                                    v_isSharedCheck_6609_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6571_)) as u8;
                                    if v_isSharedCheck_6609_ == 0 {
                                        v___x_6574_ = v___x_6571_;
                                        v_isShared_6575_ = v_isSharedCheck_6609_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6572_);
                                        crate::leanh::lean_dec(v___x_6571_);
                                        v___x_6574_ = crate::leanh::lean_box(0);
                                        v_isShared_6575_ = v_isSharedCheck_6609_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_6610_ = crate::leanh::lean_ctor_get(v___x_6571_, 0);
                                    v_isSharedCheck_6617_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6571_)) as u8;
                                    if v_isSharedCheck_6617_ == 0 {
                                        v___x_6612_ = v___x_6571_;
                                        v_isShared_6613_ = v_isSharedCheck_6617_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6610_);
                                        crate::leanh::lean_dec(v___x_6571_);
                                        v___x_6612_ = crate::leanh::lean_box(0);
                                        v_isShared_6613_ = v_isSharedCheck_6617_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6566_);
                                crate::leanh::lean_dec(v_goal_6541_);
                                v_a_6618_ = crate::leanh::lean_ctor_get(v___x_6567_, 0);
                                v_isSharedCheck_6625_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6567_)) as u8;
                                if v_isSharedCheck_6625_ == 0 {
                                    v___x_6620_ = v___x_6567_;
                                    v_isShared_6621_ = v_isSharedCheck_6625_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6618_);
                                    crate::leanh::lean_dec(v___x_6567_);
                                    v___x_6620_ = crate::leanh::lean_box(0);
                                    v_isShared_6621_ = v_isSharedCheck_6625_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_goal_6541_);
                            v_a_6626_ = crate::leanh::lean_ctor_get(v___x_6565_, 0);
                            v_isSharedCheck_6633_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6565_)) as u8;
                            if v_isSharedCheck_6633_ == 0 {
                                v___x_6628_ = v___x_6565_;
                                v_isShared_6629_ = v_isSharedCheck_6633_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6626_);
                                crate::leanh::lean_dec(v___x_6565_);
                                v___x_6628_ = crate::leanh::lean_box(0);
                                v_isShared_6629_ = v_isSharedCheck_6633_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6551_);
                        crate::leanh::lean_dec(v_goal_6541_);
                        v_a_6634_ = crate::leanh::lean_ctor_get(v___x_6552_, 0);
                        v_isSharedCheck_6641_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6552_)) as u8;
                        if v_isSharedCheck_6641_ == 0 {
                            v___x_6636_ = v___x_6552_;
                            v_isShared_6637_ = v_isSharedCheck_6641_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6634_);
                            crate::leanh::lean_dec(v___x_6552_);
                            v___x_6636_ = crate::leanh::lean_box(0);
                            v_isShared_6637_ = v_isSharedCheck_6641_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_goal_6541_);
                    v_a_6642_ = crate::leanh::lean_ctor_get(v___x_6550_, 0);
                    v_isSharedCheck_6649_ = (!crate::leanh::lean_is_exclusive(v___x_6550_)) as u8;
                    if v_isSharedCheck_6649_ == 0 {
                        v___x_6644_ = v___x_6550_;
                        v_isShared_6645_ = v_isSharedCheck_6649_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6642_);
                        crate::leanh::lean_dec(v___x_6550_);
                        v___x_6644_ = crate::leanh::lean_box(0);
                        v_isShared_6645_ = v_isSharedCheck_6649_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6576_ = crate::leanh::lean_ctor_get(v_a_6572_, 0);
                crate::leanh::lean_inc(v_fst_6576_);
                crate::leanh::lean_dec(v_a_6572_);
                if crate::leanh::lean_obj_tag(v_fst_6576_) == 1 {
                    crate::leanh::lean_del_object(v___x_6574_);
                    v_val_6577_ = crate::leanh::lean_ctor_get(v_fst_6576_, 0);
                    v_isSharedCheck_6605_ = (!crate::leanh::lean_is_exclusive(v_fst_6576_)) as u8;
                    if v_isSharedCheck_6605_ == 0 {
                        v___x_6579_ = v_fst_6576_;
                        v_isShared_6580_ = v_isSharedCheck_6605_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6577_);
                        crate::leanh::lean_dec(v_fst_6576_);
                        v___x_6579_ = crate::leanh::lean_box(0);
                        v_isShared_6580_ = v_isSharedCheck_6605_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6576_);
                    if v_isShared_6575_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6574_, 0, v___x_6559_);
                        v___x_6607_ = v___x_6574_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6608_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6608_, 0, v___x_6559_);
                        v___x_6607_ = v_reuseFailAlloc_6608_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_6581_ = crate::leanh::lean_ctor_get(v_val_6577_, 1);
                crate::leanh::lean_inc(v_snd_6581_);
                crate::leanh::lean_dec(v_val_6577_);
                v___x_6582_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8);
                v___x_6583_ = lean_st_mk_ref(v___x_6582_);
                v___x_6584_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize(v_snd_6581_, v___x_6583_, v___y_6544_, v___y_6545_, v___y_6546_, v___y_6547_);
                if crate::leanh::lean_obj_tag(v___x_6584_) == 0 {
                    v_a_6585_ = crate::leanh::lean_ctor_get(v___x_6584_, 0);
                    v_isSharedCheck_6596_ = (!crate::leanh::lean_is_exclusive(v___x_6584_)) as u8;
                    if v_isSharedCheck_6596_ == 0 {
                        v___x_6587_ = v___x_6584_;
                        v_isShared_6588_ = v_isSharedCheck_6596_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6585_);
                        crate::leanh::lean_dec(v___x_6584_);
                        v___x_6587_ = crate::leanh::lean_box(0);
                        v_isShared_6588_ = v_isSharedCheck_6596_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6583_);
                    crate::leanh::lean_del_object(v___x_6579_);
                    v_a_6597_ = crate::leanh::lean_ctor_get(v___x_6584_, 0);
                    v_isSharedCheck_6604_ = (!crate::leanh::lean_is_exclusive(v___x_6584_)) as u8;
                    if v_isSharedCheck_6604_ == 0 {
                        v___x_6599_ = v___x_6584_;
                        v_isShared_6600_ = v_isSharedCheck_6604_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6597_);
                        crate::leanh::lean_dec(v___x_6584_);
                        v___x_6599_ = crate::leanh::lean_box(0);
                        v_isShared_6600_ = v_isSharedCheck_6604_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6589_ = lean_st_ref_get(v___x_6583_);
                crate::leanh::lean_dec(v___x_6583_);
                crate::leanh::lean_dec(v___x_6589_);
                if v_isShared_6580_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6579_, 0, v_a_6585_);
                    v___x_6591_ = v___x_6579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6595_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6595_, 0, v_a_6585_);
                    v___x_6591_ = v_reuseFailAlloc_6595_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6588_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6587_, 0, v___x_6591_);
                    v___x_6593_ = v___x_6587_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6594_, 0, v___x_6591_);
                    v___x_6593_ = v_reuseFailAlloc_6594_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6593_;
            }
            6 => {
                if v_isShared_6600_ == 0 {
                    v___x_6602_ = v___x_6599_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6603_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6603_, 0, v_a_6597_);
                    v___x_6602_ = v_reuseFailAlloc_6603_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6602_;
            }
            8 => {
                return v___x_6607_;
            }
            9 => {
                if v_isShared_6613_ == 0 {
                    v___x_6615_ = v___x_6612_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6616_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6616_, 0, v_a_6610_);
                    v___x_6615_ = v_reuseFailAlloc_6616_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6615_;
            }
            11 => {
                if v_isShared_6621_ == 0 {
                    v___x_6623_ = v___x_6620_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6624_, 0, v_a_6618_);
                    v___x_6623_ = v_reuseFailAlloc_6624_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6623_;
            }
            13 => {
                if v_isShared_6629_ == 0 {
                    v___x_6631_ = v___x_6628_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6632_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6632_, 0, v_a_6626_);
                    v___x_6631_ = v_reuseFailAlloc_6632_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6631_;
            }
            15 => {
                if v_isShared_6637_ == 0 {
                    v___x_6639_ = v___x_6636_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6640_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6640_, 0, v_a_6634_);
                    v___x_6639_ = v_reuseFailAlloc_6640_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6639_;
            }
            17 => {
                if v_isShared_6645_ == 0 {
                    v___x_6647_ = v___x_6644_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6648_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6648_, 0, v_a_6642_);
                    v___x_6647_ = v_reuseFailAlloc_6648_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed(
    mut v_goal_6650_: *mut crate::leanh::LeanObject,
    mut v___y_6651_: *mut crate::leanh::LeanObject,
    mut v___y_6652_: *mut crate::leanh::LeanObject,
    mut v___y_6653_: *mut crate::leanh::LeanObject,
    mut v___y_6654_: *mut crate::leanh::LeanObject,
    mut v___y_6655_: *mut crate::leanh::LeanObject,
    mut v___y_6656_: *mut crate::leanh::LeanObject,
    mut v___y_6657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6658_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(
        v_goal_6650_,
        v___y_6651_,
        v___y_6652_,
        v___y_6653_,
        v___y_6654_,
        v___y_6655_,
        v___y_6656_,
    );
    crate::leanh::lean_dec(v___y_6656_);
    crate::leanh::lean_dec_ref(v___y_6655_);
    crate::leanh::lean_dec(v___y_6654_);
    crate::leanh::lean_dec_ref(v___y_6653_);
    crate::leanh::lean_dec(v___y_6652_);
    crate::leanh::lean_dec_ref(v___y_6651_);
    return v_res_6658_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
}
