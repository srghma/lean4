// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.IntToBitVec
// Imports: Lean.Meta.Tactic.BVDecide.Normalize.Basic
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef, l_Pi_instInhabited___redArg___lam__0,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mod, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_string_dec_eq,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Util::ReplaceExpr::lean_replace_expr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_6, lean_apply_7, lean_box, lean_box_usize, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_eqv___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 115, 116, 101, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 108, 97, 116, 102, 111, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 117, 109, 66, 105, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value) as *mut LeanObject,3794196532276496372 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value) as *mut LeanObject,3058792918547557504 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__5_value) as *mut LeanObject,9241886346910436803 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__7_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 121, 109, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__9_value) as *mut LeanObject,15643637366941324764 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__0_value) as *mut LeanObject,13655884332201764339 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__0_value) as *mut LeanObject,5394957827732845164 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__0_value) as *mut LeanObject,8738205681931236784 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [122, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__0_value) as *mut LeanObject,5764232124464284678 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__2_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 115, 101, 115, 79, 110, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__1_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__5_value) as *mut LeanObject,5881126286461038842 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13_value: LeanStringObject<76> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 76, m_capacity: 76, m_length: 75, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 114, 101, 97, 116, 101, 32, 98, 105, 110, 100, 101, 114, 32, 100, 117, 101, 32, 116, 111, 32, 102, 97, 105, 108, 117, 114, 101, 32, 119, 104, 101, 110, 32, 114, 101, 118, 101, 114, 116, 105, 110, 103, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 105, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0_value: LeanStringObject<110> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 110, m_capacity: 110, m_length: 109, m_data: [68, 101, 116, 101, 99, 116, 101, 100, 32, 85, 83, 105, 122, 101, 47, 73, 83, 105, 122, 101, 32, 105, 110, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 98, 117, 116, 32, 110, 111, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 97, 98, 111, 117, 116, 32, 83, 121, 115, 116, 101, 109, 46, 80, 108, 97, 116, 102, 111, 114, 109, 46, 110, 117, 109, 66, 105, 116, 115, 44, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 99, 97, 115, 101, 32, 115, 112, 108, 105, 116, 116, 105, 110, 103, 32, 111, 110, 32, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [110, 117, 109, 66, 105, 116, 115, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__3_value) as *mut LeanObject,3794196532276496372 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__4_value) as *mut LeanObject,3058792918547557504 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__2_value) as *mut LeanObject,11860477813648696129 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 83, 105, 122, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__0_value) as *mut LeanObject,17712594561405737325 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value) as *mut LeanObject,9255850586598716316 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [73, 83, 105, 122, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__3_value) as *mut LeanObject,16021149375362053230 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__1_value) as *mut LeanObject,12113648043307972955 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__4_value) as *mut LeanObject;
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0: usize = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__1_value)
            as *mut LeanObject,
        5625817593341794690 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__2_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___closed__3_value)
        as *mut LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(
    mut v_e_3336_: *mut LeanObject,
    mut v_a_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3339_ = lean_st_ref_take(v_a_3337_);
                v_relevantTerms_3340_ = lean_ctor_get(v___x_3339_, 0);
                v_relevantHyps_3341_ = lean_ctor_get(v___x_3339_, 1);
                v_isSharedCheck_3354_ = (!lean_is_exclusive(v___x_3339_)) as u8;
                if v_isSharedCheck_3354_ == 0 {
                    v___x_3343_ = v___x_3339_;
                    v_isShared_3344_ = v_isSharedCheck_3354_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_relevantHyps_3341_);
                    lean_inc(v_relevantTerms_3340_);
                    lean_dec(v___x_3339_);
                    v___x_3343_ = lean_box(0);
                    v_isShared_3344_ = v_isSharedCheck_3354_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3345_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0;
                v___x_3346_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1;
                v___x_3347_ = lean_box(0);
                v___x_3348_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_3345_,
                    v___x_3346_,
                    v_relevantTerms_3340_,
                    v_e_3336_,
                    v___x_3347_,
                );
                if v_isShared_3344_ == 0 {
                    lean_ctor_set(v___x_3343_, 0, v___x_3348_);
                    v___x_3350_ = v___x_3343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3348_);
                    lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_relevantHyps_3341_);
                    v___x_3350_ = v_reuseFailAlloc_3353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3351_ = lean_st_ref_set(v_a_3337_, v___x_3350_);
                v___x_3352_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3352_, 0, v___x_3347_);
                return v___x_3352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___boxed(
    mut v_e_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
    mut v_a_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3358_: *mut LeanObject = core::ptr::null_mut();
    v_res_3358_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg(v_e_3355_, v_a_3356_);
    lean_dec(v_a_3356_);
    return v_res_3358_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(
    mut v_e_3359_: *mut LeanObject,
    mut v_a_3360_: *mut LeanObject,
    mut v_a_3361_: *mut LeanObject,
    mut v_a_3362_: *mut LeanObject,
    mut v_a_3363_: *mut LeanObject,
    mut v_a_3364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3371_: u8 = 0;
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3366_ = lean_st_ref_take(v_a_3360_);
                v_relevantTerms_3367_ = lean_ctor_get(v___x_3366_, 0);
                v_relevantHyps_3368_ = lean_ctor_get(v___x_3366_, 1);
                v_isSharedCheck_3381_ = (!lean_is_exclusive(v___x_3366_)) as u8;
                if v_isSharedCheck_3381_ == 0 {
                    v___x_3370_ = v___x_3366_;
                    v_isShared_3371_ = v_isSharedCheck_3381_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_relevantHyps_3368_);
                    lean_inc(v_relevantTerms_3367_);
                    lean_dec(v___x_3366_);
                    v___x_3370_ = lean_box(0);
                    v_isShared_3371_ = v_isSharedCheck_3381_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3372_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__0;
                v___x_3373_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___redArg___closed__1;
                v___x_3374_ = lean_box(0);
                v___x_3375_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_3372_,
                    v___x_3373_,
                    v_relevantTerms_3367_,
                    v_e_3359_,
                    v___x_3374_,
                );
                if v_isShared_3371_ == 0 {
                    lean_ctor_set(v___x_3370_, 0, v___x_3375_);
                    v___x_3377_ = v___x_3370_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3375_);
                    lean_ctor_set(v_reuseFailAlloc_3380_, 1, v_relevantHyps_3368_);
                    v___x_3377_ = v_reuseFailAlloc_3380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3378_ = lean_st_ref_set(v_a_3360_, v___x_3377_);
                v___x_3379_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3379_, 0, v___x_3374_);
                return v___x_3379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm___boxed(
    mut v_e_3382_: *mut LeanObject,
    mut v_a_3383_: *mut LeanObject,
    mut v_a_3384_: *mut LeanObject,
    mut v_a_3385_: *mut LeanObject,
    mut v_a_3386_: *mut LeanObject,
    mut v_a_3387_: *mut LeanObject,
    mut v_a_3388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3389_: *mut LeanObject = core::ptr::null_mut();
    v_res_3389_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeTerm(v_e_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_);
    lean_dec(v_a_3387_);
    lean_dec_ref(v_a_3386_);
    lean_dec(v_a_3385_);
    lean_dec_ref(v_a_3384_);
    lean_dec(v_a_3383_);
    return v_res_3389_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(
    mut v_f_3392_: *mut LeanObject,
    mut v_a_3393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3400_: u8 = 0;
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3395_ = lean_st_ref_take(v_a_3393_);
                v_relevantTerms_3396_ = lean_ctor_get(v___x_3395_, 0);
                v_relevantHyps_3397_ = lean_ctor_get(v___x_3395_, 1);
                v_isSharedCheck_3410_ = (!lean_is_exclusive(v___x_3395_)) as u8;
                if v_isSharedCheck_3410_ == 0 {
                    v___x_3399_ = v___x_3395_;
                    v_isShared_3400_ = v_isSharedCheck_3410_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_relevantHyps_3397_);
                    lean_inc(v_relevantTerms_3396_);
                    lean_dec(v___x_3395_);
                    v___x_3399_ = lean_box(0);
                    v_isShared_3400_ = v_isSharedCheck_3410_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3401_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0;
                v___x_3402_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1;
                v___x_3403_ = lean_box(0);
                v___x_3404_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_3401_,
                    v___x_3402_,
                    v_relevantHyps_3397_,
                    v_f_3392_,
                    v___x_3403_,
                );
                if v_isShared_3400_ == 0 {
                    lean_ctor_set(v___x_3399_, 1, v___x_3404_);
                    v___x_3406_ = v___x_3399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_relevantTerms_3396_);
                    lean_ctor_set(v_reuseFailAlloc_3409_, 1, v___x_3404_);
                    v___x_3406_ = v_reuseFailAlloc_3409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3407_ = lean_st_ref_set(v_a_3393_, v___x_3406_);
                v___x_3408_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3408_, 0, v___x_3403_);
                return v___x_3408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___boxed(
    mut v_f_3411_: *mut LeanObject,
    mut v_a_3412_: *mut LeanObject,
    mut v_a_3413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3414_: *mut LeanObject = core::ptr::null_mut();
    v_res_3414_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg(v_f_3411_, v_a_3412_);
    lean_dec(v_a_3412_);
    return v_res_3414_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(
    mut v_f_3415_: *mut LeanObject,
    mut v_a_3416_: *mut LeanObject,
    mut v_a_3417_: *mut LeanObject,
    mut v_a_3418_: *mut LeanObject,
    mut v_a_3419_: *mut LeanObject,
    mut v_a_3420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3427_: u8 = 0;
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3422_ = lean_st_ref_take(v_a_3416_);
                v_relevantTerms_3423_ = lean_ctor_get(v___x_3422_, 0);
                v_relevantHyps_3424_ = lean_ctor_get(v___x_3422_, 1);
                v_isSharedCheck_3437_ = (!lean_is_exclusive(v___x_3422_)) as u8;
                if v_isSharedCheck_3437_ == 0 {
                    v___x_3426_ = v___x_3422_;
                    v_isShared_3427_ = v_isSharedCheck_3437_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_relevantHyps_3424_);
                    lean_inc(v_relevantTerms_3423_);
                    lean_dec(v___x_3422_);
                    v___x_3426_ = lean_box(0);
                    v_isShared_3427_ = v_isSharedCheck_3437_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3428_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__0;
                v___x_3429_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___redArg___closed__1;
                v___x_3430_ = lean_box(0);
                v___x_3431_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v___x_3428_,
                    v___x_3429_,
                    v_relevantHyps_3424_,
                    v_f_3415_,
                    v___x_3430_,
                );
                if v_isShared_3427_ == 0 {
                    lean_ctor_set(v___x_3426_, 1, v___x_3431_);
                    v___x_3433_ = v___x_3426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_relevantTerms_3423_);
                    lean_ctor_set(v_reuseFailAlloc_3436_, 1, v___x_3431_);
                    v___x_3433_ = v_reuseFailAlloc_3436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3434_ = lean_st_ref_set(v_a_3416_, v___x_3433_);
                v___x_3435_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3435_, 0, v___x_3430_);
                return v___x_3435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp___boxed(
    mut v_f_3438_: *mut LeanObject,
    mut v_a_3439_: *mut LeanObject,
    mut v_a_3440_: *mut LeanObject,
    mut v_a_3441_: *mut LeanObject,
    mut v_a_3442_: *mut LeanObject,
    mut v_a_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3445_: *mut LeanObject = core::ptr::null_mut();
    v_res_3445_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_M_addSizeHyp(v_f_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_);
    lean_dec(v_a_3443_);
    lean_dec_ref(v_a_3442_);
    lean_dec(v_a_3441_);
    lean_dec_ref(v_a_3440_);
    lean_dec(v_a_3439_);
    return v_res_3445_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(
    mut v_e_3446_: *mut LeanObject,
    mut v___y_3447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3449_: u8 = 0;
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3463_: u8 = 0;
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_unused_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3449_ = l_Lean_Expr_hasMVar(v_e_3446_);
                if v___x_3449_ == 0 {
                    v___x_3450_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3450_, 0, v_e_3446_);
                    return v___x_3450_;
                } else {
                    v___x_3451_ = lean_st_ref_get(v___y_3447_);
                    v_mctx_3452_ = lean_ctor_get(v___x_3451_, 0);
                    lean_inc_ref(v_mctx_3452_);
                    lean_dec(v___x_3451_);
                    v___x_3453_ = l_Lean_instantiateMVarsCore(v_mctx_3452_, v_e_3446_);
                    v_fst_3454_ = lean_ctor_get(v___x_3453_, 0);
                    lean_inc(v_fst_3454_);
                    v_snd_3455_ = lean_ctor_get(v___x_3453_, 1);
                    lean_inc(v_snd_3455_);
                    lean_dec_ref(v___x_3453_);
                    v___x_3456_ = lean_st_ref_take(v___y_3447_);
                    v_cache_3457_ = lean_ctor_get(v___x_3456_, 1);
                    v_zetaDeltaFVarIds_3458_ = lean_ctor_get(v___x_3456_, 2);
                    v_postponed_3459_ = lean_ctor_get(v___x_3456_, 3);
                    v_diag_3460_ = lean_ctor_get(v___x_3456_, 4);
                    v_isSharedCheck_3469_ = (!lean_is_exclusive(v___x_3456_)) as u8;
                    if v_isSharedCheck_3469_ == 0 {
                        v_unused_3470_ = lean_ctor_get(v___x_3456_, 0);
                        lean_dec(v_unused_3470_);
                        v___x_3462_ = v___x_3456_;
                        v_isShared_3463_ = v_isSharedCheck_3469_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_3460_);
                        lean_inc(v_postponed_3459_);
                        lean_inc(v_zetaDeltaFVarIds_3458_);
                        lean_inc(v_cache_3457_);
                        lean_dec(v___x_3456_);
                        v___x_3462_ = lean_box(0);
                        v_isShared_3463_ = v_isSharedCheck_3469_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3463_ == 0 {
                    lean_ctor_set(v___x_3462_, 0, v_snd_3455_);
                    v___x_3465_ = v___x_3462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_snd_3455_);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 1, v_cache_3457_);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 2, v_zetaDeltaFVarIds_3458_);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 3, v_postponed_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 4, v_diag_3460_);
                    v___x_3465_ = v_reuseFailAlloc_3468_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3466_ = lean_st_ref_set(v___y_3447_, v___x_3465_);
                v___x_3467_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3467_, 0, v_fst_3454_);
                return v___x_3467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg___boxed(
    mut v_e_3471_: *mut LeanObject,
    mut v___y_3472_: *mut LeanObject,
    mut v___y_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3474_: *mut LeanObject = core::ptr::null_mut();
    v_res_3474_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_3471_, v___y_3472_);
    lean_dec(v___y_3472_);
    return v_res_3474_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(
    mut v_e_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    v___x_3481_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_e_3475_, v___y_3477_);
    return v___x_3481_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___boxed(
    mut v_e_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
    mut v___y_3485_: *mut LeanObject,
    mut v___y_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3488_: *mut LeanObject = core::ptr::null_mut();
    v_res_3488_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0(v_e_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
    lean_dec(v___y_3486_);
    lean_dec_ref(v___y_3485_);
    lean_dec(v___y_3484_);
    lean_dec_ref(v___y_3483_);
    return v_res_3488_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(
    mut v_mvarId_3489_: *mut LeanObject,
    mut v_x_3490_: *mut LeanObject,
    mut v___y_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3500_: u8 = 0;
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut v_a_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3508_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3496_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_3489_,
                    v_x_3490_,
                    v___y_3491_,
                    v___y_3492_,
                    v___y_3493_,
                    v___y_3494_,
                );
                if lean_obj_tag(v___x_3496_) == 0 {
                    v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
                    v_isSharedCheck_3504_ = (!lean_is_exclusive(v___x_3496_)) as u8;
                    if v_isSharedCheck_3504_ == 0 {
                        v___x_3499_ = v___x_3496_;
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3497_);
                        lean_dec(v___x_3496_);
                        v___x_3499_ = lean_box(0);
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3505_ = lean_ctor_get(v___x_3496_, 0);
                    v_isSharedCheck_3512_ = (!lean_is_exclusive(v___x_3496_)) as u8;
                    if v_isSharedCheck_3512_ == 0 {
                        v___x_3507_ = v___x_3496_;
                        v_isShared_3508_ = v_isSharedCheck_3512_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3505_);
                        lean_dec(v___x_3496_);
                        v___x_3507_ = lean_box(0);
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
                    v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
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
                    v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
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
    mut v_mvarId_3513_: *mut LeanObject,
    mut v_x_3514_: *mut LeanObject,
    mut v___y_3515_: *mut LeanObject,
    mut v___y_3516_: *mut LeanObject,
    mut v___y_3517_: *mut LeanObject,
    mut v___y_3518_: *mut LeanObject,
    mut v___y_3519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3520_: *mut LeanObject = core::ptr::null_mut();
    v_res_3520_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_3513_, v_x_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
    lean_dec(v___y_3518_);
    lean_dec_ref(v___y_3517_);
    lean_dec(v___y_3516_);
    lean_dec_ref(v___y_3515_);
    return v_res_3520_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(
    mut v_00_u03b1_3521_: *mut LeanObject,
    mut v_mvarId_3522_: *mut LeanObject,
    mut v_x_3523_: *mut LeanObject,
    mut v___y_3524_: *mut LeanObject,
    mut v___y_3525_: *mut LeanObject,
    mut v___y_3526_: *mut LeanObject,
    mut v___y_3527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    v___x_3529_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_mvarId_3522_, v_x_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
    return v___x_3529_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___boxed(
    mut v_00_u03b1_3530_: *mut LeanObject,
    mut v_mvarId_3531_: *mut LeanObject,
    mut v_x_3532_: *mut LeanObject,
    mut v___y_3533_: *mut LeanObject,
    mut v___y_3534_: *mut LeanObject,
    mut v___y_3535_: *mut LeanObject,
    mut v___y_3536_: *mut LeanObject,
    mut v___y_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3538_: *mut LeanObject = core::ptr::null_mut();
    v_res_3538_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2(v_00_u03b1_3530_, v_mvarId_3531_, v_x_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
    lean_dec(v___y_3536_);
    lean_dec_ref(v___y_3535_);
    lean_dec(v___y_3534_);
    lean_dec_ref(v___y_3533_);
    return v_res_3538_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11()
-> *mut LeanObject {
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    v___x_3561_ = lean_unsigned_to_nat(1);
    v___x_3562_ = l_Lean_Level_ofNat(v___x_3561_);
    return v___x_3562_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12()
-> *mut LeanObject {
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    v___x_3563_ = lean_box(0);
    v___x_3564_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
    v___x_3565_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3565_, 0, v___x_3564_);
    lean_ctor_set(v___x_3565_, 1, v___x_3563_);
    return v___x_3565_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13()
-> *mut LeanObject {
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    v___x_3566_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
    v___x_3567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__10;
    v___x_3568_ = l_Lean_mkConst(v___x_3567_, v___x_3566_);
    return v___x_3568_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(
    mut v_as_3569_: *mut LeanObject,
    mut v_sz_3570_: usize,
    mut v_i_3571_: usize,
    mut v_b_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
    mut v___y_3574_: *mut LeanObject,
    mut v___y_3575_: *mut LeanObject,
    mut v___y_3576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3578_: u8 = 0;
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: usize = 0;
    let mut v___x_3590_: usize = 0;
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: u8 = 0;
    let mut v_arg_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: u8 = 0;
    let mut v_arg_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: u8 = 0;
    let mut v_arg_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: u8 = 0;
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: u8 = 0;
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3613_: u8 = 0;
    let mut v_val_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3617_: u8 = 0;
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3633_: u8 = 0;
    let mut v_a_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3646_: u8 = 0;
    let mut v_val_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3650_: u8 = 0;
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3668_: u8 = 0;
    let mut v_a_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3676_: u8 = 0;
    let mut v_a_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3680_: u8 = 0;
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3684_: u8 = 0;
    let mut v_a_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3688_: u8 = 0;
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut v_a_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3578_ = lean_usize_dec_lt(v_i_3571_, v_sz_3570_);
                if v___x_3578_ == 0 {
                    v___x_3579_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3579_, 0, v_b_3572_);
                    return v___x_3579_;
                } else {
                    lean_dec_ref(v_b_3572_);
                    v_a_3580_ = lean_array_uget_borrowed(v_as_3569_, v_i_3571_);
                    lean_inc(v_a_3580_);
                    v___x_3581_ = l_Lean_FVarId_getType___redArg(
                        v_a_3580_,
                        v___y_3573_,
                        v___y_3575_,
                        v___y_3576_,
                    );
                    if lean_obj_tag(v___x_3581_) == 0 {
                        v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
                        lean_inc(v_a_3582_);
                        lean_dec_ref_known(v___x_3581_, 1);
                        v___x_3583_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__0___redArg(v_a_3582_, v___y_3574_);
                        if lean_obj_tag(v___x_3583_) == 0 {
                            v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
                            lean_inc(v_a_3584_);
                            lean_dec_ref_known(v___x_3583_, 1);
                            v___x_3585_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                v_a_3584_,
                                v___y_3574_,
                            );
                            if lean_obj_tag(v___x_3585_) == 0 {
                                v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
                                lean_inc(v_a_3586_);
                                lean_dec_ref_known(v___x_3585_, 1);
                                v___x_3592_ = lean_box(0);
                                v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0;
                                v___x_3594_ = l_Lean_Expr_cleanupAnnotations(v_a_3586_);
                                v___x_3595_ = l_Lean_Expr_isApp(v___x_3594_);
                                if v___x_3595_ == 0 {
                                    lean_dec_ref(v___x_3594_);
                                    v_a_3588_ = v___x_3593_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_3596_ = lean_ctor_get(v___x_3594_, 1);
                                    lean_inc_ref(v_arg_3596_);
                                    v___x_3597_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3594_);
                                    v___x_3598_ = l_Lean_Expr_isApp(v___x_3597_);
                                    if v___x_3598_ == 0 {
                                        lean_dec_ref(v___x_3597_);
                                        lean_dec_ref(v_arg_3596_);
                                        v_a_3588_ = v___x_3593_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_3599_ = lean_ctor_get(v___x_3597_, 1);
                                        lean_inc_ref(v_arg_3599_);
                                        v___x_3600_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3597_);
                                        v___x_3601_ = l_Lean_Expr_isApp(v___x_3600_);
                                        if v___x_3601_ == 0 {
                                            lean_dec_ref(v___x_3600_);
                                            lean_dec_ref(v_arg_3599_);
                                            lean_dec_ref(v_arg_3596_);
                                            v_a_3588_ = v___x_3593_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_arg_3602_ = lean_ctor_get(v___x_3600_, 1);
                                            lean_inc_ref(v_arg_3602_);
                                            v___x_3603_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3600_);
                                            v___x_3604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2;
                                            v___x_3605_ =
                                                l_Lean_Expr_isConstOf(v___x_3603_, v___x_3604_);
                                            lean_dec_ref(v___x_3603_);
                                            if v___x_3605_ == 0 {
                                                lean_dec_ref(v_arg_3602_);
                                                lean_dec_ref(v_arg_3599_);
                                                lean_dec_ref(v_arg_3596_);
                                                v_a_3588_ = v___x_3593_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6;
                                                v___x_3607_ =
                                                    l_Lean_Expr_isConstOf(v_arg_3599_, v___x_3606_);
                                                if v___x_3607_ == 0 {
                                                    lean_dec_ref(v_arg_3602_);
                                                    v___x_3608_ = l_Lean_Expr_isConstOf(
                                                        v_arg_3596_,
                                                        v___x_3606_,
                                                    );
                                                    lean_dec_ref(v_arg_3596_);
                                                    if v___x_3608_ == 0 {
                                                        lean_dec_ref(v_arg_3599_);
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
                                                        lean_dec_ref(v_arg_3599_);
                                                        if lean_obj_tag(v___x_3609_) == 0 {
                                                            v_a_3610_ =
                                                                lean_ctor_get(v___x_3609_, 0);
                                                            v_isSharedCheck_3633_ =
                                                                (!lean_is_exclusive(v___x_3609_))
                                                                    as u8;
                                                            if v_isSharedCheck_3633_ == 0 {
                                                                v___x_3612_ = v___x_3609_;
                                                                v_isShared_3613_ =
                                                                    v_isSharedCheck_3633_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_3610_);
                                                                lean_dec(v___x_3609_);
                                                                v___x_3612_ = lean_box(0);
                                                                v_isShared_3613_ =
                                                                    v_isSharedCheck_3633_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_3634_ =
                                                                lean_ctor_get(v___x_3609_, 0);
                                                            v_isSharedCheck_3641_ =
                                                                (!lean_is_exclusive(v___x_3609_))
                                                                    as u8;
                                                            if v_isSharedCheck_3641_ == 0 {
                                                                v___x_3636_ = v___x_3609_;
                                                                v_isShared_3637_ =
                                                                    v_isSharedCheck_3641_;
                                                                state = 7;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_3634_);
                                                                lean_dec(v___x_3609_);
                                                                v___x_3636_ = lean_box(0);
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
                                                    if lean_obj_tag(v___x_3642_) == 0 {
                                                        v_a_3643_ = lean_ctor_get(v___x_3642_, 0);
                                                        v_isSharedCheck_3668_ =
                                                            (!lean_is_exclusive(v___x_3642_)) as u8;
                                                        if v_isSharedCheck_3668_ == 0 {
                                                            v___x_3645_ = v___x_3642_;
                                                            v_isShared_3646_ =
                                                                v_isSharedCheck_3668_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_3643_);
                                                            lean_dec(v___x_3642_);
                                                            v___x_3645_ = lean_box(0);
                                                            v_isShared_3646_ =
                                                                v_isSharedCheck_3668_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_3602_);
                                                        lean_dec_ref(v_arg_3599_);
                                                        lean_dec_ref(v_arg_3596_);
                                                        v_a_3669_ = lean_ctor_get(v___x_3642_, 0);
                                                        v_isSharedCheck_3676_ =
                                                            (!lean_is_exclusive(v___x_3642_)) as u8;
                                                        if v_isSharedCheck_3676_ == 0 {
                                                            v___x_3671_ = v___x_3642_;
                                                            v_isShared_3672_ =
                                                                v_isSharedCheck_3676_;
                                                            state = 14;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_3669_);
                                                            lean_dec(v___x_3642_);
                                                            v___x_3671_ = lean_box(0);
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
                                v_a_3677_ = lean_ctor_get(v___x_3585_, 0);
                                v_isSharedCheck_3684_ = (!lean_is_exclusive(v___x_3585_)) as u8;
                                if v_isSharedCheck_3684_ == 0 {
                                    v___x_3679_ = v___x_3585_;
                                    v_isShared_3680_ = v_isSharedCheck_3684_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_3677_);
                                    lean_dec(v___x_3585_);
                                    v___x_3679_ = lean_box(0);
                                    v_isShared_3680_ = v_isSharedCheck_3684_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            v_a_3685_ = lean_ctor_get(v___x_3583_, 0);
                            v_isSharedCheck_3692_ = (!lean_is_exclusive(v___x_3583_)) as u8;
                            if v_isSharedCheck_3692_ == 0 {
                                v___x_3687_ = v___x_3583_;
                                v_isShared_3688_ = v_isSharedCheck_3692_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_3685_);
                                lean_dec(v___x_3583_);
                                v___x_3687_ = lean_box(0);
                                v_isShared_3688_ = v_isSharedCheck_3692_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        v_a_3693_ = lean_ctor_get(v___x_3581_, 0);
                        v_isSharedCheck_3700_ = (!lean_is_exclusive(v___x_3581_)) as u8;
                        if v_isSharedCheck_3700_ == 0 {
                            v___x_3695_ = v___x_3581_;
                            v_isShared_3696_ = v_isSharedCheck_3700_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_3693_);
                            lean_dec(v___x_3581_);
                            v___x_3695_ = lean_box(0);
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
                lean_inc_ref(v_a_3588_);
                v_i_3571_ = v___x_3590_;
                v_b_3572_ = v_a_3588_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v_a_3610_) == 1 {
                    v_val_3614_ = lean_ctor_get(v_a_3610_, 0);
                    v_isSharedCheck_3628_ = (!lean_is_exclusive(v_a_3610_)) as u8;
                    if v_isSharedCheck_3628_ == 0 {
                        v___x_3616_ = v_a_3610_;
                        v_isShared_3617_ = v_isSharedCheck_3628_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_3614_);
                        lean_dec(v_a_3610_);
                        v___x_3616_ = lean_box(0);
                        v_isShared_3617_ = v_isSharedCheck_3628_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3610_);
                    v___x_3629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8;
                    if v_isShared_3613_ == 0 {
                        lean_ctor_set(v___x_3612_, 0, v___x_3629_);
                        v___x_3631_ = v___x_3612_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
                        v___x_3631_ = v_reuseFailAlloc_3632_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_3580_);
                v___x_3618_ = l_Lean_mkFVar(v_a_3580_);
                v___x_3619_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3619_, 0, v_val_3614_);
                lean_ctor_set(v___x_3619_, 1, v___x_3618_);
                if v_isShared_3617_ == 0 {
                    lean_ctor_set(v___x_3616_, 0, v___x_3619_);
                    v___x_3621_ = v___x_3616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3619_);
                    v___x_3621_ = v_reuseFailAlloc_3627_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3622_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3622_, 0, v___x_3621_);
                v___x_3623_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3623_, 0, v___x_3622_);
                lean_ctor_set(v___x_3623_, 1, v___x_3592_);
                if v_isShared_3613_ == 0 {
                    lean_ctor_set(v___x_3612_, 0, v___x_3623_);
                    v___x_3625_ = v___x_3612_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
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
                    v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
                    v___x_3639_ = v_reuseFailAlloc_3640_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3639_;
            }
            9 => {
                if lean_obj_tag(v_a_3643_) == 1 {
                    v_val_3647_ = lean_ctor_get(v_a_3643_, 0);
                    v_isSharedCheck_3663_ = (!lean_is_exclusive(v_a_3643_)) as u8;
                    if v_isSharedCheck_3663_ == 0 {
                        v___x_3649_ = v_a_3643_;
                        v_isShared_3650_ = v_isSharedCheck_3663_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_val_3647_);
                        lean_dec(v_a_3643_);
                        v___x_3649_ = lean_box(0);
                        v_isShared_3650_ = v_isSharedCheck_3663_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3643_);
                    lean_dec_ref(v_arg_3602_);
                    lean_dec_ref(v_arg_3599_);
                    lean_dec_ref(v_arg_3596_);
                    v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__8;
                    if v_isShared_3646_ == 0 {
                        lean_ctor_set(v___x_3645_, 0, v___x_3664_);
                        v___x_3666_ = v___x_3645_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
                        v___x_3666_ = v_reuseFailAlloc_3667_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                v___x_3651_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__13);
                lean_inc(v_a_3580_);
                v___x_3652_ = l_Lean_mkFVar(v_a_3580_);
                v___x_3653_ = l_Lean_mkApp4(
                    v___x_3651_,
                    v_arg_3602_,
                    v_arg_3599_,
                    v_arg_3596_,
                    v___x_3652_,
                );
                v___x_3654_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3654_, 0, v_val_3647_);
                lean_ctor_set(v___x_3654_, 1, v___x_3653_);
                if v_isShared_3650_ == 0 {
                    lean_ctor_set(v___x_3649_, 0, v___x_3654_);
                    v___x_3656_ = v___x_3649_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3654_);
                    v___x_3656_ = v_reuseFailAlloc_3662_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3657_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3657_, 0, v___x_3656_);
                v___x_3658_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3658_, 0, v___x_3657_);
                lean_ctor_set(v___x_3658_, 1, v___x_3592_);
                if v_isShared_3646_ == 0 {
                    lean_ctor_set(v___x_3645_, 0, v___x_3658_);
                    v___x_3660_ = v___x_3645_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
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
                    v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
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
                    v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
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
                    v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
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
                    v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
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
    mut v_as_3701_: *mut LeanObject,
    mut v_sz_3702_: *mut LeanObject,
    mut v_i_3703_: *mut LeanObject,
    mut v_b_3704_: *mut LeanObject,
    mut v___y_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
    mut v___y_3707_: *mut LeanObject,
    mut v___y_3708_: *mut LeanObject,
    mut v___y_3709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3710_: usize = 0;
    let mut v_i_boxed_3711_: usize = 0;
    let mut v_res_3712_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3710_ = lean_unbox_usize(v_sz_3702_);
    lean_dec(v_sz_3702_);
    v_i_boxed_3711_ = lean_unbox_usize(v_i_3703_);
    lean_dec(v_i_3703_);
    v_res_3712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_as_3701_, v_sz_boxed_3710_, v_i_boxed_3711_, v_b_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
    lean_dec(v___y_3708_);
    lean_dec_ref(v___y_3707_);
    lean_dec(v___y_3706_);
    lean_dec_ref(v___y_3705_);
    lean_dec_ref(v_as_3701_);
    return v_res_3712_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(
    mut v___y_3713_: *mut LeanObject,
    mut v___y_3714_: *mut LeanObject,
    mut v___y_3715_: *mut LeanObject,
    mut v___y_3716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3722_: usize = 0;
    let mut v___x_3723_: usize = 0;
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3728_: u8 = 0;
    let mut v_fst_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut v_a_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut v_a_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3749_: u8 = 0;
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3718_ =
                    l_Lean_Meta_getPropHyps(v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
                if lean_obj_tag(v___x_3718_) == 0 {
                    v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
                    lean_inc(v_a_3719_);
                    lean_dec_ref_known(v___x_3718_, 1);
                    v___x_3720_ = lean_box(0);
                    v___x_3721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__0;
                    v_sz_3722_ = lean_array_size(v_a_3719_);
                    v___x_3723_ = 0usize;
                    v___x_3724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1(v_a_3719_, v_sz_3722_, v___x_3723_, v___x_3721_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
                    lean_dec(v_a_3719_);
                    if lean_obj_tag(v___x_3724_) == 0 {
                        v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
                        v_isSharedCheck_3737_ = (!lean_is_exclusive(v___x_3724_)) as u8;
                        if v_isSharedCheck_3737_ == 0 {
                            v___x_3727_ = v___x_3724_;
                            v_isShared_3728_ = v_isSharedCheck_3737_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3725_);
                            lean_dec(v___x_3724_);
                            v___x_3727_ = lean_box(0);
                            v_isShared_3728_ = v_isSharedCheck_3737_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3738_ = lean_ctor_get(v___x_3724_, 0);
                        v_isSharedCheck_3745_ = (!lean_is_exclusive(v___x_3724_)) as u8;
                        if v_isSharedCheck_3745_ == 0 {
                            v___x_3740_ = v___x_3724_;
                            v_isShared_3741_ = v_isSharedCheck_3745_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3738_);
                            lean_dec(v___x_3724_);
                            v___x_3740_ = lean_box(0);
                            v_isShared_3741_ = v_isSharedCheck_3745_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_3746_ = lean_ctor_get(v___x_3718_, 0);
                    v_isSharedCheck_3753_ = (!lean_is_exclusive(v___x_3718_)) as u8;
                    if v_isSharedCheck_3753_ == 0 {
                        v___x_3748_ = v___x_3718_;
                        v_isShared_3749_ = v_isSharedCheck_3753_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3746_);
                        lean_dec(v___x_3718_);
                        v___x_3748_ = lean_box(0);
                        v_isShared_3749_ = v_isSharedCheck_3753_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3729_ = lean_ctor_get(v_a_3725_, 0);
                lean_inc(v_fst_3729_);
                lean_dec(v_a_3725_);
                if lean_obj_tag(v_fst_3729_) == 0 {
                    if v_isShared_3728_ == 0 {
                        lean_ctor_set(v___x_3727_, 0, v___x_3720_);
                        v___x_3731_ = v___x_3727_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3720_);
                        v___x_3731_ = v_reuseFailAlloc_3732_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3733_ = lean_ctor_get(v_fst_3729_, 0);
                    lean_inc(v_val_3733_);
                    lean_dec_ref_known(v_fst_3729_, 1);
                    if v_isShared_3728_ == 0 {
                        lean_ctor_set(v___x_3727_, 0, v_val_3733_);
                        v___x_3735_ = v___x_3727_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_val_3733_);
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
                    v_reuseFailAlloc_3744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_a_3738_);
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
                    v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
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
    mut v___y_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
    mut v___y_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3759_: *mut LeanObject = core::ptr::null_mut();
    v_res_3759_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___lam__0(v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
    lean_dec(v___y_3757_);
    lean_dec_ref(v___y_3756_);
    lean_dec(v___y_3755_);
    lean_dec_ref(v___y_3754_);
    return v_res_3759_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(
    mut v_goal_3761_: *mut LeanObject,
    mut v_a_3762_: *mut LeanObject,
    mut v_a_3763_: *mut LeanObject,
    mut v_a_3764_: *mut LeanObject,
    mut v_a_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    v___f_3767_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___closed__0;
    v___x_3768_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__2___redArg(v_goal_3761_, v___f_3767_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_);
    return v___x_3768_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq___boxed(
    mut v_goal_3769_: *mut LeanObject,
    mut v_a_3770_: *mut LeanObject,
    mut v_a_3771_: *mut LeanObject,
    mut v_a_3772_: *mut LeanObject,
    mut v_a_3773_: *mut LeanObject,
    mut v_a_3774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3775_: *mut LeanObject = core::ptr::null_mut();
    v_res_3775_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(v_goal_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
    lean_dec(v_a_3773_);
    lean_dec_ref(v_a_3772_);
    lean_dec(v_a_3771_);
    lean_dec_ref(v_a_3770_);
    return v_res_3775_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(
    mut v_x_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
    mut v___y_3780_: *mut LeanObject,
    mut v___y_3781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3777_);
    v___x_3783_ = lean_apply_6(
        v_x_3776_,
        v___y_3777_,
        v___y_3778_,
        v___y_3779_,
        v___y_3780_,
        v___y_3781_,
        lean_box(0),
    );
    return v___x_3783_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed(
    mut v_x_3784_: *mut LeanObject,
    mut v___y_3785_: *mut LeanObject,
    mut v___y_3786_: *mut LeanObject,
    mut v___y_3787_: *mut LeanObject,
    mut v___y_3788_: *mut LeanObject,
    mut v___y_3789_: *mut LeanObject,
    mut v___y_3790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3791_: *mut LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0(v_x_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
    lean_dec(v___y_3785_);
    return v_res_3791_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(
    mut v_mvarId_3792_: *mut LeanObject,
    mut v_x_3793_: *mut LeanObject,
    mut v___y_3794_: *mut LeanObject,
    mut v___y_3795_: *mut LeanObject,
    mut v___y_3796_: *mut LeanObject,
    mut v___y_3797_: *mut LeanObject,
    mut v___y_3798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3805_: u8 = 0;
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3794_);
                v___f_3800_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
                lean_closure_set(v___f_3800_, 0, v_x_3793_);
                lean_closure_set(v___f_3800_, 1, v___y_3794_);
                v___x_3801_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_3792_,
                    v___f_3800_,
                    v___y_3795_,
                    v___y_3796_,
                    v___y_3797_,
                    v___y_3798_,
                );
                if lean_obj_tag(v___x_3801_) == 0 {
                    return v___x_3801_;
                } else {
                    v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
                    v_isSharedCheck_3809_ = (!lean_is_exclusive(v___x_3801_)) as u8;
                    if v_isSharedCheck_3809_ == 0 {
                        v___x_3804_ = v___x_3801_;
                        v_isShared_3805_ = v_isSharedCheck_3809_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3802_);
                        lean_dec(v___x_3801_);
                        v___x_3804_ = lean_box(0);
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
                    v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
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
    mut v_mvarId_3810_: *mut LeanObject,
    mut v_x_3811_: *mut LeanObject,
    mut v___y_3812_: *mut LeanObject,
    mut v___y_3813_: *mut LeanObject,
    mut v___y_3814_: *mut LeanObject,
    mut v___y_3815_: *mut LeanObject,
    mut v___y_3816_: *mut LeanObject,
    mut v___y_3817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3818_: *mut LeanObject = core::ptr::null_mut();
    v_res_3818_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_mvarId_3810_, v_x_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
    lean_dec(v___y_3816_);
    lean_dec_ref(v___y_3815_);
    lean_dec(v___y_3814_);
    lean_dec_ref(v___y_3813_);
    lean_dec(v___y_3812_);
    return v_res_3818_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14(
    mut v_00_u03b1_3819_: *mut LeanObject,
    mut v_mvarId_3820_: *mut LeanObject,
    mut v_x_3821_: *mut LeanObject,
    mut v___y_3822_: *mut LeanObject,
    mut v___y_3823_: *mut LeanObject,
    mut v___y_3824_: *mut LeanObject,
    mut v___y_3825_: *mut LeanObject,
    mut v___y_3826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    v___x_3828_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_mvarId_3820_, v_x_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
    return v___x_3828_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___boxed(
    mut v_00_u03b1_3829_: *mut LeanObject,
    mut v_mvarId_3830_: *mut LeanObject,
    mut v_x_3831_: *mut LeanObject,
    mut v___y_3832_: *mut LeanObject,
    mut v___y_3833_: *mut LeanObject,
    mut v___y_3834_: *mut LeanObject,
    mut v___y_3835_: *mut LeanObject,
    mut v___y_3836_: *mut LeanObject,
    mut v___y_3837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3838_: *mut LeanObject = core::ptr::null_mut();
    v_res_3838_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14(v_00_u03b1_3829_, v_mvarId_3830_, v_x_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
    lean_dec(v___y_3836_);
    lean_dec_ref(v___y_3835_);
    lean_dec(v___y_3834_);
    lean_dec_ref(v___y_3833_);
    lean_dec(v___y_3832_);
    return v_res_3838_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(
    mut v_a_3839_: *mut LeanObject,
    mut v_x_3840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: u8 = 0;
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3840_) == 0 {
                    v___x_3841_ = lean_box(0);
                    return v___x_3841_;
                } else {
                    v_key_3842_ = lean_ctor_get(v_x_3840_, 0);
                    v_value_3843_ = lean_ctor_get(v_x_3840_, 1);
                    v_tail_3844_ = lean_ctor_get(v_x_3840_, 2);
                    v___x_3845_ = lean_expr_eqv(v_key_3842_, v_a_3839_);
                    if v___x_3845_ == 0 {
                        v_x_3840_ = v_tail_3844_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3843_);
                        v___x_3847_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3847_, 0, v_value_3843_);
                        return v___x_3847_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg___boxed(
    mut v_a_3848_: *mut LeanObject,
    mut v_x_3849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3850_: *mut LeanObject = core::ptr::null_mut();
    v_res_3850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_3848_, v_x_3849_);
    lean_dec(v_x_3849_);
    lean_dec_ref(v_a_3848_);
    return v_res_3850_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(
    mut v_m_3851_: *mut LeanObject,
    mut v_a_3852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_3853_ = lean_ctor_get(v_m_3851_, 1);
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
    mut v_m_3869_: *mut LeanObject,
    mut v_a_3870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3871_: *mut LeanObject = core::ptr::null_mut();
    v_res_3871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_3869_, v_a_3870_);
    lean_dec_ref(v_a_3870_);
    lean_dec_ref(v_m_3869_);
    return v_res_3871_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0(
    mut v_fst_3872_: *mut LeanObject,
    mut v___y_3873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    v___x_3874_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_fst_3872_, v___y_3873_);
    return v___x_3874_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0___boxed(
    mut v_fst_3875_: *mut LeanObject,
    mut v___y_3876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3877_: *mut LeanObject = core::ptr::null_mut();
    v_res_3877_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0(v_fst_3875_, v___y_3876_);
    lean_dec_ref(v___y_3876_);
    lean_dec(v_fst_3875_);
    return v_res_3877_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(
    mut v_a_3878_: *mut LeanObject,
    mut v_x_3879_: *mut LeanObject,
) -> u8 {
    let mut v___x_3880_: u8 = 0;
    let mut v_key_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3879_) == 0 {
                    v___x_3880_ = 0;
                    return v___x_3880_;
                } else {
                    v_key_3881_ = lean_ctor_get(v_x_3879_, 0);
                    v_tail_3882_ = lean_ctor_get(v_x_3879_, 2);
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
    mut v_a_3885_: *mut LeanObject,
    mut v_x_3886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3887_: u8 = 0;
    let mut v_r_3888_: *mut LeanObject = core::ptr::null_mut();
    v_res_3887_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_3885_, v_x_3886_);
    lean_dec(v_x_3886_);
    lean_dec_ref(v_a_3885_);
    v_r_3888_ = lean_box((v_res_3887_) as usize);
    return v_r_3888_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(
    mut v_x_3889_: *mut LeanObject,
    mut v_x_3890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3890_) == 0 {
                    return v_x_3889_;
                } else {
                    v_key_3891_ = lean_ctor_get(v_x_3890_, 0);
                    v_value_3892_ = lean_ctor_get(v_x_3890_, 1);
                    v_tail_3893_ = lean_ctor_get(v_x_3890_, 2);
                    v_isSharedCheck_3916_ = (!lean_is_exclusive(v_x_3890_)) as u8;
                    if v_isSharedCheck_3916_ == 0 {
                        v___x_3895_ = v_x_3890_;
                        v_isShared_3896_ = v_isSharedCheck_3916_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3893_);
                        lean_inc(v_value_3892_);
                        lean_inc(v_key_3891_);
                        lean_dec(v_x_3890_);
                        v___x_3895_ = lean_box(0);
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
                lean_inc(v___x_3910_);
                if v_isShared_3896_ == 0 {
                    lean_ctor_set(v___x_3895_, 2, v___x_3910_);
                    v___x_3912_ = v___x_3895_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_key_3891_);
                    lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_value_3892_);
                    lean_ctor_set(v_reuseFailAlloc_3915_, 2, v___x_3910_);
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
    mut v_i_3917_: *mut LeanObject,
    mut v_source_3918_: *mut LeanObject,
    mut v_target_3919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: u8 = 0;
    let mut v_es_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3920_ = lean_array_get_size(v_source_3918_);
                v___x_3921_ = lean_nat_dec_lt(v_i_3917_, v___x_3920_);
                if v___x_3921_ == 0 {
                    lean_dec_ref(v_source_3918_);
                    lean_dec(v_i_3917_);
                    return v_target_3919_;
                } else {
                    v_es_3922_ = lean_array_fget(v_source_3918_, v_i_3917_);
                    v___x_3923_ = lean_box(0);
                    v_source_3924_ = lean_array_fset(v_source_3918_, v_i_3917_, v___x_3923_);
                    v_target_3925_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_target_3919_, v_es_3922_);
                    v___x_3926_ = lean_unsigned_to_nat(1);
                    v___x_3927_ = lean_nat_add(v_i_3917_, v___x_3926_);
                    lean_dec(v_i_3917_);
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
    mut v_data_3929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    v___x_3930_ = lean_array_get_size(v_data_3929_);
    v___x_3931_ = lean_unsigned_to_nat(2);
    v_nbuckets_3932_ = lean_nat_mul(v___x_3930_, v___x_3931_);
    v___x_3933_ = lean_unsigned_to_nat(0);
    v___x_3934_ = lean_box(0);
    v___x_3935_ = lean_mk_array(v_nbuckets_3932_, v___x_3934_);
    v___x_3936_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v___x_3933_, v_data_3929_, v___x_3935_);
    return v___x_3936_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(
    mut v_a_3937_: *mut LeanObject,
    mut v_b_3938_: *mut LeanObject,
    mut v_x_3939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v___x_3946_: u8 = 0;
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3939_) == 0 {
                    lean_dec(v_b_3938_);
                    lean_dec_ref(v_a_3937_);
                    return v_x_3939_;
                } else {
                    v_key_3940_ = lean_ctor_get(v_x_3939_, 0);
                    v_value_3941_ = lean_ctor_get(v_x_3939_, 1);
                    v_tail_3942_ = lean_ctor_get(v_x_3939_, 2);
                    v_isSharedCheck_3954_ = (!lean_is_exclusive(v_x_3939_)) as u8;
                    if v_isSharedCheck_3954_ == 0 {
                        v___x_3944_ = v_x_3939_;
                        v_isShared_3945_ = v_isSharedCheck_3954_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3942_);
                        lean_inc(v_value_3941_);
                        lean_inc(v_key_3940_);
                        lean_dec(v_x_3939_);
                        v___x_3944_ = lean_box(0);
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
                        lean_ctor_set(v___x_3944_, 2, v___x_3947_);
                        v___x_3949_ = v___x_3944_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3950_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_key_3940_);
                        lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_value_3941_);
                        lean_ctor_set(v_reuseFailAlloc_3950_, 2, v___x_3947_);
                        v___x_3949_ = v_reuseFailAlloc_3950_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3941_);
                    lean_dec(v_key_3940_);
                    if v_isShared_3945_ == 0 {
                        lean_ctor_set(v___x_3944_, 1, v_b_3938_);
                        lean_ctor_set(v___x_3944_, 0, v_a_3937_);
                        v___x_3952_ = v___x_3944_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3937_);
                        lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_b_3938_);
                        lean_ctor_set(v_reuseFailAlloc_3953_, 2, v_tail_3942_);
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
    mut v_m_3955_: *mut LeanObject,
    mut v_a_3956_: *mut LeanObject,
    mut v_b_3957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: u8 = 0;
    let mut v_val_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3958_ = lean_ctor_get(v_m_3955_, 0);
                v_buckets_3959_ = lean_ctor_get(v_m_3955_, 1);
                v_isSharedCheck_4002_ = (!lean_is_exclusive(v_m_3955_)) as u8;
                if v_isSharedCheck_4002_ == 0 {
                    v___x_3961_ = v_m_3955_;
                    v_isShared_3962_ = v_isSharedCheck_4002_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3959_);
                    lean_inc(v_size_3958_);
                    lean_dec(v_m_3955_);
                    v___x_3961_ = lean_box(0);
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
                    v___x_3978_ = lean_unsigned_to_nat(1);
                    v_size_x27_3979_ = lean_nat_add(v_size_3958_, v___x_3978_);
                    lean_dec(v_size_3958_);
                    lean_inc(v_bkt_3976_);
                    v___x_3980_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3980_, 0, v_a_3956_);
                    lean_ctor_set(v___x_3980_, 1, v_b_3957_);
                    lean_ctor_set(v___x_3980_, 2, v_bkt_3976_);
                    v_buckets_x27_3981_ =
                        lean_array_uset(v_buckets_3959_, v___x_3975_, v___x_3980_);
                    v___x_3982_ = lean_unsigned_to_nat(4);
                    v___x_3983_ = lean_nat_mul(v_size_x27_3979_, v___x_3982_);
                    v___x_3984_ = lean_unsigned_to_nat(3);
                    v___x_3985_ = lean_nat_div(v___x_3983_, v___x_3984_);
                    lean_dec(v___x_3983_);
                    v___x_3986_ = lean_array_get_size(v_buckets_x27_3981_);
                    v___x_3987_ = lean_nat_dec_le(v___x_3985_, v___x_3986_);
                    lean_dec(v___x_3985_);
                    if v___x_3987_ == 0 {
                        v_val_3988_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_3981_);
                        if v_isShared_3962_ == 0 {
                            lean_ctor_set(v___x_3961_, 1, v_val_3988_);
                            lean_ctor_set(v___x_3961_, 0, v_size_x27_3979_);
                            v___x_3990_ = v___x_3961_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_size_x27_3979_);
                            lean_ctor_set(v_reuseFailAlloc_3991_, 1, v_val_3988_);
                            v___x_3990_ = v_reuseFailAlloc_3991_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3962_ == 0 {
                            lean_ctor_set(v___x_3961_, 1, v_buckets_x27_3981_);
                            lean_ctor_set(v___x_3961_, 0, v_size_x27_3979_);
                            v___x_3993_ = v___x_3961_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_size_x27_3979_);
                            lean_ctor_set(v_reuseFailAlloc_3994_, 1, v_buckets_x27_3981_);
                            v___x_3993_ = v_reuseFailAlloc_3994_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3976_);
                    v___x_3995_ = lean_box(0);
                    v_buckets_x27_3996_ =
                        lean_array_uset(v_buckets_3959_, v___x_3975_, v___x_3995_);
                    v___x_3997_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_3956_, v_b_3957_, v_bkt_3976_);
                    v___x_3998_ = lean_array_uset(v_buckets_x27_3996_, v___x_3975_, v___x_3997_);
                    if v_isShared_3962_ == 0 {
                        lean_ctor_set(v___x_3961_, 1, v___x_3998_);
                        v___x_4000_ = v___x_3961_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_size_3958_);
                        lean_ctor_set(v_reuseFailAlloc_4001_, 1, v___x_3998_);
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
    mut v_as_4003_: *mut LeanObject,
    mut v_sz_4004_: usize,
    mut v_i_4005_: usize,
    mut v_b_4006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4008_: u8 = 0;
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4014_: u8 = 0;
    let mut v_array_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: u8 = 0;
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4025_: u8 = 0;
    let mut v_a_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: usize = 0;
    let mut v___x_4036_: usize = 0;
    let mut v_reuseFailAlloc_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4040_: u8 = 0;
    let mut v_unused_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4008_ = lean_usize_dec_lt(v_i_4005_, v_sz_4004_);
                if v___x_4008_ == 0 {
                    v___x_4009_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4009_, 0, v_b_4006_);
                    return v___x_4009_;
                } else {
                    v_snd_4010_ = lean_ctor_get(v_b_4006_, 1);
                    v_fst_4011_ = lean_ctor_get(v_b_4006_, 0);
                    v_isSharedCheck_4044_ = (!lean_is_exclusive(v_b_4006_)) as u8;
                    if v_isSharedCheck_4044_ == 0 {
                        v___x_4013_ = v_b_4006_;
                        v_isShared_4014_ = v_isSharedCheck_4044_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4010_);
                        lean_inc(v_fst_4011_);
                        lean_dec(v_b_4006_);
                        v___x_4013_ = lean_box(0);
                        v_isShared_4014_ = v_isSharedCheck_4044_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_4015_ = lean_ctor_get(v_snd_4010_, 0);
                v_start_4016_ = lean_ctor_get(v_snd_4010_, 1);
                v_stop_4017_ = lean_ctor_get(v_snd_4010_, 2);
                v___x_4018_ = lean_nat_dec_lt(v_start_4016_, v_stop_4017_);
                if v___x_4018_ == 0 {
                    if v_isShared_4014_ == 0 {
                        v___x_4020_ = v___x_4013_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_fst_4011_);
                        lean_ctor_set(v_reuseFailAlloc_4022_, 1, v_snd_4010_);
                        v___x_4020_ = v_reuseFailAlloc_4022_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_4017_);
                    lean_inc(v_start_4016_);
                    lean_inc_ref(v_array_4015_);
                    v_isSharedCheck_4040_ = (!lean_is_exclusive(v_snd_4010_)) as u8;
                    if v_isSharedCheck_4040_ == 0 {
                        v_unused_4041_ = lean_ctor_get(v_snd_4010_, 2);
                        lean_dec(v_unused_4041_);
                        v_unused_4042_ = lean_ctor_get(v_snd_4010_, 1);
                        lean_dec(v_unused_4042_);
                        v_unused_4043_ = lean_ctor_get(v_snd_4010_, 0);
                        lean_dec(v_unused_4043_);
                        v___x_4024_ = v_snd_4010_;
                        v_isShared_4025_ = v_isSharedCheck_4040_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_snd_4010_);
                        v___x_4024_ = lean_box(0);
                        v_isShared_4025_ = v_isSharedCheck_4040_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4021_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4021_, 0, v___x_4020_);
                return v___x_4021_;
            }
            3 => {
                v_a_4026_ = lean_array_uget_borrowed(v_as_4003_, v_i_4005_);
                v___x_4027_ = lean_array_fget(v_array_4015_, v_start_4016_);
                v___x_4028_ = lean_unsigned_to_nat(1);
                v___x_4029_ = lean_nat_add(v_start_4016_, v___x_4028_);
                lean_dec(v_start_4016_);
                if v_isShared_4025_ == 0 {
                    lean_ctor_set(v___x_4024_, 1, v___x_4029_);
                    v___x_4031_ = v___x_4024_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_array_4015_);
                    lean_ctor_set(v_reuseFailAlloc_4039_, 1, v___x_4029_);
                    lean_ctor_set(v_reuseFailAlloc_4039_, 2, v_stop_4017_);
                    v___x_4031_ = v_reuseFailAlloc_4039_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_a_4026_);
                v___x_4032_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_fst_4011_, v_a_4026_, v___x_4027_);
                if v_isShared_4014_ == 0 {
                    lean_ctor_set(v___x_4013_, 1, v___x_4031_);
                    lean_ctor_set(v___x_4013_, 0, v___x_4032_);
                    v___x_4034_ = v___x_4013_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4038_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4038_, 0, v___x_4032_);
                    lean_ctor_set(v_reuseFailAlloc_4038_, 1, v___x_4031_);
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
    mut v_as_4045_: *mut LeanObject,
    mut v_sz_4046_: *mut LeanObject,
    mut v_i_4047_: *mut LeanObject,
    mut v_b_4048_: *mut LeanObject,
    mut v___y_4049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4050_: usize = 0;
    let mut v_i_boxed_4051_: usize = 0;
    let mut v_res_4052_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4050_ = lean_unbox_usize(v_sz_4046_);
    lean_dec(v_sz_4046_);
    v_i_boxed_4051_ = lean_unbox_usize(v_i_4047_);
    lean_dec(v_i_4047_);
    v_res_4052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_4045_, v_sz_boxed_4050_, v_i_boxed_4051_, v_b_4048_);
    lean_dec_ref(v_as_4045_);
    return v_res_4052_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1(
    mut v___x_4053_: *mut LeanObject,
    mut v___x_4054_: *mut LeanObject,
    mut v_z_4055_: *mut LeanObject,
    mut v___y_4056_: *mut LeanObject,
    mut v___x_4057_: usize,
    mut v_a_4058_: *mut LeanObject,
    mut v___x_4059_: u8,
    mut v_args_4060_: *mut LeanObject,
    mut v___y_4061_: *mut LeanObject,
    mut v___y_4062_: *mut LeanObject,
    mut v___y_4063_: *mut LeanObject,
    mut v___y_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4083_: usize = 0;
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4095_: u8 = 0;
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4067_ = lean_array_get_size(v_args_4060_);
                v___x_4068_ = lean_nat_add(v___x_4067_, v___x_4053_);
                v___x_4069_ = lean_unsigned_to_nat(0);
                v___x_4070_ = lean_unsigned_to_nat(4);
                v___x_4071_ = lean_nat_mul(v___x_4068_, v___x_4070_);
                lean_dec(v___x_4068_);
                v___x_4072_ = lean_unsigned_to_nat(3);
                v___x_4073_ = lean_nat_div(v___x_4071_, v___x_4072_);
                lean_dec(v___x_4071_);
                v___x_4074_ = l_Nat_nextPowerOfTwo(v___x_4073_);
                lean_dec(v___x_4073_);
                v___x_4075_ = lean_box(0);
                v___x_4076_ = lean_mk_array(v___x_4074_, v___x_4075_);
                v___x_4077_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4077_, 0, v___x_4069_);
                lean_ctor_set(v___x_4077_, 1, v___x_4076_);
                v___x_4078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6;
                v___x_4079_ = l_Lean_mkConst(v___x_4078_, v___x_4054_);
                v___x_4080_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v___x_4077_, v___x_4079_, v_z_4055_);
                lean_inc_ref(v_args_4060_);
                v___x_4081_ = l_Array_toSubarray___redArg(v_args_4060_, v___x_4069_, v___x_4067_);
                v___x_4082_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4082_, 0, v___x_4080_);
                lean_ctor_set(v___x_4082_, 1, v___x_4081_);
                v_sz_4083_ = lean_array_size(v___y_4056_);
                v___x_4084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v___y_4056_, v_sz_4083_, v___x_4057_, v___x_4082_);
                if lean_obj_tag(v___x_4084_) == 0 {
                    v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
                    lean_inc(v_a_4085_);
                    lean_dec_ref_known(v___x_4084_, 1);
                    v_fst_4086_ = lean_ctor_get(v_a_4085_, 0);
                    lean_inc(v_fst_4086_);
                    lean_dec(v_a_4085_);
                    v___f_4087_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_4087_, 0, v_fst_4086_);
                    v___x_4088_ = lean_replace_expr(v___f_4087_, v_a_4058_);
                    lean_dec_ref(v___f_4087_);
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
                    lean_dec_ref(v_args_4060_);
                    return v___x_4091_;
                } else {
                    lean_dec_ref(v_args_4060_);
                    v_a_4092_ = lean_ctor_get(v___x_4084_, 0);
                    v_isSharedCheck_4099_ = (!lean_is_exclusive(v___x_4084_)) as u8;
                    if v_isSharedCheck_4099_ == 0 {
                        v___x_4094_ = v___x_4084_;
                        v_isShared_4095_ = v_isSharedCheck_4099_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4092_);
                        lean_dec(v___x_4084_);
                        v___x_4094_ = lean_box(0);
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
                    v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
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
    mut v___x_4100_: *mut LeanObject,
    mut v___x_4101_: *mut LeanObject,
    mut v_z_4102_: *mut LeanObject,
    mut v___y_4103_: *mut LeanObject,
    mut v___x_4104_: *mut LeanObject,
    mut v_a_4105_: *mut LeanObject,
    mut v___x_4106_: *mut LeanObject,
    mut v_args_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
    mut v___y_4112_: *mut LeanObject,
    mut v___y_4113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_21195__boxed_4114_: usize = 0;
    let mut v___x_21197__boxed_4115_: u8 = 0;
    let mut v_res_4116_: *mut LeanObject = core::ptr::null_mut();
    v___x_21195__boxed_4114_ = lean_unbox_usize(v___x_4104_);
    lean_dec(v___x_4104_);
    v___x_21197__boxed_4115_ = (lean_unbox(v___x_4106_) as u8);
    v_res_4116_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1(v___x_4100_, v___x_4101_, v_z_4102_, v___y_4103_, v___x_21195__boxed_4114_, v_a_4105_, v___x_21197__boxed_4115_, v_args_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
    lean_dec(v___y_4112_);
    lean_dec_ref(v___y_4111_);
    lean_dec(v___y_4110_);
    lean_dec_ref(v___y_4109_);
    lean_dec(v___y_4108_);
    lean_dec_ref(v_a_4105_);
    lean_dec_ref(v___y_4103_);
    lean_dec(v___x_4100_);
    return v_res_4116_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(
    mut v_sz_4117_: usize,
    mut v_i_4118_: usize,
    mut v_bs_4119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4120_: u8 = 0;
    let mut v_v_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4126_: u8 = 0;
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: u8 = 0;
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: usize = 0;
    let mut v___x_4135_: usize = 0;
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4138_: *mut LeanObject = core::ptr::null_mut();
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
                    v_fst_4122_ = lean_ctor_get(v_v_4121_, 0);
                    v_snd_4123_ = lean_ctor_get(v_v_4121_, 1);
                    v_isSharedCheck_4139_ = (!lean_is_exclusive(v_v_4121_)) as u8;
                    if v_isSharedCheck_4139_ == 0 {
                        v___x_4125_ = v_v_4121_;
                        v_isShared_4126_ = v_isSharedCheck_4139_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4123_);
                        lean_inc(v_fst_4122_);
                        lean_dec(v_v_4121_);
                        v___x_4125_ = lean_box(0);
                        v_isShared_4126_ = v_isSharedCheck_4139_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4127_ = lean_unsigned_to_nat(0);
                v_bs_x27_4128_ = lean_array_uset(v_bs_4119_, v_i_4118_, v___x_4127_);
                v___x_4129_ = 0;
                v___x_4130_ = lean_box((v___x_4129_) as usize);
                if v_isShared_4126_ == 0 {
                    lean_ctor_set(v___x_4125_, 0, v___x_4130_);
                    v___x_4132_ = v___x_4125_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4138_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4138_, 0, v___x_4130_);
                    lean_ctor_set(v_reuseFailAlloc_4138_, 1, v_snd_4123_);
                    v___x_4132_ = v_reuseFailAlloc_4138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4133_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4133_, 0, v_fst_4122_);
                lean_ctor_set(v___x_4133_, 1, v___x_4132_);
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
    mut v_sz_4140_: *mut LeanObject,
    mut v_i_4141_: *mut LeanObject,
    mut v_bs_4142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4143_: usize = 0;
    let mut v_i_boxed_4144_: usize = 0;
    let mut v_res_4145_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4143_ = lean_unbox_usize(v_sz_4140_);
    lean_dec(v_sz_4140_);
    v_i_boxed_4144_ = lean_unbox_usize(v_i_4141_);
    lean_dec(v_i_4141_);
    v_res_4145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_boxed_4143_, v_i_boxed_4144_, v_bs_4142_);
    return v_res_4145_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0(
    mut v___x_4146_: *mut LeanObject,
    mut v_a_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_20783__overap_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    v___x_4154_ = l_Lean_instInhabitedExpr;
    v___x_20783__overap_4155_ = l_instInhabitedOfMonad___redArg(v___x_4146_, v___x_4154_);
    lean_inc(v___y_4152_);
    lean_inc_ref(v___y_4151_);
    lean_inc(v___y_4150_);
    lean_inc_ref(v___y_4149_);
    lean_inc(v___y_4148_);
    v___x_4156_ = lean_apply_6(
        v___x_20783__overap_4155_,
        v___y_4148_,
        v___y_4149_,
        v___y_4150_,
        v___y_4151_,
        v___y_4152_,
        lean_box(0),
    );
    return v___x_4156_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0___boxed(
    mut v___x_4157_: *mut LeanObject,
    mut v_a_4158_: *mut LeanObject,
    mut v___y_4159_: *mut LeanObject,
    mut v___y_4160_: *mut LeanObject,
    mut v___y_4161_: *mut LeanObject,
    mut v___y_4162_: *mut LeanObject,
    mut v___y_4163_: *mut LeanObject,
    mut v___y_4164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4165_: *mut LeanObject = core::ptr::null_mut();
    v_res_4165_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0(v___x_4157_, v_a_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
    lean_dec(v___y_4163_);
    lean_dec_ref(v___y_4162_);
    lean_dec(v___y_4161_);
    lean_dec_ref(v___y_4160_);
    lean_dec(v___y_4159_);
    lean_dec_ref(v_a_4158_);
    return v_res_4165_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0()
-> *mut LeanObject {
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    v___x_4166_ = l_instMonadEIO(lean_box(0));
    return v___x_4166_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1()
-> *mut LeanObject {
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    v___x_4167_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__0);
    v___x_4168_ = l_StateRefT_x27_instMonad___redArg(v___x_4167_);
    return v___x_4168_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0___boxed(
    mut v_acc_4173_: *mut LeanObject,
    mut v_declInfos_4174_: *mut LeanObject,
    mut v_k_4175_: *mut LeanObject,
    mut v_kind_4176_: *mut LeanObject,
    mut v___y_4177_: *mut LeanObject,
    mut v_b_4178_: *mut LeanObject,
    mut v___y_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
    mut v___y_4183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4184_: u8 = 0;
    let mut v_res_4185_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4184_ = (lean_unbox(v_kind_4176_) as u8);
    v_res_4185_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0(v_acc_4173_, v_declInfos_4174_, v_k_4175_, v_kind_boxed_4184_, v___y_4177_, v_b_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
    lean_dec(v___y_4182_);
    lean_dec_ref(v___y_4181_);
    lean_dec(v___y_4180_);
    lean_dec_ref(v___y_4179_);
    lean_dec(v___y_4177_);
    return v_res_4185_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(
    mut v_acc_4186_: *mut LeanObject,
    mut v_declInfos_4187_: *mut LeanObject,
    mut v_k_4188_: *mut LeanObject,
    mut v_kind_4189_: u8,
    mut v_name_4190_: *mut LeanObject,
    mut v_bi_4191_: u8,
    mut v_type_4192_: *mut LeanObject,
    mut v_kind_4193_: u8,
    mut v___y_4194_: *mut LeanObject,
    mut v___y_4195_: *mut LeanObject,
    mut v___y_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4200_ = lean_box((v_kind_4189_) as usize);
                lean_inc(v___y_4194_);
                v___f_4201_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                lean_closure_set(v___f_4201_, 0, v_acc_4186_);
                lean_closure_set(v___f_4201_, 1, v_declInfos_4187_);
                lean_closure_set(v___f_4201_, 2, v_k_4188_);
                lean_closure_set(v___f_4201_, 3, v___x_4200_);
                lean_closure_set(v___f_4201_, 4, v___y_4194_);
                v___x_4202_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_4202_) == 0 {
                    return v___x_4202_;
                } else {
                    v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
                    v_isSharedCheck_4210_ = (!lean_is_exclusive(v___x_4202_)) as u8;
                    if v_isSharedCheck_4210_ == 0 {
                        v___x_4205_ = v___x_4202_;
                        v_isShared_4206_ = v_isSharedCheck_4210_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4203_);
                        lean_dec(v___x_4202_);
                        v___x_4205_ = lean_box(0);
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
                    v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
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
    mut v_declInfos_4211_: *mut LeanObject,
    mut v_k_4212_: *mut LeanObject,
    mut v_kind_4213_: u8,
    mut v_acc_4214_: *mut LeanObject,
    mut v___y_4215_: *mut LeanObject,
    mut v___y_4216_: *mut LeanObject,
    mut v___y_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4241_: u8 = 0;
    let mut v_toFunctor_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___f_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: u8 = 0;
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: u8 = 0;
    let mut v___f_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4284_: u8 = 0;
    let mut v_unused_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4286_: u8 = 0;
    let mut v_unused_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4221_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__1);
                v_toApplicative_4222_ = lean_ctor_get(v___x_4221_, 0);
                v_toFunctor_4223_ = lean_ctor_get(v_toApplicative_4222_, 0);
                v_toSeq_4224_ = lean_ctor_get(v_toApplicative_4222_, 2);
                v_toSeqLeft_4225_ = lean_ctor_get(v_toApplicative_4222_, 3);
                v_toSeqRight_4226_ = lean_ctor_get(v_toApplicative_4222_, 4);
                v___f_4227_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__2;
                v___f_4228_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__3;
                lean_inc_ref_n(v_toFunctor_4223_, 2);
                v___f_4229_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4229_, 0, v_toFunctor_4223_);
                v___f_4230_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4230_, 0, v_toFunctor_4223_);
                v___x_4231_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4231_, 0, v___f_4229_);
                lean_ctor_set(v___x_4231_, 1, v___f_4230_);
                lean_inc(v_toSeqRight_4226_);
                v___f_4232_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4232_, 0, v_toSeqRight_4226_);
                lean_inc(v_toSeqLeft_4225_);
                v___f_4233_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4233_, 0, v_toSeqLeft_4225_);
                lean_inc(v_toSeq_4224_);
                v___f_4234_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4234_, 0, v_toSeq_4224_);
                v___x_4235_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_4235_, 0, v___x_4231_);
                lean_ctor_set(v___x_4235_, 1, v___f_4227_);
                lean_ctor_set(v___x_4235_, 2, v___f_4234_);
                lean_ctor_set(v___x_4235_, 3, v___f_4233_);
                lean_ctor_set(v___x_4235_, 4, v___f_4232_);
                v___x_4236_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4236_, 0, v___x_4235_);
                lean_ctor_set(v___x_4236_, 1, v___f_4228_);
                v___x_4237_ = l_StateRefT_x27_instMonad___redArg(v___x_4236_);
                v_toApplicative_4238_ = lean_ctor_get(v___x_4237_, 0);
                v_isSharedCheck_4286_ = (!lean_is_exclusive(v___x_4237_)) as u8;
                if v_isSharedCheck_4286_ == 0 {
                    v_unused_4287_ = lean_ctor_get(v___x_4237_, 1);
                    lean_dec(v_unused_4287_);
                    v___x_4240_ = v___x_4237_;
                    v_isShared_4241_ = v_isSharedCheck_4286_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_4238_);
                    lean_dec(v___x_4237_);
                    v___x_4240_ = lean_box(0);
                    v_isShared_4241_ = v_isSharedCheck_4286_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_4242_ = lean_ctor_get(v_toApplicative_4238_, 0);
                v_toSeq_4243_ = lean_ctor_get(v_toApplicative_4238_, 2);
                v_toSeqLeft_4244_ = lean_ctor_get(v_toApplicative_4238_, 3);
                v_toSeqRight_4245_ = lean_ctor_get(v_toApplicative_4238_, 4);
                v_isSharedCheck_4284_ = (!lean_is_exclusive(v_toApplicative_4238_)) as u8;
                if v_isSharedCheck_4284_ == 0 {
                    v_unused_4285_ = lean_ctor_get(v_toApplicative_4238_, 1);
                    lean_dec(v_unused_4285_);
                    v___x_4247_ = v_toApplicative_4238_;
                    v_isShared_4248_ = v_isSharedCheck_4284_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_4245_);
                    lean_inc(v_toSeqLeft_4244_);
                    lean_inc(v_toSeq_4243_);
                    lean_inc(v_toFunctor_4242_);
                    lean_dec(v_toApplicative_4238_);
                    v___x_4247_ = lean_box(0);
                    v_isShared_4248_ = v_isSharedCheck_4284_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4249_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__4;
                v___f_4250_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___closed__5;
                lean_inc_ref(v_toFunctor_4242_);
                v___f_4251_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4251_, 0, v_toFunctor_4242_);
                v___f_4252_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4252_, 0, v_toFunctor_4242_);
                v___x_4253_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4253_, 0, v___f_4251_);
                lean_ctor_set(v___x_4253_, 1, v___f_4252_);
                v___f_4254_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4254_, 0, v_toSeqRight_4245_);
                v___f_4255_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4255_, 0, v_toSeqLeft_4244_);
                v___f_4256_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_4256_, 0, v_toSeq_4243_);
                if v_isShared_4248_ == 0 {
                    lean_ctor_set(v___x_4247_, 4, v___f_4254_);
                    lean_ctor_set(v___x_4247_, 3, v___f_4255_);
                    lean_ctor_set(v___x_4247_, 2, v___f_4256_);
                    lean_ctor_set(v___x_4247_, 1, v___f_4249_);
                    lean_ctor_set(v___x_4247_, 0, v___x_4253_);
                    v___x_4258_ = v___x_4247_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4253_);
                    lean_ctor_set(v_reuseFailAlloc_4283_, 1, v___f_4249_);
                    lean_ctor_set(v_reuseFailAlloc_4283_, 2, v___f_4256_);
                    lean_ctor_set(v_reuseFailAlloc_4283_, 3, v___f_4255_);
                    lean_ctor_set(v_reuseFailAlloc_4283_, 4, v___f_4254_);
                    v___x_4258_ = v_reuseFailAlloc_4283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4241_ == 0 {
                    lean_ctor_set(v___x_4240_, 1, v___f_4250_);
                    lean_ctor_set(v___x_4240_, 0, v___x_4258_);
                    v___x_4260_ = v___x_4240_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4258_);
                    lean_ctor_set(v_reuseFailAlloc_4282_, 1, v___f_4250_);
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
                    lean_dec_ref(v___x_4261_);
                    lean_dec_ref(v_declInfos_4211_);
                    lean_inc(v___y_4219_);
                    lean_inc_ref(v___y_4218_);
                    lean_inc(v___y_4217_);
                    lean_inc_ref(v___y_4216_);
                    lean_inc(v___y_4215_);
                    v___x_4265_ = lean_apply_7(
                        v_k_4212_,
                        v_acc_4214_,
                        v___y_4215_,
                        v___y_4216_,
                        v___y_4217_,
                        v___y_4218_,
                        v___y_4219_,
                        lean_box(0),
                    );
                    return v___x_4265_;
                } else {
                    v___f_4266_ = lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    lean_closure_set(v___f_4266_, 0, v___x_4261_);
                    v___x_4267_ = lean_box(0);
                    v___x_4268_ = 0;
                    v___f_4269_ = lean_alloc_closure(
                        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_4269_, 0, v___f_4266_);
                    v___x_4270_ = lean_box((v___x_4268_) as usize);
                    v___x_4271_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4271_, 0, v___x_4270_);
                    lean_ctor_set(v___x_4271_, 1, v___f_4269_);
                    v___x_4272_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4272_, 0, v___x_4267_);
                    lean_ctor_set(v___x_4272_, 1, v___x_4271_);
                    v___x_4273_ = lean_array_get(v___x_4272_, v_declInfos_4211_, v___x_4262_);
                    lean_dec_ref_known(v___x_4272_, 2);
                    v_snd_4274_ = lean_ctor_get(v___x_4273_, 1);
                    lean_inc(v_snd_4274_);
                    v_fst_4275_ = lean_ctor_get(v___x_4273_, 0);
                    lean_inc(v_fst_4275_);
                    lean_dec(v___x_4273_);
                    v_fst_4276_ = lean_ctor_get(v_snd_4274_, 0);
                    lean_inc(v_fst_4276_);
                    v_snd_4277_ = lean_ctor_get(v_snd_4274_, 1);
                    lean_inc(v_snd_4277_);
                    lean_dec(v_snd_4274_);
                    lean_inc(v___y_4219_);
                    lean_inc_ref(v___y_4218_);
                    lean_inc(v___y_4217_);
                    lean_inc_ref(v___y_4216_);
                    lean_inc(v___y_4215_);
                    lean_inc_ref(v_acc_4214_);
                    v___x_4278_ = lean_apply_7(
                        v_snd_4277_,
                        v_acc_4214_,
                        v___y_4215_,
                        v___y_4216_,
                        v___y_4217_,
                        v___y_4218_,
                        v___y_4219_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_4278_) == 0 {
                        v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
                        lean_inc(v_a_4279_);
                        lean_dec_ref_known(v___x_4278_, 1);
                        v___x_4280_ = (lean_unbox(v_fst_4276_) as u8);
                        lean_dec(v_fst_4276_);
                        v___x_4281_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(v_acc_4214_, v_declInfos_4211_, v_k_4212_, v_kind_4213_, v_fst_4275_, v___x_4280_, v_a_4279_, v_kind_4213_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
                        return v___x_4281_;
                    } else {
                        lean_dec(v_fst_4276_);
                        lean_dec(v_fst_4275_);
                        lean_dec_ref(v_acc_4214_);
                        lean_dec_ref(v_k_4212_);
                        lean_dec_ref(v_declInfos_4211_);
                        return v___x_4278_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___lam__0(
    mut v_acc_4288_: *mut LeanObject,
    mut v_declInfos_4289_: *mut LeanObject,
    mut v_k_4290_: *mut LeanObject,
    mut v_kind_4291_: u8,
    mut v___y_4292_: *mut LeanObject,
    mut v_b_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
    mut v___y_4295_: *mut LeanObject,
    mut v___y_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    v___x_4299_ = lean_array_push(v_acc_4288_, v_b_4293_);
    v___x_4300_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_4289_, v_k_4290_, v_kind_4291_, v___x_4299_, v___y_4292_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
    return v___x_4300_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34___boxed(
    mut v_acc_4301_: *mut LeanObject,
    mut v_declInfos_4302_: *mut LeanObject,
    mut v_k_4303_: *mut LeanObject,
    mut v_kind_4304_: *mut LeanObject,
    mut v_name_4305_: *mut LeanObject,
    mut v_bi_4306_: *mut LeanObject,
    mut v_type_4307_: *mut LeanObject,
    mut v_kind_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
    mut v___y_4310_: *mut LeanObject,
    mut v___y_4311_: *mut LeanObject,
    mut v___y_4312_: *mut LeanObject,
    mut v___y_4313_: *mut LeanObject,
    mut v___y_4314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4315_: u8 = 0;
    let mut v_bi_boxed_4316_: u8 = 0;
    let mut v_kind_boxed_4317_: u8 = 0;
    let mut v_res_4318_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4315_ = (lean_unbox(v_kind_4304_) as u8);
    v_bi_boxed_4316_ = (lean_unbox(v_bi_4306_) as u8);
    v_kind_boxed_4317_ = (lean_unbox(v_kind_4308_) as u8);
    v_res_4318_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27_spec__34(v_acc_4301_, v_declInfos_4302_, v_k_4303_, v_kind_boxed_4315_, v_name_4305_, v_bi_boxed_4316_, v_type_4307_, v_kind_boxed_4317_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
    lean_dec(v___y_4313_);
    lean_dec_ref(v___y_4312_);
    lean_dec(v___y_4311_);
    lean_dec_ref(v___y_4310_);
    lean_dec(v___y_4309_);
    return v_res_4318_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27___boxed(
    mut v_declInfos_4319_: *mut LeanObject,
    mut v_k_4320_: *mut LeanObject,
    mut v_kind_4321_: *mut LeanObject,
    mut v_acc_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4329_: u8 = 0;
    let mut v_res_4330_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4329_ = (lean_unbox(v_kind_4321_) as u8);
    v_res_4330_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_4319_, v_k_4320_, v_kind_boxed_4329_, v_acc_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
    lean_dec(v___y_4327_);
    lean_dec_ref(v___y_4326_);
    lean_dec(v___y_4325_);
    lean_dec_ref(v___y_4324_);
    lean_dec(v___y_4323_);
    return v_res_4330_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(
    mut v_declInfos_4333_: *mut LeanObject,
    mut v_k_4334_: *mut LeanObject,
    mut v_kind_4335_: u8,
    mut v___y_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    v___x_4342_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___closed__0;
    v___x_4343_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14_spec__27(v_declInfos_4333_, v_k_4334_, v_kind_4335_, v___x_4342_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
    return v___x_4343_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14___boxed(
    mut v_declInfos_4344_: *mut LeanObject,
    mut v_k_4345_: *mut LeanObject,
    mut v_kind_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4353_: u8 = 0;
    let mut v_res_4354_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4353_ = (lean_unbox(v_kind_4346_) as u8);
    v_res_4354_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(v_declInfos_4344_, v_k_4345_, v_kind_boxed_4353_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
    lean_dec(v___y_4351_);
    lean_dec_ref(v___y_4350_);
    lean_dec(v___y_4349_);
    lean_dec_ref(v___y_4348_);
    lean_dec(v___y_4347_);
    return v_res_4354_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(
    mut v_declInfos_4355_: *mut LeanObject,
    mut v_k_4356_: *mut LeanObject,
    mut v_kind_4357_: u8,
    mut v___y_4358_: *mut LeanObject,
    mut v___y_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_4364_: usize = 0;
    let mut v___x_4365_: usize = 0;
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    v_sz_4364_ = lean_array_size(v_declInfos_4355_);
    v___x_4365_ = 0usize;
    v___x_4366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__13(v_sz_4364_, v___x_4365_, v_declInfos_4355_);
    v___x_4367_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10_spec__14(v___x_4366_, v_k_4356_, v_kind_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_);
    return v___x_4367_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10___boxed(
    mut v_declInfos_4368_: *mut LeanObject,
    mut v_k_4369_: *mut LeanObject,
    mut v_kind_4370_: *mut LeanObject,
    mut v___y_4371_: *mut LeanObject,
    mut v___y_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4377_: u8 = 0;
    let mut v_res_4378_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4377_ = (lean_unbox(v_kind_4370_) as u8);
    v_res_4378_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(v_declInfos_4368_, v_k_4369_, v_kind_boxed_4377_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
    lean_dec(v___y_4375_);
    lean_dec_ref(v___y_4374_);
    lean_dec(v___y_4373_);
    lean_dec_ref(v___y_4372_);
    lean_dec(v___y_4371_);
    return v_res_4378_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(
    mut v_snd_4379_: *mut LeanObject,
    mut v_x_4380_: *mut LeanObject,
    mut v___y_4381_: *mut LeanObject,
    mut v___y_4382_: *mut LeanObject,
    mut v___y_4383_: *mut LeanObject,
    mut v___y_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    v___x_4387_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4387_, 0, v_snd_4379_);
    return v___x_4387_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed(
    mut v_snd_4388_: *mut LeanObject,
    mut v_x_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4396_: *mut LeanObject = core::ptr::null_mut();
    v_res_4396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0(v_snd_4388_, v_x_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
    lean_dec(v___y_4394_);
    lean_dec_ref(v___y_4393_);
    lean_dec(v___y_4392_);
    lean_dec_ref(v___y_4391_);
    lean_dec(v___y_4390_);
    lean_dec_ref(v_x_4389_);
    return v_res_4396_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(
    mut v_sz_4397_: usize,
    mut v_i_4398_: usize,
    mut v_bs_4399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4400_: u8 = 0;
    let mut v_v_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4406_: u8 = 0;
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: usize = 0;
    let mut v___x_4413_: usize = 0;
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4416_: *mut LeanObject = core::ptr::null_mut();
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
                    v_fst_4402_ = lean_ctor_get(v_v_4401_, 0);
                    v_snd_4403_ = lean_ctor_get(v_v_4401_, 1);
                    v_isSharedCheck_4417_ = (!lean_is_exclusive(v_v_4401_)) as u8;
                    if v_isSharedCheck_4417_ == 0 {
                        v___x_4405_ = v_v_4401_;
                        v_isShared_4406_ = v_isSharedCheck_4417_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4403_);
                        lean_inc(v_fst_4402_);
                        lean_dec(v_v_4401_);
                        v___x_4405_ = lean_box(0);
                        v_isShared_4406_ = v_isSharedCheck_4417_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4407_ = lean_unsigned_to_nat(0);
                v_bs_x27_4408_ = lean_array_uset(v_bs_4399_, v_i_4398_, v___x_4407_);
                v___f_4409_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_4409_, 0, v_snd_4403_);
                if v_isShared_4406_ == 0 {
                    lean_ctor_set(v___x_4405_, 1, v___f_4409_);
                    v___x_4411_ = v___x_4405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_fst_4402_);
                    lean_ctor_set(v_reuseFailAlloc_4416_, 1, v___f_4409_);
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
    mut v_sz_4418_: *mut LeanObject,
    mut v_i_4419_: *mut LeanObject,
    mut v_bs_4420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4421_: usize = 0;
    let mut v_i_boxed_4422_: usize = 0;
    let mut v_res_4423_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4421_ = lean_unbox_usize(v_sz_4418_);
    lean_dec(v_sz_4418_);
    v_i_boxed_4422_ = lean_unbox_usize(v_i_4419_);
    lean_dec(v_i_4419_);
    v_res_4423_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_boxed_4421_, v_i_boxed_4422_, v_bs_4420_);
    return v_res_4423_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5(
    mut v_declInfos_4424_: *mut LeanObject,
    mut v_k_4425_: *mut LeanObject,
    mut v_kind_4426_: u8,
    mut v___y_4427_: *mut LeanObject,
    mut v___y_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
    mut v___y_4431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_4433_: usize = 0;
    let mut v___x_4434_: usize = 0;
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    v_sz_4433_ = lean_array_size(v_declInfos_4424_);
    v___x_4434_ = 0usize;
    v___x_4435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__9(v_sz_4433_, v___x_4434_, v_declInfos_4424_);
    v___x_4436_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5_spec__10(v___x_4435_, v_k_4425_, v_kind_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
    return v___x_4436_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5___boxed(
    mut v_declInfos_4437_: *mut LeanObject,
    mut v_k_4438_: *mut LeanObject,
    mut v_kind_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
    mut v___y_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v___y_4445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4446_: u8 = 0;
    let mut v_res_4447_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4446_ = (lean_unbox(v_kind_4439_) as u8);
    v_res_4447_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5(v_declInfos_4437_, v_k_4438_, v_kind_boxed_4446_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_);
    lean_dec(v___y_4444_);
    lean_dec_ref(v___y_4443_);
    lean_dec(v___y_4442_);
    lean_dec_ref(v___y_4441_);
    lean_dec(v___y_4440_);
    return v_res_4447_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4(
    mut v___x_4451_: *mut LeanObject,
    mut v_sz_4452_: usize,
    mut v_i_4453_: usize,
    mut v_bs_4454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4455_: u8 = 0;
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: usize = 0;
    let mut v___x_4461_: usize = 0;
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4455_ = lean_usize_dec_lt(v_i_4453_, v_sz_4452_);
                if v___x_4455_ == 0 {
                    lean_dec_ref(v___x_4451_);
                    return v_bs_4454_;
                } else {
                    v___x_4456_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4457_ = lean_array_uset(v_bs_4454_, v_i_4453_, v___x_4456_);
                    v___x_4458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4___closed__1;
                    lean_inc_ref(v___x_4451_);
                    v___x_4459_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4459_, 0, v___x_4458_);
                    lean_ctor_set(v___x_4459_, 1, v___x_4451_);
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
    mut v___x_4464_: *mut LeanObject,
    mut v_sz_4465_: *mut LeanObject,
    mut v_i_4466_: *mut LeanObject,
    mut v_bs_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4468_: usize = 0;
    let mut v_i_boxed_4469_: usize = 0;
    let mut v_res_4470_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4468_ = lean_unbox_usize(v_sz_4465_);
    lean_dec(v_sz_4465_);
    v_i_boxed_4469_ = lean_unbox_usize(v_i_4466_);
    lean_dec(v_i_4466_);
    v_res_4470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_4464_, v_sz_boxed_4468_, v_i_boxed_4469_, v_bs_4467_);
    return v_res_4470_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2(
    mut v___x_4474_: *mut LeanObject,
    mut v_z_4475_: *mut LeanObject,
    mut v___y_4476_: *mut LeanObject,
    mut v___x_4477_: usize,
    mut v___f_4478_: *mut LeanObject,
    mut v___x_4479_: *mut LeanObject,
    mut v___x_4480_: u8,
    mut v_other_4481_: *mut LeanObject,
    mut v___y_4482_: *mut LeanObject,
    mut v___y_4483_: *mut LeanObject,
    mut v___y_4484_: *mut LeanObject,
    mut v___y_4485_: *mut LeanObject,
    mut v___y_4486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4491_: usize = 0;
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: u8 = 0;
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4507_: u8 = 0;
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4512_: u8 = 0;
    let mut v_a_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4516_: u8 = 0;
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4520_: u8 = 0;
    let mut v_a_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4488_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___closed__1;
                v___x_4489_ = l_Lean_mkConst(v___x_4488_, v___x_4474_);
                lean_inc_ref(v_z_4475_);
                v___x_4490_ = l_Lean_Expr_app___override(v___x_4489_, v_z_4475_);
                v_sz_4491_ = lean_array_size(v___y_4476_);
                v___x_4492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__4(v___x_4490_, v_sz_4491_, v___x_4477_, v___y_4476_);
                v___x_4493_ = 0;
                v___x_4494_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__5(v___x_4492_, v___f_4478_, v___x_4493_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
                if lean_obj_tag(v___x_4494_) == 0 {
                    v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
                    lean_inc(v_a_4495_);
                    lean_dec_ref_known(v___x_4494_, 1);
                    lean_inc_ref(v_z_4475_);
                    v___x_4496_ = l_Lean_Expr_replaceFVar(v_a_4495_, v_z_4475_, v___x_4479_);
                    v___x_4497_ = lean_unsigned_to_nat(2);
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
                    lean_dec_ref(v___x_4500_);
                    if lean_obj_tag(v___x_4503_) == 0 {
                        v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
                        v_isSharedCheck_4512_ = (!lean_is_exclusive(v___x_4503_)) as u8;
                        if v_isSharedCheck_4512_ == 0 {
                            v___x_4506_ = v___x_4503_;
                            v_isShared_4507_ = v_isSharedCheck_4512_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4504_);
                            lean_dec(v___x_4503_);
                            v___x_4506_ = lean_box(0);
                            v_isShared_4507_ = v_isSharedCheck_4512_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4496_);
                        v_a_4513_ = lean_ctor_get(v___x_4503_, 0);
                        v_isSharedCheck_4520_ = (!lean_is_exclusive(v___x_4503_)) as u8;
                        if v_isSharedCheck_4520_ == 0 {
                            v___x_4515_ = v___x_4503_;
                            v_isShared_4516_ = v_isSharedCheck_4520_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4513_);
                            lean_dec(v___x_4503_);
                            v___x_4515_ = lean_box(0);
                            v_isShared_4516_ = v_isSharedCheck_4520_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_other_4481_);
                    lean_dec_ref(v_z_4475_);
                    v_a_4521_ = lean_ctor_get(v___x_4494_, 0);
                    v_isSharedCheck_4528_ = (!lean_is_exclusive(v___x_4494_)) as u8;
                    if v_isSharedCheck_4528_ == 0 {
                        v___x_4523_ = v___x_4494_;
                        v_isShared_4524_ = v_isSharedCheck_4528_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4521_);
                        lean_dec(v___x_4494_);
                        v___x_4523_ = lean_box(0);
                        v_isShared_4524_ = v_isSharedCheck_4528_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4508_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4508_, 0, v_a_4504_);
                lean_ctor_set(v___x_4508_, 1, v___x_4496_);
                if v_isShared_4507_ == 0 {
                    lean_ctor_set(v___x_4506_, 0, v___x_4508_);
                    v___x_4510_ = v___x_4506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4511_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4508_);
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
                    v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
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
                    v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
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
    mut v___x_4529_: *mut LeanObject,
    mut v_z_4530_: *mut LeanObject,
    mut v___y_4531_: *mut LeanObject,
    mut v___x_4532_: *mut LeanObject,
    mut v___f_4533_: *mut LeanObject,
    mut v___x_4534_: *mut LeanObject,
    mut v___x_4535_: *mut LeanObject,
    mut v_other_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
    mut v___y_4538_: *mut LeanObject,
    mut v___y_4539_: *mut LeanObject,
    mut v___y_4540_: *mut LeanObject,
    mut v___y_4541_: *mut LeanObject,
    mut v___y_4542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_21741__boxed_4543_: usize = 0;
    let mut v___x_21744__boxed_4544_: u8 = 0;
    let mut v_res_4545_: *mut LeanObject = core::ptr::null_mut();
    v___x_21741__boxed_4543_ = lean_unbox_usize(v___x_4532_);
    lean_dec(v___x_4532_);
    v___x_21744__boxed_4544_ = (lean_unbox(v___x_4535_) as u8);
    v_res_4545_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2(v___x_4529_, v_z_4530_, v___y_4531_, v___x_21741__boxed_4543_, v___f_4533_, v___x_4534_, v___x_21744__boxed_4544_, v_other_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_);
    lean_dec(v___y_4541_);
    lean_dec_ref(v___y_4540_);
    lean_dec(v___y_4539_);
    lean_dec_ref(v___y_4538_);
    lean_dec(v___y_4537_);
    lean_dec_ref(v___x_4534_);
    return v_res_4545_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(
    mut v_k_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
    mut v_b_4548_: *mut LeanObject,
    mut v___y_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
    mut v___y_4552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4552_);
    lean_inc_ref(v___y_4551_);
    lean_inc(v___y_4550_);
    lean_inc_ref(v___y_4549_);
    lean_inc(v___y_4547_);
    v___x_4554_ = lean_apply_7(
        v_k_4546_,
        v_b_4548_,
        v___y_4547_,
        v___y_4549_,
        v___y_4550_,
        v___y_4551_,
        v___y_4552_,
        lean_box(0),
    );
    return v___x_4554_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed(
    mut v_k_4555_: *mut LeanObject,
    mut v___y_4556_: *mut LeanObject,
    mut v_b_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
    mut v___y_4560_: *mut LeanObject,
    mut v___y_4561_: *mut LeanObject,
    mut v___y_4562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4563_: *mut LeanObject = core::ptr::null_mut();
    v_res_4563_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0(v_k_4555_, v___y_4556_, v_b_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
    lean_dec(v___y_4561_);
    lean_dec_ref(v___y_4560_);
    lean_dec(v___y_4559_);
    lean_dec_ref(v___y_4558_);
    lean_dec(v___y_4556_);
    return v_res_4563_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(
    mut v_name_4564_: *mut LeanObject,
    mut v_bi_4565_: u8,
    mut v_type_4566_: *mut LeanObject,
    mut v_k_4567_: *mut LeanObject,
    mut v_kind_4568_: u8,
    mut v___y_4569_: *mut LeanObject,
    mut v___y_4570_: *mut LeanObject,
    mut v___y_4571_: *mut LeanObject,
    mut v___y_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_4569_);
                v___f_4575_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                lean_closure_set(v___f_4575_, 0, v_k_4567_);
                lean_closure_set(v___f_4575_, 1, v___y_4569_);
                v___x_4576_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_4576_) == 0 {
                    return v___x_4576_;
                } else {
                    v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
                    v_isSharedCheck_4584_ = (!lean_is_exclusive(v___x_4576_)) as u8;
                    if v_isSharedCheck_4584_ == 0 {
                        v___x_4579_ = v___x_4576_;
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4577_);
                        lean_dec(v___x_4576_);
                        v___x_4579_ = lean_box(0);
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
                    v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
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
    mut v_name_4585_: *mut LeanObject,
    mut v_bi_4586_: *mut LeanObject,
    mut v_type_4587_: *mut LeanObject,
    mut v_k_4588_: *mut LeanObject,
    mut v_kind_4589_: *mut LeanObject,
    mut v___y_4590_: *mut LeanObject,
    mut v___y_4591_: *mut LeanObject,
    mut v___y_4592_: *mut LeanObject,
    mut v___y_4593_: *mut LeanObject,
    mut v___y_4594_: *mut LeanObject,
    mut v___y_4595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_4596_: u8 = 0;
    let mut v_kind_boxed_4597_: u8 = 0;
    let mut v_res_4598_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_4596_ = (lean_unbox(v_bi_4586_) as u8);
    v_kind_boxed_4597_ = (lean_unbox(v_kind_4589_) as u8);
    v_res_4598_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_4585_, v_bi_boxed_4596_, v_type_4587_, v_k_4588_, v_kind_boxed_4597_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
    lean_dec(v___y_4594_);
    lean_dec_ref(v___y_4593_);
    lean_dec(v___y_4592_);
    lean_dec_ref(v___y_4591_);
    lean_dec(v___y_4590_);
    return v_res_4598_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(
    mut v_name_4599_: *mut LeanObject,
    mut v_type_4600_: *mut LeanObject,
    mut v_k_4601_: *mut LeanObject,
    mut v___y_4602_: *mut LeanObject,
    mut v___y_4603_: *mut LeanObject,
    mut v___y_4604_: *mut LeanObject,
    mut v___y_4605_: *mut LeanObject,
    mut v___y_4606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4608_: u8 = 0;
    let mut v___x_4609_: u8 = 0;
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    v___x_4608_ = 0;
    v___x_4609_ = 0;
    v___x_4610_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_4599_, v___x_4608_, v_type_4600_, v_k_4601_, v___x_4609_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
    return v___x_4610_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg___boxed(
    mut v_name_4611_: *mut LeanObject,
    mut v_type_4612_: *mut LeanObject,
    mut v_k_4613_: *mut LeanObject,
    mut v___y_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
    mut v___y_4617_: *mut LeanObject,
    mut v___y_4618_: *mut LeanObject,
    mut v___y_4619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4620_: *mut LeanObject = core::ptr::null_mut();
    v_res_4620_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_4611_, v_type_4612_, v_k_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
    lean_dec(v___y_4618_);
    lean_dec_ref(v___y_4617_);
    lean_dec(v___y_4616_);
    lean_dec_ref(v___y_4615_);
    lean_dec(v___y_4614_);
    return v_res_4620_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3(
    mut v___x_4624_: *mut LeanObject,
    mut v___y_4625_: *mut LeanObject,
    mut v___x_4626_: usize,
    mut v_a_4627_: *mut LeanObject,
    mut v___x_4628_: u8,
    mut v_fst_4629_: *mut LeanObject,
    mut v___x_4630_: *mut LeanObject,
    mut v_z_4631_: *mut LeanObject,
    mut v___y_4632_: *mut LeanObject,
    mut v___y_4633_: *mut LeanObject,
    mut v___y_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
    mut v___y_4636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    v___x_4638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__2;
    v___x_4639_ = lean_unsigned_to_nat(1);
    v___x_4640_ = lean_box_usize(v___x_4626_);
    v___x_4641_ = lean_box((v___x_4628_) as usize);
    lean_inc_ref(v___y_4625_);
    lean_inc_ref_n(v_z_4631_, 2);
    lean_inc_n(v___x_4624_, 2);
    v___f_4642_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__1___boxed as *mut core::ffi::c_void, 14, 7);
    lean_closure_set(v___f_4642_, 0, v___x_4639_);
    lean_closure_set(v___f_4642_, 1, v___x_4624_);
    lean_closure_set(v___f_4642_, 2, v_z_4631_);
    lean_closure_set(v___f_4642_, 3, v___y_4625_);
    lean_closure_set(v___f_4642_, 4, v___x_4640_);
    lean_closure_set(v___f_4642_, 5, v_a_4627_);
    lean_closure_set(v___f_4642_, 6, v___x_4641_);
    v___x_4643_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__11);
    v___x_4644_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4644_, 0, v___x_4643_);
    lean_ctor_set(v___x_4644_, 1, v___x_4624_);
    v___x_4645_ = l_Lean_mkConst(v___x_4638_, v___x_4644_);
    v___x_4646_ = l_Lean_mkNatLit(v_fst_4629_);
    v___x_4647_ = lean_box_usize(v___x_4626_);
    v___x_4648_ = lean_box((v___x_4628_) as usize);
    lean_inc_ref(v___x_4646_);
    v___f_4649_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__2___boxed as *mut core::ffi::c_void, 14, 7);
    lean_closure_set(v___f_4649_, 0, v___x_4624_);
    lean_closure_set(v___f_4649_, 1, v_z_4631_);
    lean_closure_set(v___f_4649_, 2, v___y_4625_);
    lean_closure_set(v___f_4649_, 3, v___x_4647_);
    lean_closure_set(v___f_4649_, 4, v___f_4642_);
    lean_closure_set(v___f_4649_, 5, v___x_4646_);
    lean_closure_set(v___f_4649_, 6, v___x_4648_);
    v___x_4650_ = l_Lean_mkApp3(v___x_4645_, v___x_4630_, v___x_4646_, v_z_4631_);
    v___x_4651_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___closed__1;
    v___x_4652_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_4651_, v___x_4650_, v___f_4649_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_);
    return v___x_4652_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___boxed(
    mut v___x_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___x_4655_: *mut LeanObject,
    mut v_a_4656_: *mut LeanObject,
    mut v___x_4657_: *mut LeanObject,
    mut v_fst_4658_: *mut LeanObject,
    mut v___x_4659_: *mut LeanObject,
    mut v_z_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
    mut v___y_4662_: *mut LeanObject,
    mut v___y_4663_: *mut LeanObject,
    mut v___y_4664_: *mut LeanObject,
    mut v___y_4665_: *mut LeanObject,
    mut v___y_4666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_21954__boxed_4667_: usize = 0;
    let mut v___x_21956__boxed_4668_: u8 = 0;
    let mut v_res_4669_: *mut LeanObject = core::ptr::null_mut();
    v___x_21954__boxed_4667_ = lean_unbox_usize(v___x_4655_);
    lean_dec(v___x_4655_);
    v___x_21956__boxed_4668_ = (lean_unbox(v___x_4657_) as u8);
    v_res_4669_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3(v___x_4653_, v___y_4654_, v___x_21954__boxed_4667_, v_a_4656_, v___x_21956__boxed_4668_, v_fst_4658_, v___x_4659_, v_z_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
    lean_dec(v___y_4665_);
    lean_dec_ref(v___y_4664_);
    lean_dec(v___y_4663_);
    lean_dec_ref(v___y_4662_);
    lean_dec(v___y_4661_);
    return v_res_4669_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__10(
    mut v_x_4670_: *mut LeanObject,
    mut v_x_4671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4671_) == 0 {
                    return v_x_4670_;
                } else {
                    v_key_4672_ = lean_ctor_get(v_x_4671_, 0);
                    lean_inc(v_key_4672_);
                    v_tail_4673_ = lean_ctor_get(v_x_4671_, 2);
                    lean_inc(v_tail_4673_);
                    lean_dec_ref_known(v_x_4671_, 3);
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
    mut v_as_4676_: *mut LeanObject,
    mut v_i_4677_: usize,
    mut v_stop_4678_: usize,
    mut v_b_4679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4680_: u8 = 0;
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: usize = 0;
    let mut v___x_4684_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4680_ = lean_usize_dec_eq(v_i_4677_, v_stop_4678_);
                if v___x_4680_ == 0 {
                    v___x_4681_ = lean_array_uget_borrowed(v_as_4676_, v_i_4677_);
                    lean_inc(v___x_4681_);
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
    mut v_as_4686_: *mut LeanObject,
    mut v_i_4687_: *mut LeanObject,
    mut v_stop_4688_: *mut LeanObject,
    mut v_b_4689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4690_: usize = 0;
    let mut v_stop_boxed_4691_: usize = 0;
    let mut v_res_4692_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4690_ = lean_unbox_usize(v_i_4687_);
    lean_dec(v_i_4687_);
    v_stop_boxed_4691_ = lean_unbox_usize(v_stop_4688_);
    lean_dec(v_stop_4688_);
    v_res_4692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(v_as_4686_, v_i_boxed_4690_, v_stop_boxed_4691_, v_b_4689_);
    lean_dec_ref(v_as_4686_);
    return v_res_4692_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(
    mut v_msgData_4693_: *mut LeanObject,
    mut v___y_4694_: *mut LeanObject,
    mut v___y_4695_: *mut LeanObject,
    mut v___y_4696_: *mut LeanObject,
    mut v___y_4697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    v___x_4699_ = lean_st_ref_get(v___y_4697_);
    v_env_4700_ = lean_ctor_get(v___x_4699_, 0);
    lean_inc_ref(v_env_4700_);
    lean_dec(v___x_4699_);
    v___x_4701_ = lean_st_ref_get(v___y_4695_);
    v_mctx_4702_ = lean_ctor_get(v___x_4701_, 0);
    lean_inc_ref(v_mctx_4702_);
    lean_dec(v___x_4701_);
    v_lctx_4703_ = lean_ctor_get(v___y_4694_, 2);
    v_options_4704_ = lean_ctor_get(v___y_4696_, 2);
    lean_inc_ref(v_options_4704_);
    lean_inc_ref(v_lctx_4703_);
    v___x_4705_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4705_, 0, v_env_4700_);
    lean_ctor_set(v___x_4705_, 1, v_mctx_4702_);
    lean_ctor_set(v___x_4705_, 2, v_lctx_4703_);
    lean_ctor_set(v___x_4705_, 3, v_options_4704_);
    v___x_4706_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4706_, 0, v___x_4705_);
    lean_ctor_set(v___x_4706_, 1, v_msgData_4693_);
    v___x_4707_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4707_, 0, v___x_4706_);
    return v___x_4707_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17___boxed(
    mut v_msgData_4708_: *mut LeanObject,
    mut v___y_4709_: *mut LeanObject,
    mut v___y_4710_: *mut LeanObject,
    mut v___y_4711_: *mut LeanObject,
    mut v___y_4712_: *mut LeanObject,
    mut v___y_4713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4714_: *mut LeanObject = core::ptr::null_mut();
    v_res_4714_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msgData_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
    lean_dec(v___y_4712_);
    lean_dec_ref(v___y_4711_);
    lean_dec(v___y_4710_);
    lean_dec_ref(v___y_4709_);
    return v_res_4714_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(
    mut v_msg_4715_: *mut LeanObject,
    mut v___y_4716_: *mut LeanObject,
    mut v___y_4717_: *mut LeanObject,
    mut v___y_4718_: *mut LeanObject,
    mut v___y_4719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4726_: u8 = 0;
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4721_ = lean_ctor_get(v___y_4718_, 5);
                v___x_4722_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v_msg_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
                v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
                v_isSharedCheck_4731_ = (!lean_is_exclusive(v___x_4722_)) as u8;
                if v_isSharedCheck_4731_ == 0 {
                    v___x_4725_ = v___x_4722_;
                    v_isShared_4726_ = v_isSharedCheck_4731_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4723_);
                    lean_dec(v___x_4722_);
                    v___x_4725_ = lean_box(0);
                    v_isShared_4726_ = v_isSharedCheck_4731_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4721_);
                v___x_4727_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4727_, 0, v_ref_4721_);
                lean_ctor_set(v___x_4727_, 1, v_a_4723_);
                if v_isShared_4726_ == 0 {
                    lean_ctor_set_tag(v___x_4725_, 1);
                    lean_ctor_set(v___x_4725_, 0, v___x_4727_);
                    v___x_4729_ = v___x_4725_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4730_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4727_);
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
    mut v_msg_4732_: *mut LeanObject,
    mut v___y_4733_: *mut LeanObject,
    mut v___y_4734_: *mut LeanObject,
    mut v___y_4735_: *mut LeanObject,
    mut v___y_4736_: *mut LeanObject,
    mut v___y_4737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4738_: *mut LeanObject = core::ptr::null_mut();
    v_res_4738_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
    lean_dec(v___y_4736_);
    lean_dec_ref(v___y_4735_);
    lean_dec(v___y_4734_);
    lean_dec_ref(v___y_4733_);
    return v_res_4738_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1(
    mut v_sz_4739_: usize,
    mut v_i_4740_: usize,
    mut v_bs_4741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4742_: u8 = 0;
    let mut v_v_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: usize = 0;
    let mut v___x_4748_: usize = 0;
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4742_ = lean_usize_dec_lt(v_i_4740_, v_sz_4739_);
                if v___x_4742_ == 0 {
                    return v_bs_4741_;
                } else {
                    v_v_4743_ = lean_array_uget(v_bs_4741_, v_i_4740_);
                    v___x_4744_ = lean_unsigned_to_nat(0);
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
    mut v_sz_4751_: *mut LeanObject,
    mut v_i_4752_: *mut LeanObject,
    mut v_bs_4753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4754_: usize = 0;
    let mut v_i_boxed_4755_: usize = 0;
    let mut v_res_4756_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4754_ = lean_unbox_usize(v_sz_4751_);
    lean_dec(v_sz_4751_);
    v_i_boxed_4755_ = lean_unbox_usize(v_i_4752_);
    lean_dec(v_i_4752_);
    v_res_4756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_boxed_4754_, v_i_boxed_4755_, v_bs_4753_);
    return v_res_4756_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__12(
    mut v_x_4757_: *mut LeanObject,
    mut v_x_4758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4758_) == 0 {
                    return v_x_4757_;
                } else {
                    v_key_4759_ = lean_ctor_get(v_x_4758_, 0);
                    lean_inc(v_key_4759_);
                    v_tail_4760_ = lean_ctor_get(v_x_4758_, 2);
                    lean_inc(v_tail_4760_);
                    lean_dec_ref_known(v_x_4758_, 3);
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
    mut v_as_4763_: *mut LeanObject,
    mut v_i_4764_: usize,
    mut v_stop_4765_: usize,
    mut v_b_4766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4767_: u8 = 0;
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: usize = 0;
    let mut v___x_4771_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4767_ = lean_usize_dec_eq(v_i_4764_, v_stop_4765_);
                if v___x_4767_ == 0 {
                    v___x_4768_ = lean_array_uget_borrowed(v_as_4763_, v_i_4764_);
                    lean_inc(v___x_4768_);
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
    mut v_as_4773_: *mut LeanObject,
    mut v_i_4774_: *mut LeanObject,
    mut v_stop_4775_: *mut LeanObject,
    mut v_b_4776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4777_: usize = 0;
    let mut v_stop_boxed_4778_: usize = 0;
    let mut v_res_4779_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4777_ = lean_unbox_usize(v_i_4774_);
    lean_dec(v_i_4774_);
    v_stop_boxed_4778_ = lean_unbox_usize(v_stop_4775_);
    lean_dec(v_stop_4775_);
    v_res_4779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(v_as_4773_, v_i_boxed_4777_, v_stop_boxed_4778_, v_b_4776_);
    lean_dec_ref(v_as_4773_);
    return v_res_4779_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8(
    mut v_sz_4780_: usize,
    mut v_i_4781_: usize,
    mut v_bs_4782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4783_: u8 = 0;
    let mut v_v_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: usize = 0;
    let mut v___x_4789_: usize = 0;
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4783_ = lean_usize_dec_lt(v_i_4781_, v_sz_4780_);
                if v___x_4783_ == 0 {
                    return v_bs_4782_;
                } else {
                    v_v_4784_ = lean_array_uget(v_bs_4782_, v_i_4781_);
                    v___x_4785_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4786_ = lean_array_uset(v_bs_4782_, v_i_4781_, v___x_4785_);
                    v___x_4787_ = l_Lean_Expr_fvarId_x21(v_v_4784_);
                    lean_dec(v_v_4784_);
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
    mut v_sz_4792_: *mut LeanObject,
    mut v_i_4793_: *mut LeanObject,
    mut v_bs_4794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4795_: usize = 0;
    let mut v_i_boxed_4796_: usize = 0;
    let mut v_res_4797_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4795_ = lean_unbox_usize(v_sz_4792_);
    lean_dec(v_sz_4792_);
    v_i_boxed_4796_ = lean_unbox_usize(v_i_4793_);
    lean_dec(v_i_4793_);
    v_res_4797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_boxed_4795_, v_i_boxed_4796_, v_bs_4794_);
    return v_res_4797_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(
    mut v_x_4798_: *mut LeanObject,
    mut v_x_4799_: *mut LeanObject,
    mut v_x_4800_: *mut LeanObject,
    mut v_x_4801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4806_: u8 = 0;
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: u8 = 0;
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: u8 = 0;
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4802_ = lean_ctor_get(v_x_4798_, 0);
                v_vs_4803_ = lean_ctor_get(v_x_4798_, 1);
                v_isSharedCheck_4827_ = (!lean_is_exclusive(v_x_4798_)) as u8;
                if v_isSharedCheck_4827_ == 0 {
                    v___x_4805_ = v_x_4798_;
                    v_isShared_4806_ = v_isSharedCheck_4827_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_4803_);
                    lean_inc(v_ks_4802_);
                    lean_dec(v_x_4798_);
                    v___x_4805_ = lean_box(0);
                    v_isShared_4806_ = v_isSharedCheck_4827_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4807_ = lean_array_get_size(v_ks_4802_);
                v___x_4808_ = lean_nat_dec_lt(v_x_4799_, v___x_4807_);
                if v___x_4808_ == 0 {
                    lean_dec(v_x_4799_);
                    v___x_4809_ = lean_array_push(v_ks_4802_, v_x_4800_);
                    v___x_4810_ = lean_array_push(v_vs_4803_, v_x_4801_);
                    if v_isShared_4806_ == 0 {
                        lean_ctor_set(v___x_4805_, 1, v___x_4810_);
                        lean_ctor_set(v___x_4805_, 0, v___x_4809_);
                        v___x_4812_ = v___x_4805_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4809_);
                        lean_ctor_set(v_reuseFailAlloc_4813_, 1, v___x_4810_);
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
                            v_reuseFailAlloc_4821_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4821_, 0, v_ks_4802_);
                            lean_ctor_set(v_reuseFailAlloc_4821_, 1, v_vs_4803_);
                            v___x_4817_ = v_reuseFailAlloc_4821_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4822_ = lean_array_fset(v_ks_4802_, v_x_4799_, v_x_4800_);
                        v___x_4823_ = lean_array_fset(v_vs_4803_, v_x_4799_, v_x_4801_);
                        lean_dec(v_x_4799_);
                        if v_isShared_4806_ == 0 {
                            lean_ctor_set(v___x_4805_, 1, v___x_4823_);
                            lean_ctor_set(v___x_4805_, 0, v___x_4822_);
                            v___x_4825_ = v___x_4805_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4822_);
                            lean_ctor_set(v_reuseFailAlloc_4826_, 1, v___x_4823_);
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
                v___x_4818_ = lean_unsigned_to_nat(1);
                v___x_4819_ = lean_nat_add(v_x_4799_, v___x_4818_);
                lean_dec(v_x_4799_);
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
    mut v_n_4828_: *mut LeanObject,
    mut v_k_4829_: *mut LeanObject,
    mut v_v_4830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    v___x_4831_ = lean_unsigned_to_nat(0);
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
    v___x_4837_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__0);
    v___x_4838_ = lean_usize_sub(v___x_4837_, v___x_4836_);
    return v___x_4838_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    v___x_4839_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_4839_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(
    mut v_x_4840_: *mut LeanObject,
    mut v_x_4841_: usize,
    mut v_x_4842_: usize,
    mut v_x_4843_: *mut LeanObject,
    mut v_x_4844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: usize = 0;
    let mut v___x_4847_: usize = 0;
    let mut v___x_4848_: usize = 0;
    let mut v___x_4849_: usize = 0;
    let mut v_j_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: u8 = 0;
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v_v_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v___x_4870_: u8 = 0;
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4876_: u8 = 0;
    let mut v_node_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4880_: u8 = 0;
    let mut v___x_4881_: usize = 0;
    let mut v___x_4882_: usize = 0;
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4887_: u8 = 0;
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4889_: u8 = 0;
    let mut v_unused_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4895_: u8 = 0;
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: u8 = 0;
    let mut v_ks_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: usize = 0;
    let mut v___x_4907_: u8 = 0;
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: u8 = 0;
    let mut v_reuseFailAlloc_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4840_) == 0 {
                    v_es_4845_ = lean_ctor_get(v_x_4840_, 0);
                    v___x_4846_ = 5usize;
                    v___x_4847_ = 1usize;
                    v___x_4848_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__1);
                    v___x_4849_ = lean_usize_land(v_x_4841_, v___x_4848_);
                    v_j_4850_ = lean_usize_to_nat(v___x_4849_);
                    v___x_4851_ = lean_array_get_size(v_es_4845_);
                    v___x_4852_ = lean_nat_dec_lt(v_j_4850_, v___x_4851_);
                    if v___x_4852_ == 0 {
                        lean_dec(v_j_4850_);
                        lean_dec(v_x_4844_);
                        lean_dec(v_x_4843_);
                        return v_x_4840_;
                    } else {
                        lean_inc_ref(v_es_4845_);
                        v_isSharedCheck_4889_ = (!lean_is_exclusive(v_x_4840_)) as u8;
                        if v_isSharedCheck_4889_ == 0 {
                            v_unused_4890_ = lean_ctor_get(v_x_4840_, 0);
                            lean_dec(v_unused_4890_);
                            v___x_4854_ = v_x_4840_;
                            v_isShared_4855_ = v_isSharedCheck_4889_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_4840_);
                            v___x_4854_ = lean_box(0);
                            v_isShared_4855_ = v_isSharedCheck_4889_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4891_ = lean_ctor_get(v_x_4840_, 0);
                    v_vs_4892_ = lean_ctor_get(v_x_4840_, 1);
                    v_isSharedCheck_4912_ = (!lean_is_exclusive(v_x_4840_)) as u8;
                    if v_isSharedCheck_4912_ == 0 {
                        v___x_4894_ = v_x_4840_;
                        v_isShared_4895_ = v_isSharedCheck_4912_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_4892_);
                        lean_inc(v_ks_4891_);
                        lean_dec(v_x_4840_);
                        v___x_4894_ = lean_box(0);
                        v_isShared_4895_ = v_isSharedCheck_4912_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4856_ = lean_array_fget(v_es_4845_, v_j_4850_);
                v___x_4857_ = lean_box(0);
                v_xs_x27_4858_ = lean_array_fset(v_es_4845_, v_j_4850_, v___x_4857_);
                match lean_obj_tag(v_v_4856_) {
                    0 => {
                        v_key_4865_ = lean_ctor_get(v_v_4856_, 0);
                        v_val_4866_ = lean_ctor_get(v_v_4856_, 1);
                        v_isSharedCheck_4876_ = (!lean_is_exclusive(v_v_4856_)) as u8;
                        if v_isSharedCheck_4876_ == 0 {
                            v___x_4868_ = v_v_4856_;
                            v_isShared_4869_ = v_isSharedCheck_4876_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_4866_);
                            lean_inc(v_key_4865_);
                            lean_dec(v_v_4856_);
                            v___x_4868_ = lean_box(0);
                            v_isShared_4869_ = v_isSharedCheck_4876_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4877_ = lean_ctor_get(v_v_4856_, 0);
                        v_isSharedCheck_4887_ = (!lean_is_exclusive(v_v_4856_)) as u8;
                        if v_isSharedCheck_4887_ == 0 {
                            v___x_4879_ = v_v_4856_;
                            v_isShared_4880_ = v_isSharedCheck_4887_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_4877_);
                            lean_dec(v_v_4856_);
                            v___x_4879_ = lean_box(0);
                            v_isShared_4880_ = v_isSharedCheck_4887_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4888_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4888_, 0, v_x_4843_);
                        lean_ctor_set(v___x_4888_, 1, v_x_4844_);
                        v___y_4860_ = v___x_4888_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4861_ = lean_array_fset(v_xs_x27_4858_, v_j_4850_, v___y_4860_);
                lean_dec(v_j_4850_);
                if v_isShared_4855_ == 0 {
                    lean_ctor_set(v___x_4854_, 0, v___x_4861_);
                    v___x_4863_ = v___x_4854_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4864_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4864_, 0, v___x_4861_);
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
                    lean_del_object(v___x_4868_);
                    v___x_4871_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4865_,
                        v_val_4866_,
                        v_x_4843_,
                        v_x_4844_,
                    );
                    v___x_4872_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4872_, 0, v___x_4871_);
                    v___y_4860_ = v___x_4872_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_4866_);
                    lean_dec(v_key_4865_);
                    if v_isShared_4869_ == 0 {
                        lean_ctor_set(v___x_4868_, 1, v_x_4844_);
                        lean_ctor_set(v___x_4868_, 0, v_x_4843_);
                        v___x_4874_ = v___x_4868_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4875_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4875_, 0, v_x_4843_);
                        lean_ctor_set(v_reuseFailAlloc_4875_, 1, v_x_4844_);
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
                    lean_ctor_set(v___x_4879_, 0, v___x_4883_);
                    v___x_4885_ = v___x_4879_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4886_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4886_, 0, v___x_4883_);
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
                    v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_ks_4891_);
                    lean_ctor_set(v_reuseFailAlloc_4911_, 1, v_vs_4892_);
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
                    v___x_4909_ = lean_unsigned_to_nat(4);
                    v___x_4910_ = lean_nat_dec_lt(v___x_4908_, v___x_4909_);
                    lean_dec(v___x_4908_);
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
                    v_ks_4901_ = lean_ctor_get(v_newNode_4898_, 0);
                    lean_inc_ref(v_ks_4901_);
                    v_vs_4902_ = lean_ctor_get(v_newNode_4898_, 1);
                    lean_inc_ref(v_vs_4902_);
                    lean_dec_ref(v_newNode_4898_);
                    v___x_4903_ = lean_unsigned_to_nat(0);
                    v___x_4904_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___closed__2);
                    v___x_4905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_x_4842_, v_ks_4901_, v_vs_4902_, v___x_4903_, v___x_4904_);
                    lean_dec_ref(v_vs_4902_);
                    lean_dec_ref(v_ks_4901_);
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
    mut v_keys_4914_: *mut LeanObject,
    mut v_vals_4915_: *mut LeanObject,
    mut v_i_4916_: *mut LeanObject,
    mut v_entries_4917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: u8 = 0;
    let mut v_k_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: u64 = 0;
    let mut v_h_4923_: usize = 0;
    let mut v___x_4924_: usize = 0;
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: usize = 0;
    let mut v___x_4927_: usize = 0;
    let mut v___x_4928_: usize = 0;
    let mut v_h_4929_: usize = 0;
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4918_ = lean_array_get_size(v_keys_4914_);
                v___x_4919_ = lean_nat_dec_lt(v_i_4916_, v___x_4918_);
                if v___x_4919_ == 0 {
                    lean_dec(v_i_4916_);
                    return v_entries_4917_;
                } else {
                    v_k_4920_ = lean_array_fget_borrowed(v_keys_4914_, v_i_4916_);
                    v_v_4921_ = lean_array_fget_borrowed(v_vals_4915_, v_i_4916_);
                    v___x_4922_ = l_Lean_instHashableMVarId_hash(v_k_4920_);
                    v_h_4923_ = lean_uint64_to_usize(v___x_4922_);
                    v___x_4924_ = 5usize;
                    v___x_4925_ = lean_unsigned_to_nat(1);
                    v___x_4926_ = 1usize;
                    v___x_4927_ = lean_usize_sub(v_depth_4913_, v___x_4926_);
                    v___x_4928_ = lean_usize_mul(v___x_4924_, v___x_4927_);
                    v_h_4929_ = lean_usize_shift_right(v_h_4923_, v___x_4928_);
                    v___x_4930_ = lean_nat_add(v_i_4916_, v___x_4925_);
                    lean_dec(v_i_4916_);
                    lean_inc(v_v_4921_);
                    lean_inc(v_k_4920_);
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
    mut v_depth_4933_: *mut LeanObject,
    mut v_keys_4934_: *mut LeanObject,
    mut v_vals_4935_: *mut LeanObject,
    mut v_i_4936_: *mut LeanObject,
    mut v_entries_4937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4938_: usize = 0;
    let mut v_res_4939_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4938_ = lean_unbox_usize(v_depth_4933_);
    lean_dec(v_depth_4933_);
    v_res_4939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_boxed_4938_, v_keys_4934_, v_vals_4935_, v_i_4936_, v_entries_4937_);
    lean_dec_ref(v_vals_4935_);
    lean_dec_ref(v_keys_4934_);
    return v_res_4939_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg___boxed(
    mut v_x_4940_: *mut LeanObject,
    mut v_x_4941_: *mut LeanObject,
    mut v_x_4942_: *mut LeanObject,
    mut v_x_4943_: *mut LeanObject,
    mut v_x_4944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_22252__boxed_4945_: usize = 0;
    let mut v_x_22253__boxed_4946_: usize = 0;
    let mut v_res_4947_: *mut LeanObject = core::ptr::null_mut();
    v_x_22252__boxed_4945_ = lean_unbox_usize(v_x_4941_);
    lean_dec(v_x_4941_);
    v_x_22253__boxed_4946_ = lean_unbox_usize(v_x_4942_);
    lean_dec(v_x_4942_);
    v_res_4947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_4940_, v_x_22252__boxed_4945_, v_x_22253__boxed_4946_, v_x_4943_, v_x_4944_);
    return v_res_4947_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(
    mut v_x_4948_: *mut LeanObject,
    mut v_x_4949_: *mut LeanObject,
    mut v_x_4950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4951_: u64 = 0;
    let mut v___x_4952_: usize = 0;
    let mut v___x_4953_: usize = 0;
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    v___x_4951_ = l_Lean_instHashableMVarId_hash(v_x_4949_);
    v___x_4952_ = lean_uint64_to_usize(v___x_4951_);
    v___x_4953_ = 1usize;
    v___x_4954_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_4948_, v___x_4952_, v___x_4953_, v_x_4949_, v_x_4950_);
    return v___x_4954_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(
    mut v_mvarId_4955_: *mut LeanObject,
    mut v_val_4956_: *mut LeanObject,
    mut v___y_4957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4967_: u8 = 0;
    let mut v_depth_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4991_: u8 = 0;
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4959_ = lean_st_ref_take(v___y_4957_);
                v_mctx_4960_ = lean_ctor_get(v___x_4959_, 0);
                v_cache_4961_ = lean_ctor_get(v___x_4959_, 1);
                v_zetaDeltaFVarIds_4962_ = lean_ctor_get(v___x_4959_, 2);
                v_postponed_4963_ = lean_ctor_get(v___x_4959_, 3);
                v_diag_4964_ = lean_ctor_get(v___x_4959_, 4);
                v_isSharedCheck_4992_ = (!lean_is_exclusive(v___x_4959_)) as u8;
                if v_isSharedCheck_4992_ == 0 {
                    v___x_4966_ = v___x_4959_;
                    v_isShared_4967_ = v_isSharedCheck_4992_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_4964_);
                    lean_inc(v_postponed_4963_);
                    lean_inc(v_zetaDeltaFVarIds_4962_);
                    lean_inc(v_cache_4961_);
                    lean_inc(v_mctx_4960_);
                    lean_dec(v___x_4959_);
                    v___x_4966_ = lean_box(0);
                    v_isShared_4967_ = v_isSharedCheck_4992_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4968_ = lean_ctor_get(v_mctx_4960_, 0);
                v_levelAssignDepth_4969_ = lean_ctor_get(v_mctx_4960_, 1);
                v_lmvarCounter_4970_ = lean_ctor_get(v_mctx_4960_, 2);
                v_mvarCounter_4971_ = lean_ctor_get(v_mctx_4960_, 3);
                v_lDecls_4972_ = lean_ctor_get(v_mctx_4960_, 4);
                v_decls_4973_ = lean_ctor_get(v_mctx_4960_, 5);
                v_userNames_4974_ = lean_ctor_get(v_mctx_4960_, 6);
                v_lAssignment_4975_ = lean_ctor_get(v_mctx_4960_, 7);
                v_eAssignment_4976_ = lean_ctor_get(v_mctx_4960_, 8);
                v_dAssignment_4977_ = lean_ctor_get(v_mctx_4960_, 9);
                v_isSharedCheck_4991_ = (!lean_is_exclusive(v_mctx_4960_)) as u8;
                if v_isSharedCheck_4991_ == 0 {
                    v___x_4979_ = v_mctx_4960_;
                    v_isShared_4980_ = v_isSharedCheck_4991_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_4977_);
                    lean_inc(v_eAssignment_4976_);
                    lean_inc(v_lAssignment_4975_);
                    lean_inc(v_userNames_4974_);
                    lean_inc(v_decls_4973_);
                    lean_inc(v_lDecls_4972_);
                    lean_inc(v_mvarCounter_4971_);
                    lean_inc(v_lmvarCounter_4970_);
                    lean_inc(v_levelAssignDepth_4969_);
                    lean_inc(v_depth_4968_);
                    lean_dec(v_mctx_4960_);
                    v___x_4979_ = lean_box(0);
                    v_isShared_4980_ = v_isSharedCheck_4991_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4981_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_eAssignment_4976_, v_mvarId_4955_, v_val_4956_);
                if v_isShared_4980_ == 0 {
                    lean_ctor_set(v___x_4979_, 8, v___x_4981_);
                    v___x_4983_ = v___x_4979_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_depth_4968_);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 1, v_levelAssignDepth_4969_);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 2, v_lmvarCounter_4970_);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 3, v_mvarCounter_4971_);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 4, v_lDecls_4972_);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 5, v_decls_4973_);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 6, v_userNames_4974_);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 7, v_lAssignment_4975_);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 8, v___x_4981_);
                    lean_ctor_set(v_reuseFailAlloc_4990_, 9, v_dAssignment_4977_);
                    v___x_4983_ = v_reuseFailAlloc_4990_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4967_ == 0 {
                    lean_ctor_set(v___x_4966_, 0, v___x_4983_);
                    v___x_4985_ = v___x_4966_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4983_);
                    lean_ctor_set(v_reuseFailAlloc_4989_, 1, v_cache_4961_);
                    lean_ctor_set(v_reuseFailAlloc_4989_, 2, v_zetaDeltaFVarIds_4962_);
                    lean_ctor_set(v_reuseFailAlloc_4989_, 3, v_postponed_4963_);
                    lean_ctor_set(v_reuseFailAlloc_4989_, 4, v_diag_4964_);
                    v___x_4985_ = v_reuseFailAlloc_4989_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4986_ = lean_st_ref_set(v___y_4957_, v___x_4985_);
                v___x_4987_ = lean_box(0);
                v___x_4988_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4988_, 0, v___x_4987_);
                return v___x_4988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg___boxed(
    mut v_mvarId_4993_: *mut LeanObject,
    mut v_val_4994_: *mut LeanObject,
    mut v___y_4995_: *mut LeanObject,
    mut v___y_4996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4997_: *mut LeanObject = core::ptr::null_mut();
    v_res_4997_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_4993_, v_val_4994_, v___y_4995_);
    lean_dec(v___y_4995_);
    return v_res_4997_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4()
-> *mut LeanObject {
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    v___x_5004_ = lean_box(0);
    v___x_5005_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__3;
    v___x_5006_ = l_Lean_mkConst(v___x_5005_, v___x_5004_);
    return v___x_5006_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7()
-> *mut LeanObject {
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    v___x_5011_ = lean_unsigned_to_nat(0);
    v___x_5012_ = l_Lean_Level_ofNat(v___x_5011_);
    return v___x_5012_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8()
-> *mut LeanObject {
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    v___x_5013_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__12);
    v___x_5014_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__7);
    v___x_5015_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5015_, 0, v___x_5014_);
    lean_ctor_set(v___x_5015_, 1, v___x_5013_);
    return v___x_5015_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9()
-> *mut LeanObject {
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    v___x_5016_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__8);
    v___x_5017_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__6;
    v___x_5018_ = l_Lean_mkConst(v___x_5017_, v___x_5016_);
    return v___x_5018_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10()
-> *mut LeanObject {
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    v___x_5019_ = lean_box(0);
    v___x_5020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq_spec__1___closed__6;
    v___x_5021_ = l_Lean_mkConst(v___x_5020_, v___x_5019_);
    return v___x_5021_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11()
-> *mut LeanObject {
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    v___x_5022_ = lean_box(0);
    v___x_5023_ = lean_unsigned_to_nat(16);
    v___x_5024_ = lean_mk_array(v___x_5023_, v___x_5022_);
    return v___x_5024_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12()
-> *mut LeanObject {
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    v___x_5025_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__11);
    v___x_5026_ = lean_unsigned_to_nat(0);
    v___x_5027_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5027_, 0, v___x_5026_);
    lean_ctor_set(v___x_5027_, 1, v___x_5025_);
    return v___x_5027_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14()
-> *mut LeanObject {
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    v___x_5029_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__13;
    v___x_5030_ = l_Lean_stringToMessageData(v___x_5029_);
    return v___x_5030_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4(
    mut v_fst_5031_: *mut LeanObject,
    mut v_snd_5032_: *mut LeanObject,
    mut v_goal_5033_: *mut LeanObject,
    mut v___y_5034_: *mut LeanObject,
    mut v___y_5035_: *mut LeanObject,
    mut v___y_5036_: *mut LeanObject,
    mut v___y_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5041_: u8 = 0;
    let mut v___y_5042_: usize = 0;
    let mut v___y_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5045_: usize = 0;
    let mut v_a_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: u8 = 0;
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5077_: usize = 0;
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: u8 = 0;
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5090_: u8 = 0;
    let mut v_snd_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5095_: u8 = 0;
    let mut v_a_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5099_: u8 = 0;
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5103_: u8 = 0;
    let mut v_a_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5107_: u8 = 0;
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5111_: u8 = 0;
    let mut v_a_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5119_: u8 = 0;
    let mut v_a_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5123_: u8 = 0;
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5127_: u8 = 0;
    let mut v_a_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5131_: u8 = 0;
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5135_: u8 = 0;
    let mut v___y_5137_: usize = 0;
    let mut v___y_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: u8 = 0;
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5165_: u8 = 0;
    let mut v___x_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5179_: u8 = 0;
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5184_: u8 = 0;
    let mut v_unused_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut v_unused_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5215_: u8 = 0;
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5224_: u8 = 0;
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5228_: u8 = 0;
    let mut v_reuseFailAlloc_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5230_: u8 = 0;
    let mut v_unused_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5234_: u8 = 0;
    let mut v_unused_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5243_: usize = 0;
    let mut v___x_5244_: usize = 0;
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: u8 = 0;
    let mut v___x_5250_: u8 = 0;
    let mut v___x_5251_: usize = 0;
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: usize = 0;
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: u8 = 0;
    let mut v___x_5262_: u8 = 0;
    let mut v___x_5263_: usize = 0;
    let mut v___x_5264_: usize = 0;
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: usize = 0;
    let mut v___x_5267_: usize = 0;
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5236_ = lean_st_ref_get(v___y_5034_);
                v_relevantHyps_5255_ = lean_ctor_get(v___x_5236_, 1);
                lean_inc_ref(v_relevantHyps_5255_);
                lean_dec(v___x_5236_);
                v_size_5256_ = lean_ctor_get(v_relevantHyps_5255_, 0);
                lean_inc(v_size_5256_);
                v_buckets_5257_ = lean_ctor_get(v_relevantHyps_5255_, 1);
                lean_inc_ref(v_buckets_5257_);
                lean_dec_ref(v_relevantHyps_5255_);
                v___x_5258_ = lean_mk_empty_array_with_capacity(v_size_5256_);
                lean_dec(v_size_5256_);
                v___x_5259_ = lean_unsigned_to_nat(0);
                v___x_5260_ = lean_array_get_size(v_buckets_5257_);
                v___x_5261_ = lean_nat_dec_lt(v___x_5259_, v___x_5260_);
                if v___x_5261_ == 0 {
                    lean_dec_ref(v_buckets_5257_);
                    v___y_5238_ = v___x_5258_;
                    state = 25;
                    continue;
                } else {
                    v___x_5262_ = lean_nat_dec_le(v___x_5260_, v___x_5260_);
                    if v___x_5262_ == 0 {
                        if v___x_5261_ == 0 {
                            lean_dec_ref(v_buckets_5257_);
                            v___y_5238_ = v___x_5258_;
                            state = 25;
                            continue;
                        } else {
                            v___x_5263_ = 0usize;
                            v___x_5264_ = lean_usize_of_nat(v___x_5260_);
                            v___x_5265_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_5257_, v___x_5263_, v___x_5264_, v___x_5258_);
                            lean_dec_ref(v_buckets_5257_);
                            v___y_5238_ = v___x_5265_;
                            state = 25;
                            continue;
                        }
                    } else {
                        v___x_5266_ = 0usize;
                        v___x_5267_ = lean_usize_of_nat(v___x_5260_);
                        v___x_5268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__13(v_buckets_5257_, v___x_5266_, v___x_5267_, v___x_5258_);
                        lean_dec_ref(v_buckets_5257_);
                        v___y_5238_ = v___x_5268_;
                        state = 25;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5047_ = lean_ctor_get(v_a_5046_, 0);
                lean_inc(v_fst_5047_);
                v_snd_5048_ = lean_ctor_get(v_a_5046_, 1);
                lean_inc(v_snd_5048_);
                lean_dec_ref(v_a_5046_);
                v___x_5049_ = l_Lean_Expr_getAppFn(v_fst_5047_);
                lean_dec(v_fst_5047_);
                v___x_5050_ = l_Lean_Expr_mvarId_x21(v___x_5049_);
                lean_dec_ref(v___x_5049_);
                v___x_5051_ = l_Lean_MVarId_getType(
                    v___x_5050_,
                    v___y_5035_,
                    v___y_5036_,
                    v___y_5037_,
                    v___y_5038_,
                );
                if lean_obj_tag(v___x_5051_) == 0 {
                    v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
                    lean_inc(v_a_5052_);
                    lean_dec_ref_known(v___x_5051_, 1);
                    v___x_5053_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__1;
                    v___x_5054_ = lean_box(0);
                    v___x_5055_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__4);
                    v___x_5056_ = lean_box_usize(v___y_5042_);
                    v___x_5057_ = lean_box((v___y_5041_) as usize);
                    lean_inc(v_fst_5031_);
                    v___f_5058_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__3___boxed as *mut core::ffi::c_void, 14, 7);
                    lean_closure_set(v___f_5058_, 0, v___x_5054_);
                    lean_closure_set(v___f_5058_, 1, v___y_5043_);
                    lean_closure_set(v___f_5058_, 2, v___x_5056_);
                    lean_closure_set(v___f_5058_, 3, v_a_5052_);
                    lean_closure_set(v___f_5058_, 4, v___x_5057_);
                    lean_closure_set(v___f_5058_, 5, v_fst_5031_);
                    lean_closure_set(v___f_5058_, 6, v___x_5055_);
                    v___x_5059_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v___x_5053_, v___x_5055_, v___f_5058_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
                    if lean_obj_tag(v___x_5059_) == 0 {
                        v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
                        lean_inc(v_a_5060_);
                        lean_dec_ref_known(v___x_5059_, 1);
                        v_fst_5061_ = lean_ctor_get(v_a_5060_, 0);
                        lean_inc(v_fst_5061_);
                        v_snd_5062_ = lean_ctor_get(v_a_5060_, 1);
                        lean_inc(v_snd_5062_);
                        lean_dec(v_a_5060_);
                        v___x_5063_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5063_, 0, v_snd_5062_);
                        v___x_5064_ = 0;
                        v___x_5065_ = lean_box(0);
                        v___x_5066_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_5063_,
                            v___x_5064_,
                            v___x_5065_,
                            v___y_5035_,
                            v___y_5036_,
                            v___y_5037_,
                            v___y_5038_,
                        );
                        if lean_obj_tag(v___x_5066_) == 0 {
                            v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
                            lean_inc(v_a_5067_);
                            lean_dec_ref_known(v___x_5066_, 1);
                            v___x_5068_ = l_Lean_Expr_mvarId_x21(v_a_5067_);
                            lean_dec(v_a_5067_);
                            v___x_5069_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__9);
                            v___x_5070_ = l_Lean_mkNatLit(v_fst_5031_);
                            v___x_5071_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__10);
                            lean_inc(v___x_5068_);
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
                            lean_inc_ref(v___y_5044_);
                            v___x_5074_ = l_Array_append___redArg(v___y_5044_, v_snd_5048_);
                            v___x_5075_ = l_Lean_mkAppN(v___x_5073_, v___x_5074_);
                            lean_dec_ref(v___x_5074_);
                            v___x_5076_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_goal_5033_, v___x_5075_, v___y_5036_);
                            lean_dec_ref(v___x_5076_);
                            v_sz_5077_ = lean_array_size(v_snd_5048_);
                            lean_inc(v_snd_5048_);
                            v___x_5078_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__8(v_sz_5077_, v___y_5045_, v_snd_5048_);
                            v___x_5079_ = l_Lean_MVarId_tryClearMany_x27(
                                v___x_5068_,
                                v___x_5078_,
                                v___y_5035_,
                                v___y_5036_,
                                v___y_5037_,
                                v___y_5038_,
                            );
                            if lean_obj_tag(v___x_5079_) == 0 {
                                v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
                                lean_inc(v_a_5080_);
                                lean_dec_ref_known(v___x_5079_, 1);
                                v_fst_5081_ = lean_ctor_get(v_a_5080_, 0);
                                lean_inc(v_fst_5081_);
                                lean_dec(v_a_5080_);
                                v___x_5082_ = lean_array_get_size(v___y_5044_);
                                lean_dec_ref(v___y_5044_);
                                v___x_5083_ = lean_array_get_size(v_snd_5048_);
                                lean_dec(v_snd_5048_);
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
                                if lean_obj_tag(v___x_5086_) == 0 {
                                    v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
                                    v_isSharedCheck_5095_ = (!lean_is_exclusive(v___x_5086_)) as u8;
                                    if v_isSharedCheck_5095_ == 0 {
                                        v___x_5089_ = v___x_5086_;
                                        v_isShared_5090_ = v_isSharedCheck_5095_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5087_);
                                        lean_dec(v___x_5086_);
                                        v___x_5089_ = lean_box(0);
                                        v_isShared_5090_ = v_isSharedCheck_5095_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_a_5096_ = lean_ctor_get(v___x_5086_, 0);
                                    v_isSharedCheck_5103_ = (!lean_is_exclusive(v___x_5086_)) as u8;
                                    if v_isSharedCheck_5103_ == 0 {
                                        v___x_5098_ = v___x_5086_;
                                        v_isShared_5099_ = v_isSharedCheck_5103_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5096_);
                                        lean_dec(v___x_5086_);
                                        v___x_5098_ = lean_box(0);
                                        v_isShared_5099_ = v_isSharedCheck_5103_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_snd_5048_);
                                lean_dec_ref(v___y_5044_);
                                v_a_5104_ = lean_ctor_get(v___x_5079_, 0);
                                v_isSharedCheck_5111_ = (!lean_is_exclusive(v___x_5079_)) as u8;
                                if v_isSharedCheck_5111_ == 0 {
                                    v___x_5106_ = v___x_5079_;
                                    v_isShared_5107_ = v_isSharedCheck_5111_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_5104_);
                                    lean_dec(v___x_5079_);
                                    v___x_5106_ = lean_box(0);
                                    v_isShared_5107_ = v_isSharedCheck_5111_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_fst_5061_);
                            lean_dec(v_snd_5048_);
                            lean_dec_ref(v___y_5044_);
                            lean_dec(v_goal_5033_);
                            lean_dec_ref(v_snd_5032_);
                            lean_dec(v_fst_5031_);
                            v_a_5112_ = lean_ctor_get(v___x_5066_, 0);
                            v_isSharedCheck_5119_ = (!lean_is_exclusive(v___x_5066_)) as u8;
                            if v_isSharedCheck_5119_ == 0 {
                                v___x_5114_ = v___x_5066_;
                                v_isShared_5115_ = v_isSharedCheck_5119_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_5112_);
                                lean_dec(v___x_5066_);
                                v___x_5114_ = lean_box(0);
                                v_isShared_5115_ = v_isSharedCheck_5119_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_snd_5048_);
                        lean_dec_ref(v___y_5044_);
                        lean_dec(v_goal_5033_);
                        lean_dec_ref(v_snd_5032_);
                        lean_dec(v_fst_5031_);
                        v_a_5120_ = lean_ctor_get(v___x_5059_, 0);
                        v_isSharedCheck_5127_ = (!lean_is_exclusive(v___x_5059_)) as u8;
                        if v_isSharedCheck_5127_ == 0 {
                            v___x_5122_ = v___x_5059_;
                            v_isShared_5123_ = v_isSharedCheck_5127_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_5120_);
                            lean_dec(v___x_5059_);
                            v___x_5122_ = lean_box(0);
                            v_isShared_5123_ = v_isSharedCheck_5127_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_5048_);
                    lean_dec_ref(v___y_5044_);
                    lean_dec_ref(v___y_5043_);
                    lean_dec(v_goal_5033_);
                    lean_dec_ref(v_snd_5032_);
                    lean_dec(v_fst_5031_);
                    v_a_5128_ = lean_ctor_get(v___x_5051_, 0);
                    v_isSharedCheck_5135_ = (!lean_is_exclusive(v___x_5051_)) as u8;
                    if v_isSharedCheck_5135_ == 0 {
                        v___x_5130_ = v___x_5051_;
                        v_isShared_5131_ = v_isSharedCheck_5135_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_5128_);
                        lean_dec(v___x_5051_);
                        v___x_5130_ = lean_box(0);
                        v_isShared_5131_ = v_isSharedCheck_5135_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_5091_ = lean_ctor_get(v_a_5087_, 1);
                lean_inc(v_snd_5091_);
                lean_dec(v_a_5087_);
                if v_isShared_5090_ == 0 {
                    lean_ctor_set(v___x_5089_, 0, v_snd_5091_);
                    v___x_5093_ = v___x_5089_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5094_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_snd_5091_);
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
                    v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5096_);
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
                    v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
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
                    v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
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
                    v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5120_);
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
                    v_reuseFailAlloc_5134_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_a_5128_);
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
                v_lctx_5143_ = lean_ctor_get(v___y_5035_, 2);
                v_mctx_5144_ = lean_ctor_get(v___x_5140_, 0);
                lean_inc_ref(v_mctx_5144_);
                lean_dec(v___x_5140_);
                v_ngen_5145_ = lean_ctor_get(v___x_5141_, 2);
                lean_inc_ref(v_ngen_5145_);
                lean_dec(v___x_5141_);
                v_quotContext_5146_ = lean_ctor_get(v___y_5037_, 10);
                v_nextMacroScope_5147_ = lean_ctor_get(v___x_5142_, 1);
                lean_inc(v_nextMacroScope_5147_);
                lean_dec(v___x_5142_);
                v___x_5148_ = 1;
                lean_inc_ref(v_lctx_5143_);
                lean_inc(v_quotContext_5146_);
                v___x_5149_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5149_, 0, v_quotContext_5146_);
                lean_ctor_set(v___x_5149_, 1, v_lctx_5143_);
                v___x_5150_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
                v___x_5151_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_5151_, 0, v_mctx_5144_);
                lean_ctor_set(v___x_5151_, 1, v_nextMacroScope_5147_);
                lean_ctor_set(v___x_5151_, 2, v_ngen_5145_);
                lean_ctor_set(v___x_5151_, 3, v___x_5150_);
                lean_inc(v_goal_5033_);
                v___x_5152_ = l_Lean_MetavarContext_revert(
                    v___y_5138_,
                    v_goal_5033_,
                    v___x_5148_,
                    v___x_5149_,
                    v___x_5151_,
                );
                lean_dec_ref_known(v___x_5149_, 2);
                lean_dec_ref(v___y_5138_);
                if lean_obj_tag(v___x_5152_) == 0 {
                    v_a_5153_ = lean_ctor_get(v___x_5152_, 0);
                    lean_inc(v_a_5153_);
                    v_a_5154_ = lean_ctor_get(v___x_5152_, 1);
                    lean_inc(v_a_5154_);
                    lean_dec_ref_known(v___x_5152_, 2);
                    v___x_5155_ = lean_st_ref_take(v___y_5036_);
                    v_mctx_5156_ = lean_ctor_get(v_a_5154_, 0);
                    lean_inc_ref(v_mctx_5156_);
                    v_nextMacroScope_5157_ = lean_ctor_get(v_a_5154_, 1);
                    lean_inc(v_nextMacroScope_5157_);
                    v_ngen_5158_ = lean_ctor_get(v_a_5154_, 2);
                    lean_inc_ref(v_ngen_5158_);
                    lean_dec(v_a_5154_);
                    v_cache_5159_ = lean_ctor_get(v___x_5155_, 1);
                    v_zetaDeltaFVarIds_5160_ = lean_ctor_get(v___x_5155_, 2);
                    v_postponed_5161_ = lean_ctor_get(v___x_5155_, 3);
                    v_diag_5162_ = lean_ctor_get(v___x_5155_, 4);
                    v_isSharedCheck_5188_ = (!lean_is_exclusive(v___x_5155_)) as u8;
                    if v_isSharedCheck_5188_ == 0 {
                        v_unused_5189_ = lean_ctor_get(v___x_5155_, 0);
                        lean_dec(v_unused_5189_);
                        v___x_5164_ = v___x_5155_;
                        v_isShared_5165_ = v_isSharedCheck_5188_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_diag_5162_);
                        lean_inc(v_postponed_5161_);
                        lean_inc(v_zetaDeltaFVarIds_5160_);
                        lean_inc(v_cache_5159_);
                        lean_dec(v___x_5155_);
                        v___x_5164_ = lean_box(0);
                        v_isShared_5165_ = v_isSharedCheck_5188_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_5139_);
                    lean_dec(v_goal_5033_);
                    lean_dec_ref(v_snd_5032_);
                    lean_dec(v_fst_5031_);
                    v_a_5190_ = lean_ctor_get(v___x_5152_, 1);
                    lean_inc(v_a_5190_);
                    lean_dec_ref_known(v___x_5152_, 2);
                    v___x_5191_ = lean_st_ref_take(v___y_5036_);
                    v_mctx_5192_ = lean_ctor_get(v_a_5190_, 0);
                    lean_inc_ref(v_mctx_5192_);
                    v_nextMacroScope_5193_ = lean_ctor_get(v_a_5190_, 1);
                    lean_inc(v_nextMacroScope_5193_);
                    v_ngen_5194_ = lean_ctor_get(v_a_5190_, 2);
                    lean_inc_ref(v_ngen_5194_);
                    lean_dec(v_a_5190_);
                    v_cache_5195_ = lean_ctor_get(v___x_5191_, 1);
                    v_zetaDeltaFVarIds_5196_ = lean_ctor_get(v___x_5191_, 2);
                    v_postponed_5197_ = lean_ctor_get(v___x_5191_, 3);
                    v_diag_5198_ = lean_ctor_get(v___x_5191_, 4);
                    v_isSharedCheck_5234_ = (!lean_is_exclusive(v___x_5191_)) as u8;
                    if v_isSharedCheck_5234_ == 0 {
                        v_unused_5235_ = lean_ctor_get(v___x_5191_, 0);
                        lean_dec(v_unused_5235_);
                        v___x_5200_ = v___x_5191_;
                        v_isShared_5201_ = v_isSharedCheck_5234_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_diag_5198_);
                        lean_inc(v_postponed_5197_);
                        lean_inc(v_zetaDeltaFVarIds_5196_);
                        lean_inc(v_cache_5195_);
                        lean_dec(v___x_5191_);
                        v___x_5200_ = lean_box(0);
                        v_isShared_5201_ = v_isSharedCheck_5234_;
                        state = 19;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_5165_ == 0 {
                    lean_ctor_set(v___x_5164_, 0, v_mctx_5156_);
                    v___x_5167_ = v___x_5164_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5187_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_mctx_5156_);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 1, v_cache_5159_);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 2, v_zetaDeltaFVarIds_5160_);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 3, v_postponed_5161_);
                    lean_ctor_set(v_reuseFailAlloc_5187_, 4, v_diag_5162_);
                    v___x_5167_ = v_reuseFailAlloc_5187_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_5168_ = lean_st_ref_set(v___y_5036_, v___x_5167_);
                v___x_5169_ = lean_st_ref_take(v___y_5038_);
                v_env_5170_ = lean_ctor_get(v___x_5169_, 0);
                v_auxDeclNGen_5171_ = lean_ctor_get(v___x_5169_, 3);
                v_traceState_5172_ = lean_ctor_get(v___x_5169_, 4);
                v_cache_5173_ = lean_ctor_get(v___x_5169_, 5);
                v_messages_5174_ = lean_ctor_get(v___x_5169_, 6);
                v_infoState_5175_ = lean_ctor_get(v___x_5169_, 7);
                v_snapshotTasks_5176_ = lean_ctor_get(v___x_5169_, 8);
                v_isSharedCheck_5184_ = (!lean_is_exclusive(v___x_5169_)) as u8;
                if v_isSharedCheck_5184_ == 0 {
                    v_unused_5185_ = lean_ctor_get(v___x_5169_, 2);
                    lean_dec(v_unused_5185_);
                    v_unused_5186_ = lean_ctor_get(v___x_5169_, 1);
                    lean_dec(v_unused_5186_);
                    v___x_5178_ = v___x_5169_;
                    v_isShared_5179_ = v_isSharedCheck_5184_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5176_);
                    lean_inc(v_infoState_5175_);
                    lean_inc(v_messages_5174_);
                    lean_inc(v_cache_5173_);
                    lean_inc(v_traceState_5172_);
                    lean_inc(v_auxDeclNGen_5171_);
                    lean_inc(v_env_5170_);
                    lean_dec(v___x_5169_);
                    v___x_5178_ = lean_box(0);
                    v_isShared_5179_ = v_isSharedCheck_5184_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_5179_ == 0 {
                    lean_ctor_set(v___x_5178_, 2, v_ngen_5158_);
                    lean_ctor_set(v___x_5178_, 1, v_nextMacroScope_5157_);
                    v___x_5181_ = v___x_5178_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5183_, 0, v_env_5170_);
                    lean_ctor_set(v_reuseFailAlloc_5183_, 1, v_nextMacroScope_5157_);
                    lean_ctor_set(v_reuseFailAlloc_5183_, 2, v_ngen_5158_);
                    lean_ctor_set(v_reuseFailAlloc_5183_, 3, v_auxDeclNGen_5171_);
                    lean_ctor_set(v_reuseFailAlloc_5183_, 4, v_traceState_5172_);
                    lean_ctor_set(v_reuseFailAlloc_5183_, 5, v_cache_5173_);
                    lean_ctor_set(v_reuseFailAlloc_5183_, 6, v_messages_5174_);
                    lean_ctor_set(v_reuseFailAlloc_5183_, 7, v_infoState_5175_);
                    lean_ctor_set(v_reuseFailAlloc_5183_, 8, v_snapshotTasks_5176_);
                    v___x_5181_ = v_reuseFailAlloc_5183_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_5182_ = lean_st_ref_set(v___y_5038_, v___x_5181_);
                lean_inc_ref(v___y_5139_);
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
                    lean_ctor_set(v___x_5200_, 0, v_mctx_5192_);
                    v___x_5203_ = v___x_5200_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5233_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5233_, 0, v_mctx_5192_);
                    lean_ctor_set(v_reuseFailAlloc_5233_, 1, v_cache_5195_);
                    lean_ctor_set(v_reuseFailAlloc_5233_, 2, v_zetaDeltaFVarIds_5196_);
                    lean_ctor_set(v_reuseFailAlloc_5233_, 3, v_postponed_5197_);
                    lean_ctor_set(v_reuseFailAlloc_5233_, 4, v_diag_5198_);
                    v___x_5203_ = v_reuseFailAlloc_5233_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_5204_ = lean_st_ref_set(v___y_5036_, v___x_5203_);
                v___x_5205_ = lean_st_ref_take(v___y_5038_);
                v_env_5206_ = lean_ctor_get(v___x_5205_, 0);
                v_auxDeclNGen_5207_ = lean_ctor_get(v___x_5205_, 3);
                v_traceState_5208_ = lean_ctor_get(v___x_5205_, 4);
                v_cache_5209_ = lean_ctor_get(v___x_5205_, 5);
                v_messages_5210_ = lean_ctor_get(v___x_5205_, 6);
                v_infoState_5211_ = lean_ctor_get(v___x_5205_, 7);
                v_snapshotTasks_5212_ = lean_ctor_get(v___x_5205_, 8);
                v_isSharedCheck_5230_ = (!lean_is_exclusive(v___x_5205_)) as u8;
                if v_isSharedCheck_5230_ == 0 {
                    v_unused_5231_ = lean_ctor_get(v___x_5205_, 2);
                    lean_dec(v_unused_5231_);
                    v_unused_5232_ = lean_ctor_get(v___x_5205_, 1);
                    lean_dec(v_unused_5232_);
                    v___x_5214_ = v___x_5205_;
                    v_isShared_5215_ = v_isSharedCheck_5230_;
                    state = 21;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5212_);
                    lean_inc(v_infoState_5211_);
                    lean_inc(v_messages_5210_);
                    lean_inc(v_cache_5209_);
                    lean_inc(v_traceState_5208_);
                    lean_inc(v_auxDeclNGen_5207_);
                    lean_inc(v_env_5206_);
                    lean_dec(v___x_5205_);
                    v___x_5214_ = lean_box(0);
                    v_isShared_5215_ = v_isSharedCheck_5230_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_5215_ == 0 {
                    lean_ctor_set(v___x_5214_, 2, v_ngen_5194_);
                    lean_ctor_set(v___x_5214_, 1, v_nextMacroScope_5193_);
                    v___x_5217_ = v___x_5214_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5229_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_env_5206_);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 1, v_nextMacroScope_5193_);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 2, v_ngen_5194_);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 3, v_auxDeclNGen_5207_);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 4, v_traceState_5208_);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 5, v_cache_5209_);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 6, v_messages_5210_);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 7, v_infoState_5211_);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 8, v_snapshotTasks_5212_);
                    v___x_5217_ = v_reuseFailAlloc_5229_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_5218_ = lean_st_ref_set(v___y_5038_, v___x_5217_);
                v___x_5219_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__14);
                v___x_5220_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v___x_5219_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
                v_a_5221_ = lean_ctor_get(v___x_5220_, 0);
                v_isSharedCheck_5228_ = (!lean_is_exclusive(v___x_5220_)) as u8;
                if v_isSharedCheck_5228_ == 0 {
                    v___x_5223_ = v___x_5220_;
                    v_isShared_5224_ = v_isSharedCheck_5228_;
                    state = 23;
                    continue;
                } else {
                    lean_inc(v_a_5221_);
                    lean_dec(v___x_5220_);
                    v___x_5223_ = lean_box(0);
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
                    v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
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
                v_relevantTerms_5240_ = lean_ctor_get(v___x_5239_, 0);
                lean_inc_ref(v_relevantTerms_5240_);
                lean_dec(v___x_5239_);
                v_size_5241_ = lean_ctor_get(v_relevantTerms_5240_, 0);
                lean_inc(v_size_5241_);
                v_buckets_5242_ = lean_ctor_get(v_relevantTerms_5240_, 1);
                lean_inc_ref(v_buckets_5242_);
                lean_dec_ref(v_relevantTerms_5240_);
                v_sz_5243_ = lean_array_size(v___y_5238_);
                v___x_5244_ = 0usize;
                v___x_5245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__1(v_sz_5243_, v___x_5244_, v___y_5238_);
                v___x_5246_ = lean_mk_empty_array_with_capacity(v_size_5241_);
                lean_dec(v_size_5241_);
                v___x_5247_ = lean_unsigned_to_nat(0);
                v___x_5248_ = lean_array_get_size(v_buckets_5242_);
                v___x_5249_ = lean_nat_dec_lt(v___x_5247_, v___x_5248_);
                if v___x_5249_ == 0 {
                    lean_dec_ref(v_buckets_5242_);
                    v___y_5137_ = v___x_5244_;
                    v___y_5138_ = v___x_5245_;
                    v___y_5139_ = v___x_5246_;
                    state = 14;
                    continue;
                } else {
                    v___x_5250_ = lean_nat_dec_le(v___x_5248_, v___x_5248_);
                    if v___x_5250_ == 0 {
                        if v___x_5249_ == 0 {
                            lean_dec_ref(v_buckets_5242_);
                            v___y_5137_ = v___x_5244_;
                            v___y_5138_ = v___x_5245_;
                            v___y_5139_ = v___x_5246_;
                            state = 14;
                            continue;
                        } else {
                            v___x_5251_ = lean_usize_of_nat(v___x_5248_);
                            v___x_5252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_5242_, v___x_5244_, v___x_5251_, v___x_5246_);
                            lean_dec_ref(v_buckets_5242_);
                            v___y_5137_ = v___x_5244_;
                            v___y_5138_ = v___x_5245_;
                            v___y_5139_ = v___x_5252_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___x_5253_ = lean_usize_of_nat(v___x_5248_);
                        v___x_5254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__11(v_buckets_5242_, v___x_5244_, v___x_5253_, v___x_5246_);
                        lean_dec_ref(v_buckets_5242_);
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
    mut v_fst_5269_: *mut LeanObject,
    mut v_snd_5270_: *mut LeanObject,
    mut v_goal_5271_: *mut LeanObject,
    mut v___y_5272_: *mut LeanObject,
    mut v___y_5273_: *mut LeanObject,
    mut v___y_5274_: *mut LeanObject,
    mut v___y_5275_: *mut LeanObject,
    mut v___y_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5278_: *mut LeanObject = core::ptr::null_mut();
    v_res_5278_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4(v_fst_5269_, v_snd_5270_, v_goal_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_);
    lean_dec(v___y_5276_);
    lean_dec_ref(v___y_5275_);
    lean_dec(v___y_5274_);
    lean_dec_ref(v___y_5273_);
    lean_dec(v___y_5272_);
    return v_res_5278_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(
    mut v___y_5287_: u8,
    mut v_suppressElabErrors_5288_: u8,
    mut v_x_5289_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_5289_) == 1 {
        let mut v_pre_5290_: *mut LeanObject = core::ptr::null_mut();
        v_pre_5290_ = lean_ctor_get(v_x_5289_, 0);
        match lean_obj_tag(v_pre_5290_) {
            1 => {
                let mut v_pre_5291_: *mut LeanObject = core::ptr::null_mut();
                v_pre_5291_ = lean_ctor_get(v_pre_5290_, 0);
                match lean_obj_tag(v_pre_5291_) {
                    0 => {
                        let mut v_str_5292_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_5293_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5295_: u8 = 0;
                        v_str_5292_ = lean_ctor_get(v_x_5289_, 1);
                        v_str_5293_ = lean_ctor_get(v_pre_5290_, 1);
                        v___x_5294_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__0;
                        v___x_5295_ = lean_string_dec_eq(v_str_5293_, v___x_5294_);
                        if v___x_5295_ == 0 {
                            let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_5297_: u8 = 0;
                            v___x_5296_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__1;
                            v___x_5297_ = lean_string_dec_eq(v_str_5293_, v___x_5296_);
                            if v___x_5297_ == 0 {
                                return v___y_5287_;
                            } else {
                                let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_5302_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_5302_ = lean_ctor_get(v_pre_5291_, 0);
                        if lean_obj_tag(v_pre_5302_) == 0 {
                            let mut v_str_5303_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_5304_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_5305_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_5307_: u8 = 0;
                            v_str_5303_ = lean_ctor_get(v_x_5289_, 1);
                            v_str_5304_ = lean_ctor_get(v_pre_5290_, 1);
                            v_str_5305_ = lean_ctor_get(v_pre_5291_, 1);
                            v___x_5306_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__4;
                            v___x_5307_ = lean_string_dec_eq(v_str_5305_, v___x_5306_);
                            if v___x_5307_ == 0 {
                                return v___y_5287_;
                            } else {
                                let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_5309_: u8 = 0;
                                v___x_5308_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___closed__5;
                                v___x_5309_ = lean_string_dec_eq(v_str_5304_, v___x_5308_);
                                if v___x_5309_ == 0 {
                                    return v___y_5287_;
                                } else {
                                    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_5312_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5314_: u8 = 0;
                v_str_5312_ = lean_ctor_get(v_x_5289_, 1);
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
    mut v___y_5315_: *mut LeanObject,
    mut v_suppressElabErrors_5316_: *mut LeanObject,
    mut v_x_5317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_23009__boxed_5318_: u8 = 0;
    let mut v_suppressElabErrors_boxed_5319_: u8 = 0;
    let mut v_res_5320_: u8 = 0;
    let mut v_r_5321_: *mut LeanObject = core::ptr::null_mut();
    v___y_23009__boxed_5318_ = (lean_unbox(v___y_5315_) as u8);
    v_suppressElabErrors_boxed_5319_ = (lean_unbox(v_suppressElabErrors_5316_) as u8);
    v_res_5320_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0(v___y_23009__boxed_5318_, v_suppressElabErrors_boxed_5319_, v_x_5317_);
    lean_dec(v_x_5317_);
    v_r_5321_ = lean_box((v_res_5320_) as usize);
    return v_r_5321_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(
    mut v_opts_5322_: *mut LeanObject,
    mut v_opt_5323_: *mut LeanObject,
) -> u8 {
    let mut v_name_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    v_name_5324_ = lean_ctor_get(v_opt_5323_, 0);
    v_defValue_5325_ = lean_ctor_get(v_opt_5323_, 1);
    v_map_5326_ = lean_ctor_get(v_opts_5322_, 0);
    v___x_5327_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5326_,
            v_name_5324_,
        );
    if lean_obj_tag(v___x_5327_) == 0 {
        let mut v___x_5328_: u8 = 0;
        v___x_5328_ = (lean_unbox(v_defValue_5325_) as u8);
        return v___x_5328_;
    } else {
        let mut v_val_5329_: *mut LeanObject = core::ptr::null_mut();
        v_val_5329_ = lean_ctor_get(v___x_5327_, 0);
        lean_inc(v_val_5329_);
        lean_dec_ref_known(v___x_5327_, 1);
        if lean_obj_tag(v_val_5329_) == 1 {
            let mut v_v_5330_: u8 = 0;
            v_v_5330_ = lean_ctor_get_uint8(v_val_5329_, 0 as u32);
            lean_dec_ref_known(v_val_5329_, 0);
            return v_v_5330_;
        } else {
            let mut v___x_5331_: u8 = 0;
            lean_dec(v_val_5329_);
            v___x_5331_ = (lean_unbox(v_defValue_5325_) as u8);
            return v___x_5331_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34___boxed(
    mut v_opts_5332_: *mut LeanObject,
    mut v_opt_5333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5334_: u8 = 0;
    let mut v_r_5335_: *mut LeanObject = core::ptr::null_mut();
    v_res_5334_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29_spec__34(v_opts_5332_, v_opt_5333_);
    lean_dec_ref(v_opt_5333_);
    lean_dec_ref(v_opts_5332_);
    v_r_5335_ = lean_box((v_res_5334_) as usize);
    return v_r_5335_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(
    mut v_ref_5337_: *mut LeanObject,
    mut v_msgData_5338_: *mut LeanObject,
    mut v_severity_5339_: u8,
    mut v_isSilent_5340_: u8,
    mut v___y_5341_: *mut LeanObject,
    mut v___y_5342_: *mut LeanObject,
    mut v___y_5343_: *mut LeanObject,
    mut v___y_5344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5350_: u8 = 0;
    let mut v___y_5351_: u8 = 0;
    let mut v___y_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5370_: u8 = 0;
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5381_: u8 = 0;
    let mut v___y_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5385_: u8 = 0;
    let mut v___y_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5388_: u8 = 0;
    let mut v___y_5389_: u8 = 0;
    let mut v___y_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: u8 = 0;
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5406_: u8 = 0;
    let mut v___y_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5410_: u8 = 0;
    let mut v___y_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5413_: u8 = 0;
    let mut v___y_5414_: u8 = 0;
    let mut v___y_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5421_: u8 = 0;
    let mut v___y_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5424_: u8 = 0;
    let mut v___y_5425_: u8 = 0;
    let mut v_ref_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: u8 = 0;
    let mut v___y_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5433_: u8 = 0;
    let mut v___y_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5437_: u8 = 0;
    let mut v___y_5438_: u8 = 0;
    let mut v___y_5440_: u8 = 0;
    let mut v_fileName_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5445_: u8 = 0;
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: u8 = 0;
    let mut v___x_5450_: u8 = 0;
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: u8 = 0;
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_5338_);
                    v___x_5456_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5338_);
                    v___y_5440_ = v___x_5456_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5356_ = lean_st_ref_take(v___y_5355_);
                v_currNamespace_5357_ = lean_ctor_get(v___y_5354_, 6);
                v_openDecls_5358_ = lean_ctor_get(v___y_5354_, 7);
                v_env_5359_ = lean_ctor_get(v___x_5356_, 0);
                v_nextMacroScope_5360_ = lean_ctor_get(v___x_5356_, 1);
                v_ngen_5361_ = lean_ctor_get(v___x_5356_, 2);
                v_auxDeclNGen_5362_ = lean_ctor_get(v___x_5356_, 3);
                v_traceState_5363_ = lean_ctor_get(v___x_5356_, 4);
                v_cache_5364_ = lean_ctor_get(v___x_5356_, 5);
                v_messages_5365_ = lean_ctor_get(v___x_5356_, 6);
                v_infoState_5366_ = lean_ctor_get(v___x_5356_, 7);
                v_snapshotTasks_5367_ = lean_ctor_get(v___x_5356_, 8);
                v_isSharedCheck_5381_ = (!lean_is_exclusive(v___x_5356_)) as u8;
                if v_isSharedCheck_5381_ == 0 {
                    v___x_5369_ = v___x_5356_;
                    v_isShared_5370_ = v_isSharedCheck_5381_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5367_);
                    lean_inc(v_infoState_5366_);
                    lean_inc(v_messages_5365_);
                    lean_inc(v_cache_5364_);
                    lean_inc(v_traceState_5363_);
                    lean_inc(v_auxDeclNGen_5362_);
                    lean_inc(v_ngen_5361_);
                    lean_inc(v_nextMacroScope_5360_);
                    lean_inc(v_env_5359_);
                    lean_dec(v___x_5356_);
                    v___x_5369_ = lean_box(0);
                    v_isShared_5370_ = v_isSharedCheck_5381_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_5358_);
                lean_inc(v_currNamespace_5357_);
                v___x_5371_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5371_, 0, v_currNamespace_5357_);
                lean_ctor_set(v___x_5371_, 1, v_openDecls_5358_);
                v___x_5372_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5372_, 0, v___x_5371_);
                lean_ctor_set(v___x_5372_, 1, v___y_5353_);
                lean_inc_ref(v___y_5347_);
                lean_inc_ref(v___y_5348_);
                v___x_5373_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_5373_, 0, v___y_5348_);
                lean_ctor_set(v___x_5373_, 1, v___y_5352_);
                lean_ctor_set(v___x_5373_, 2, v___y_5349_);
                lean_ctor_set(v___x_5373_, 3, v___y_5347_);
                lean_ctor_set(v___x_5373_, 4, v___x_5372_);
                lean_ctor_set_uint8(
                    v___x_5373_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_5350_,
                );
                lean_ctor_set_uint8(
                    v___x_5373_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_5351_,
                );
                lean_ctor_set_uint8(
                    v___x_5373_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5340_,
                );
                v___x_5374_ = l_Lean_MessageLog_add(v___x_5373_, v_messages_5365_);
                if v_isShared_5370_ == 0 {
                    lean_ctor_set(v___x_5369_, 6, v___x_5374_);
                    v___x_5376_ = v___x_5369_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_env_5359_);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 1, v_nextMacroScope_5360_);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 2, v_ngen_5361_);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 3, v_auxDeclNGen_5362_);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 4, v_traceState_5363_);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 5, v_cache_5364_);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 6, v___x_5374_);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 7, v_infoState_5366_);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 8, v_snapshotTasks_5367_);
                    v___x_5376_ = v_reuseFailAlloc_5380_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5377_ = lean_st_ref_set(v___y_5355_, v___x_5376_);
                v___x_5378_ = lean_box(0);
                v___x_5379_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5379_, 0, v___x_5378_);
                return v___x_5379_;
            }
            4 => {
                v___x_5391_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5338_,
                    );
                v___x_5392_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9_spec__17(v___x_5391_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_);
                v_a_5393_ = lean_ctor_get(v___x_5392_, 0);
                v_isSharedCheck_5406_ = (!lean_is_exclusive(v___x_5392_)) as u8;
                if v_isSharedCheck_5406_ == 0 {
                    v___x_5395_ = v___x_5392_;
                    v_isShared_5396_ = v_isSharedCheck_5406_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_5393_);
                    lean_dec(v___x_5392_);
                    v___x_5395_ = lean_box(0);
                    v_isShared_5396_ = v_isSharedCheck_5406_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_5387_, 2);
                v___x_5397_ = l_Lean_FileMap_toPosition(v___y_5387_, v___y_5384_);
                lean_dec(v___y_5384_);
                v___x_5398_ = l_Lean_FileMap_toPosition(v___y_5387_, v___y_5390_);
                lean_dec(v___y_5390_);
                v___x_5399_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5399_, 0, v___x_5398_);
                v___x_5400_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___closed__0;
                if v___y_5385_ == 0 {
                    lean_del_object(v___x_5395_);
                    lean_dec_ref(v___y_5383_);
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
                    lean_inc(v_a_5393_);
                    v___x_5401_ = l_Lean_MessageData_hasTag(v___y_5383_, v_a_5393_);
                    if v___x_5401_ == 0 {
                        lean_dec_ref_known(v___x_5399_, 1);
                        lean_dec_ref(v___x_5397_);
                        lean_dec(v_a_5393_);
                        v___x_5402_ = lean_box(0);
                        if v_isShared_5396_ == 0 {
                            lean_ctor_set(v___x_5395_, 0, v___x_5402_);
                            v___x_5404_ = v___x_5395_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5405_, 0, v___x_5402_);
                            v___x_5404_ = v_reuseFailAlloc_5405_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5395_);
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
                lean_dec(v___y_5409_);
                if lean_obj_tag(v___x_5416_) == 0 {
                    lean_inc(v___y_5415_);
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
                    v_val_5417_ = lean_ctor_get(v___x_5416_, 0);
                    lean_inc(v_val_5417_);
                    lean_dec_ref_known(v___x_5416_, 1);
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
                if lean_obj_tag(v___x_5427_) == 0 {
                    v___x_5428_ = lean_unsigned_to_nat(0);
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
                    v_val_5429_ = lean_ctor_get(v___x_5427_, 0);
                    lean_inc(v_val_5429_);
                    lean_dec_ref_known(v___x_5427_, 1);
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
                    v_fileName_5441_ = lean_ctor_get(v___y_5343_, 0);
                    v_fileMap_5442_ = lean_ctor_get(v___y_5343_, 1);
                    v_options_5443_ = lean_ctor_get(v___y_5343_, 2);
                    v_ref_5444_ = lean_ctor_get(v___y_5343_, 5);
                    v_suppressElabErrors_5445_ = lean_ctor_get_uint8(
                        v___y_5343_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5446_ = lean_box((v___y_5440_) as usize);
                    v___x_5447_ = lean_box((v_suppressElabErrors_5445_) as usize);
                    v___f_5448_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_5448_, 0, v___x_5446_);
                    lean_closure_set(v___f_5448_, 1, v___x_5447_);
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
                    lean_dec_ref(v_msgData_5338_);
                    v___x_5453_ = lean_box(0);
                    v___x_5454_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5454_, 0, v___x_5453_);
                    return v___x_5454_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg___boxed(
    mut v_ref_5457_: *mut LeanObject,
    mut v_msgData_5458_: *mut LeanObject,
    mut v_severity_5459_: *mut LeanObject,
    mut v_isSilent_5460_: *mut LeanObject,
    mut v___y_5461_: *mut LeanObject,
    mut v___y_5462_: *mut LeanObject,
    mut v___y_5463_: *mut LeanObject,
    mut v___y_5464_: *mut LeanObject,
    mut v___y_5465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5466_: u8 = 0;
    let mut v_isSilent_boxed_5467_: u8 = 0;
    let mut v_res_5468_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5466_ = (lean_unbox(v_severity_5459_) as u8);
    v_isSilent_boxed_5467_ = (lean_unbox(v_isSilent_5460_) as u8);
    v_res_5468_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_5457_, v_msgData_5458_, v_severity_boxed_5466_, v_isSilent_boxed_5467_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_);
    lean_dec(v___y_5464_);
    lean_dec_ref(v___y_5463_);
    lean_dec(v___y_5462_);
    lean_dec_ref(v___y_5461_);
    lean_dec(v_ref_5457_);
    return v_res_5468_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(
    mut v_msgData_5469_: *mut LeanObject,
    mut v_severity_5470_: u8,
    mut v_isSilent_5471_: u8,
    mut v___y_5472_: *mut LeanObject,
    mut v___y_5473_: *mut LeanObject,
    mut v___y_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5478_ = lean_ctor_get(v___y_5475_, 5);
    v___x_5479_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_5478_, v_msgData_5469_, v_severity_5470_, v_isSilent_5471_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_);
    return v___x_5479_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24___boxed(
    mut v_msgData_5480_: *mut LeanObject,
    mut v_severity_5481_: *mut LeanObject,
    mut v_isSilent_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
    mut v___y_5485_: *mut LeanObject,
    mut v___y_5486_: *mut LeanObject,
    mut v___y_5487_: *mut LeanObject,
    mut v___y_5488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5489_: u8 = 0;
    let mut v_isSilent_boxed_5490_: u8 = 0;
    let mut v_res_5491_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5489_ = (lean_unbox(v_severity_5481_) as u8);
    v_isSilent_boxed_5490_ = (lean_unbox(v_isSilent_5482_) as u8);
    v_res_5491_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_5480_, v_severity_boxed_5489_, v_isSilent_boxed_5490_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_);
    lean_dec(v___y_5487_);
    lean_dec_ref(v___y_5486_);
    lean_dec(v___y_5485_);
    lean_dec_ref(v___y_5484_);
    lean_dec(v___y_5483_);
    return v_res_5491_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15(
    mut v_msgData_5492_: *mut LeanObject,
    mut v___y_5493_: *mut LeanObject,
    mut v___y_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
    mut v___y_5496_: *mut LeanObject,
    mut v___y_5497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5499_: u8 = 0;
    let mut v___x_5500_: u8 = 0;
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    v___x_5499_ = 1;
    v___x_5500_ = 0;
    v___x_5501_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24(v_msgData_5492_, v___x_5499_, v___x_5500_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_);
    return v___x_5501_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15___boxed(
    mut v_msgData_5502_: *mut LeanObject,
    mut v___y_5503_: *mut LeanObject,
    mut v___y_5504_: *mut LeanObject,
    mut v___y_5505_: *mut LeanObject,
    mut v___y_5506_: *mut LeanObject,
    mut v___y_5507_: *mut LeanObject,
    mut v___y_5508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5509_: *mut LeanObject = core::ptr::null_mut();
    v_res_5509_ = l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15(v_msgData_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_);
    lean_dec(v___y_5507_);
    lean_dec_ref(v___y_5506_);
    lean_dec(v___y_5505_);
    lean_dec_ref(v___y_5504_);
    lean_dec(v___y_5503_);
    return v_res_5509_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1()
-> *mut LeanObject {
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    v___x_5511_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__0;
    v___x_5512_ = l_Lean_stringToMessageData(v___x_5511_);
    return v___x_5512_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4()
-> *mut LeanObject {
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    v___x_5518_ = lean_box(0);
    v___x_5519_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__3;
    v___x_5520_ = l_Lean_mkConst(v___x_5519_, v___x_5518_);
    return v___x_5520_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5()
-> *mut LeanObject {
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    v___x_5521_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__4);
    v___x_5522_ = l_Lean_MessageData_ofExpr(v___x_5521_);
    return v___x_5522_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6()
-> *mut LeanObject {
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    v___x_5523_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__5);
    v___x_5524_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__1);
    v___x_5525_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5525_, 0, v___x_5524_);
    lean_ctor_set(v___x_5525_, 1, v___x_5523_);
    return v___x_5525_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize(
    mut v_goal_5526_: *mut LeanObject,
    mut v_a_5527_: *mut LeanObject,
    mut v_a_5528_: *mut LeanObject,
    mut v_a_5529_: *mut LeanObject,
    mut v_a_5530_: *mut LeanObject,
    mut v_a_5531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5544_: u8 = 0;
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5548_: u8 = 0;
    let mut v_unused_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5553_: u8 = 0;
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5557_: u8 = 0;
    let mut v_a_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5561_: u8 = 0;
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_goal_5526_);
                v___x_5533_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_findNumBitsEq(v_goal_5526_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
                if lean_obj_tag(v___x_5533_) == 0 {
                    v_a_5534_ = lean_ctor_get(v___x_5533_, 0);
                    lean_inc(v_a_5534_);
                    lean_dec_ref_known(v___x_5533_, 1);
                    if lean_obj_tag(v_a_5534_) == 1 {
                        v_val_5535_ = lean_ctor_get(v_a_5534_, 0);
                        lean_inc(v_val_5535_);
                        lean_dec_ref_known(v_a_5534_, 1);
                        v_fst_5536_ = lean_ctor_get(v_val_5535_, 0);
                        lean_inc(v_fst_5536_);
                        v_snd_5537_ = lean_ctor_get(v_val_5535_, 1);
                        lean_inc(v_snd_5537_);
                        lean_dec(v_val_5535_);
                        lean_inc(v_goal_5526_);
                        v___f_5538_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___boxed as *mut core::ffi::c_void, 9, 3);
                        lean_closure_set(v___f_5538_, 0, v_fst_5536_);
                        lean_closure_set(v___f_5538_, 1, v_snd_5537_);
                        lean_closure_set(v___f_5538_, 2, v_goal_5526_);
                        v___x_5539_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_5526_, v___f_5538_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
                        return v___x_5539_;
                    } else {
                        lean_dec(v_a_5534_);
                        v___x_5540_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___closed__6);
                        v___x_5541_ = l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15(v___x_5540_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
                        if lean_obj_tag(v___x_5541_) == 0 {
                            v_isSharedCheck_5548_ = (!lean_is_exclusive(v___x_5541_)) as u8;
                            if v_isSharedCheck_5548_ == 0 {
                                v_unused_5549_ = lean_ctor_get(v___x_5541_, 0);
                                lean_dec(v_unused_5549_);
                                v___x_5543_ = v___x_5541_;
                                v_isShared_5544_ = v_isSharedCheck_5548_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_5541_);
                                v___x_5543_ = lean_box(0);
                                v_isShared_5544_ = v_isSharedCheck_5548_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_goal_5526_);
                            v_a_5550_ = lean_ctor_get(v___x_5541_, 0);
                            v_isSharedCheck_5557_ = (!lean_is_exclusive(v___x_5541_)) as u8;
                            if v_isSharedCheck_5557_ == 0 {
                                v___x_5552_ = v___x_5541_;
                                v_isShared_5553_ = v_isSharedCheck_5557_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5550_);
                                lean_dec(v___x_5541_);
                                v___x_5552_ = lean_box(0);
                                v_isShared_5553_ = v_isSharedCheck_5557_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_goal_5526_);
                    v_a_5558_ = lean_ctor_get(v___x_5533_, 0);
                    v_isSharedCheck_5565_ = (!lean_is_exclusive(v___x_5533_)) as u8;
                    if v_isSharedCheck_5565_ == 0 {
                        v___x_5560_ = v___x_5533_;
                        v_isShared_5561_ = v_isSharedCheck_5565_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5558_);
                        lean_dec(v___x_5533_);
                        v___x_5560_ = lean_box(0);
                        v_isShared_5561_ = v_isSharedCheck_5565_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5544_ == 0 {
                    lean_ctor_set(v___x_5543_, 0, v_goal_5526_);
                    v___x_5546_ = v___x_5543_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_goal_5526_);
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
                    v_reuseFailAlloc_5556_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5556_, 0, v_a_5550_);
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
                    v_reuseFailAlloc_5564_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_a_5558_);
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
    mut v_goal_5566_: *mut LeanObject,
    mut v_a_5567_: *mut LeanObject,
    mut v_a_5568_: *mut LeanObject,
    mut v_a_5569_: *mut LeanObject,
    mut v_a_5570_: *mut LeanObject,
    mut v_a_5571_: *mut LeanObject,
    mut v_a_5572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5573_: *mut LeanObject = core::ptr::null_mut();
    v_res_5573_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize(v_goal_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_, v_a_5571_);
    lean_dec(v_a_5571_);
    lean_dec_ref(v_a_5570_);
    lean_dec(v_a_5569_);
    lean_dec_ref(v_a_5568_);
    lean_dec(v_a_5567_);
    return v_res_5573_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0(
    mut v_00_u03b2_5574_: *mut LeanObject,
    mut v_m_5575_: *mut LeanObject,
    mut v_a_5576_: *mut LeanObject,
    mut v_b_5577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    v___x_5578_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0___redArg(v_m_5575_, v_a_5576_, v_b_5577_);
    return v___x_5578_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2(
    mut v_as_5579_: *mut LeanObject,
    mut v_sz_5580_: usize,
    mut v_i_5581_: usize,
    mut v_b_5582_: *mut LeanObject,
    mut v___y_5583_: *mut LeanObject,
    mut v___y_5584_: *mut LeanObject,
    mut v___y_5585_: *mut LeanObject,
    mut v___y_5586_: *mut LeanObject,
    mut v___y_5587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    v___x_5589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___redArg(v_as_5579_, v_sz_5580_, v_i_5581_, v_b_5582_);
    return v___x_5589_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2___boxed(
    mut v_as_5590_: *mut LeanObject,
    mut v_sz_5591_: *mut LeanObject,
    mut v_i_5592_: *mut LeanObject,
    mut v_b_5593_: *mut LeanObject,
    mut v___y_5594_: *mut LeanObject,
    mut v___y_5595_: *mut LeanObject,
    mut v___y_5596_: *mut LeanObject,
    mut v___y_5597_: *mut LeanObject,
    mut v___y_5598_: *mut LeanObject,
    mut v___y_5599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5600_: usize = 0;
    let mut v_i_boxed_5601_: usize = 0;
    let mut v_res_5602_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5600_ = lean_unbox_usize(v_sz_5591_);
    lean_dec(v_sz_5591_);
    v_i_boxed_5601_ = lean_unbox_usize(v_i_5592_);
    lean_dec(v_i_5592_);
    v_res_5602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__2(v_as_5590_, v_sz_boxed_5600_, v_i_boxed_5601_, v_b_5593_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
    lean_dec(v___y_5598_);
    lean_dec_ref(v___y_5597_);
    lean_dec(v___y_5596_);
    lean_dec_ref(v___y_5595_);
    lean_dec(v___y_5594_);
    lean_dec_ref(v_as_5590_);
    return v_res_5602_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3(
    mut v_00_u03b2_5603_: *mut LeanObject,
    mut v_m_5604_: *mut LeanObject,
    mut v_a_5605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    v___x_5606_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___redArg(v_m_5604_, v_a_5605_);
    return v___x_5606_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3___boxed(
    mut v_00_u03b2_5607_: *mut LeanObject,
    mut v_m_5608_: *mut LeanObject,
    mut v_a_5609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5610_: *mut LeanObject = core::ptr::null_mut();
    v_res_5610_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3(v_00_u03b2_5607_, v_m_5608_, v_a_5609_);
    lean_dec_ref(v_a_5609_);
    lean_dec_ref(v_m_5608_);
    return v_res_5610_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(
    mut v_00_u03b1_5611_: *mut LeanObject,
    mut v_name_5612_: *mut LeanObject,
    mut v_bi_5613_: u8,
    mut v_type_5614_: *mut LeanObject,
    mut v_k_5615_: *mut LeanObject,
    mut v_kind_5616_: u8,
    mut v___y_5617_: *mut LeanObject,
    mut v___y_5618_: *mut LeanObject,
    mut v___y_5619_: *mut LeanObject,
    mut v___y_5620_: *mut LeanObject,
    mut v___y_5621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    v___x_5623_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___redArg(v_name_5612_, v_bi_5613_, v_type_5614_, v_k_5615_, v_kind_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    return v___x_5623_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12___boxed(
    mut v_00_u03b1_5624_: *mut LeanObject,
    mut v_name_5625_: *mut LeanObject,
    mut v_bi_5626_: *mut LeanObject,
    mut v_type_5627_: *mut LeanObject,
    mut v_k_5628_: *mut LeanObject,
    mut v_kind_5629_: *mut LeanObject,
    mut v___y_5630_: *mut LeanObject,
    mut v___y_5631_: *mut LeanObject,
    mut v___y_5632_: *mut LeanObject,
    mut v___y_5633_: *mut LeanObject,
    mut v___y_5634_: *mut LeanObject,
    mut v___y_5635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_5636_: u8 = 0;
    let mut v_kind_boxed_5637_: u8 = 0;
    let mut v_res_5638_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_5636_ = (lean_unbox(v_bi_5626_) as u8);
    v_kind_boxed_5637_ = (lean_unbox(v_kind_5629_) as u8);
    v_res_5638_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6_spec__12(v_00_u03b1_5624_, v_name_5625_, v_bi_boxed_5636_, v_type_5627_, v_k_5628_, v_kind_boxed_5637_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_);
    lean_dec(v___y_5634_);
    lean_dec_ref(v___y_5633_);
    lean_dec(v___y_5632_);
    lean_dec_ref(v___y_5631_);
    lean_dec(v___y_5630_);
    return v_res_5638_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6(
    mut v_00_u03b1_5639_: *mut LeanObject,
    mut v_name_5640_: *mut LeanObject,
    mut v_type_5641_: *mut LeanObject,
    mut v_k_5642_: *mut LeanObject,
    mut v___y_5643_: *mut LeanObject,
    mut v___y_5644_: *mut LeanObject,
    mut v___y_5645_: *mut LeanObject,
    mut v___y_5646_: *mut LeanObject,
    mut v___y_5647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    v___x_5649_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___redArg(v_name_5640_, v_type_5641_, v_k_5642_, v___y_5643_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
    return v___x_5649_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6___boxed(
    mut v_00_u03b1_5650_: *mut LeanObject,
    mut v_name_5651_: *mut LeanObject,
    mut v_type_5652_: *mut LeanObject,
    mut v_k_5653_: *mut LeanObject,
    mut v___y_5654_: *mut LeanObject,
    mut v___y_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
    mut v___y_5657_: *mut LeanObject,
    mut v___y_5658_: *mut LeanObject,
    mut v___y_5659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5660_: *mut LeanObject = core::ptr::null_mut();
    v_res_5660_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__6(v_00_u03b1_5650_, v_name_5651_, v_type_5652_, v_k_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
    lean_dec(v___y_5658_);
    lean_dec_ref(v___y_5657_);
    lean_dec(v___y_5656_);
    lean_dec_ref(v___y_5655_);
    lean_dec(v___y_5654_);
    return v_res_5660_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7(
    mut v_mvarId_5661_: *mut LeanObject,
    mut v_val_5662_: *mut LeanObject,
    mut v___y_5663_: *mut LeanObject,
    mut v___y_5664_: *mut LeanObject,
    mut v___y_5665_: *mut LeanObject,
    mut v___y_5666_: *mut LeanObject,
    mut v___y_5667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    v___x_5669_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___redArg(v_mvarId_5661_, v_val_5662_, v___y_5665_);
    return v___x_5669_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7___boxed(
    mut v_mvarId_5670_: *mut LeanObject,
    mut v_val_5671_: *mut LeanObject,
    mut v___y_5672_: *mut LeanObject,
    mut v___y_5673_: *mut LeanObject,
    mut v___y_5674_: *mut LeanObject,
    mut v___y_5675_: *mut LeanObject,
    mut v___y_5676_: *mut LeanObject,
    mut v___y_5677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5678_: *mut LeanObject = core::ptr::null_mut();
    v_res_5678_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7(v_mvarId_5670_, v_val_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_);
    lean_dec(v___y_5676_);
    lean_dec_ref(v___y_5675_);
    lean_dec(v___y_5674_);
    lean_dec_ref(v___y_5673_);
    lean_dec(v___y_5672_);
    return v_res_5678_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9(
    mut v_00_u03b1_5679_: *mut LeanObject,
    mut v_msg_5680_: *mut LeanObject,
    mut v___y_5681_: *mut LeanObject,
    mut v___y_5682_: *mut LeanObject,
    mut v___y_5683_: *mut LeanObject,
    mut v___y_5684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    v___x_5686_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___redArg(v_msg_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
    return v___x_5686_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9___boxed(
    mut v_00_u03b1_5687_: *mut LeanObject,
    mut v_msg_5688_: *mut LeanObject,
    mut v___y_5689_: *mut LeanObject,
    mut v___y_5690_: *mut LeanObject,
    mut v___y_5691_: *mut LeanObject,
    mut v___y_5692_: *mut LeanObject,
    mut v___y_5693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5694_: *mut LeanObject = core::ptr::null_mut();
    v_res_5694_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__9(v_00_u03b1_5687_, v_msg_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_);
    lean_dec(v___y_5692_);
    lean_dec_ref(v___y_5691_);
    lean_dec(v___y_5690_);
    lean_dec_ref(v___y_5689_);
    return v_res_5694_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(
    mut v_00_u03b2_5695_: *mut LeanObject,
    mut v_a_5696_: *mut LeanObject,
    mut v_x_5697_: *mut LeanObject,
) -> u8 {
    let mut v___x_5698_: u8 = 0;
    v___x_5698_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___redArg(v_a_5696_, v_x_5697_);
    return v___x_5698_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0___boxed(
    mut v_00_u03b2_5699_: *mut LeanObject,
    mut v_a_5700_: *mut LeanObject,
    mut v_x_5701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5702_: u8 = 0;
    let mut v_r_5703_: *mut LeanObject = core::ptr::null_mut();
    v_res_5702_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__0(v_00_u03b2_5699_, v_a_5700_, v_x_5701_);
    lean_dec(v_x_5701_);
    lean_dec_ref(v_a_5700_);
    v_r_5703_ = lean_box((v_res_5702_) as usize);
    return v_r_5703_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1(
    mut v_00_u03b2_5704_: *mut LeanObject,
    mut v_data_5705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    v___x_5706_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_data_5705_);
    return v___x_5706_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2(
    mut v_00_u03b2_5707_: *mut LeanObject,
    mut v_a_5708_: *mut LeanObject,
    mut v_b_5709_: *mut LeanObject,
    mut v_x_5710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    v___x_5711_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__2___redArg(v_a_5708_, v_b_5709_, v_x_5710_);
    return v___x_5711_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(
    mut v_00_u03b2_5712_: *mut LeanObject,
    mut v_a_5713_: *mut LeanObject,
    mut v_x_5714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    v___x_5715_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___redArg(v_a_5713_, v_x_5714_);
    return v___x_5715_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6___boxed(
    mut v_00_u03b2_5716_: *mut LeanObject,
    mut v_a_5717_: *mut LeanObject,
    mut v_x_5718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5719_: *mut LeanObject = core::ptr::null_mut();
    v_res_5719_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__3_spec__6(v_00_u03b2_5716_, v_a_5717_, v_x_5718_);
    lean_dec(v_x_5718_);
    lean_dec_ref(v_a_5717_);
    return v_res_5719_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14(
    mut v_00_u03b2_5720_: *mut LeanObject,
    mut v_x_5721_: *mut LeanObject,
    mut v_x_5722_: *mut LeanObject,
    mut v_x_5723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    v___x_5724_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14___redArg(v_x_5721_, v_x_5722_, v_x_5723_);
    return v___x_5724_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3(
    mut v_00_u03b2_5725_: *mut LeanObject,
    mut v_i_5726_: *mut LeanObject,
    mut v_source_5727_: *mut LeanObject,
    mut v_target_5728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    v___x_5729_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3___redArg(v_i_5726_, v_source_5727_, v_target_5728_);
    return v___x_5729_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(
    mut v_00_u03b2_5730_: *mut LeanObject,
    mut v_x_5731_: *mut LeanObject,
    mut v_x_5732_: usize,
    mut v_x_5733_: usize,
    mut v_x_5734_: *mut LeanObject,
    mut v_x_5735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    v___x_5736_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___redArg(v_x_5731_, v_x_5732_, v_x_5733_, v_x_5734_, v_x_5735_);
    return v___x_5736_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19___boxed(
    mut v_00_u03b2_5737_: *mut LeanObject,
    mut v_x_5738_: *mut LeanObject,
    mut v_x_5739_: *mut LeanObject,
    mut v_x_5740_: *mut LeanObject,
    mut v_x_5741_: *mut LeanObject,
    mut v_x_5742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_23590__boxed_5743_: usize = 0;
    let mut v_x_23591__boxed_5744_: usize = 0;
    let mut v_res_5745_: *mut LeanObject = core::ptr::null_mut();
    v_x_23590__boxed_5743_ = lean_unbox_usize(v_x_5739_);
    lean_dec(v_x_5739_);
    v_x_23591__boxed_5744_ = lean_unbox_usize(v_x_5740_);
    lean_dec(v_x_5740_);
    v_res_5745_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19(v_00_u03b2_5737_, v_x_5738_, v_x_23590__boxed_5743_, v_x_23591__boxed_5744_, v_x_5741_, v_x_5742_);
    return v_res_5745_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(
    mut v_ref_5746_: *mut LeanObject,
    mut v_msgData_5747_: *mut LeanObject,
    mut v_severity_5748_: u8,
    mut v_isSilent_5749_: u8,
    mut v___y_5750_: *mut LeanObject,
    mut v___y_5751_: *mut LeanObject,
    mut v___y_5752_: *mut LeanObject,
    mut v___y_5753_: *mut LeanObject,
    mut v___y_5754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    v___x_5756_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___redArg(v_ref_5746_, v_msgData_5747_, v_severity_5748_, v_isSilent_5749_, v___y_5751_, v___y_5752_, v___y_5753_, v___y_5754_);
    return v___x_5756_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29___boxed(
    mut v_ref_5757_: *mut LeanObject,
    mut v_msgData_5758_: *mut LeanObject,
    mut v_severity_5759_: *mut LeanObject,
    mut v_isSilent_5760_: *mut LeanObject,
    mut v___y_5761_: *mut LeanObject,
    mut v___y_5762_: *mut LeanObject,
    mut v___y_5763_: *mut LeanObject,
    mut v___y_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5767_: u8 = 0;
    let mut v_isSilent_boxed_5768_: u8 = 0;
    let mut v_res_5769_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5767_ = (lean_unbox(v_severity_5759_) as u8);
    v_isSilent_boxed_5768_ = (lean_unbox(v_isSilent_5760_) as u8);
    v_res_5769_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__15_spec__24_spec__29(v_ref_5757_, v_msgData_5758_, v_severity_boxed_5767_, v_isSilent_boxed_5768_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_);
    lean_dec(v___y_5765_);
    lean_dec_ref(v___y_5764_);
    lean_dec(v___y_5763_);
    lean_dec_ref(v___y_5762_);
    lean_dec(v___y_5761_);
    lean_dec(v_ref_5757_);
    return v_res_5769_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20(
    mut v_00_u03b2_5770_: *mut LeanObject,
    mut v_x_5771_: *mut LeanObject,
    mut v_x_5772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
    v___x_5773_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1_spec__3_spec__20___redArg(v_x_5771_, v_x_5772_);
    return v___x_5773_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30(
    mut v_00_u03b2_5774_: *mut LeanObject,
    mut v_n_5775_: *mut LeanObject,
    mut v_k_5776_: *mut LeanObject,
    mut v_v_5777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    v___x_5778_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30___redArg(v_n_5775_, v_k_5776_, v_v_5777_);
    return v___x_5778_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(
    mut v_00_u03b2_5779_: *mut LeanObject,
    mut v_depth_5780_: usize,
    mut v_keys_5781_: *mut LeanObject,
    mut v_vals_5782_: *mut LeanObject,
    mut v_heq_5783_: *mut LeanObject,
    mut v_i_5784_: *mut LeanObject,
    mut v_entries_5785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    v___x_5786_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___redArg(v_depth_5780_, v_keys_5781_, v_vals_5782_, v_i_5784_, v_entries_5785_);
    return v___x_5786_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31___boxed(
    mut v_00_u03b2_5787_: *mut LeanObject,
    mut v_depth_5788_: *mut LeanObject,
    mut v_keys_5789_: *mut LeanObject,
    mut v_vals_5790_: *mut LeanObject,
    mut v_heq_5791_: *mut LeanObject,
    mut v_i_5792_: *mut LeanObject,
    mut v_entries_5793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_5794_: usize = 0;
    let mut v_res_5795_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_5794_ = lean_unbox_usize(v_depth_5788_);
    lean_dec(v_depth_5788_);
    v_res_5795_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__31(v_00_u03b2_5787_, v_depth_boxed_5794_, v_keys_5789_, v_vals_5790_, v_heq_5791_, v_i_5792_, v_entries_5793_);
    lean_dec_ref(v_vals_5790_);
    lean_dec_ref(v_keys_5789_);
    return v_res_5795_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32(
    mut v_00_u03b2_5796_: *mut LeanObject,
    mut v_x_5797_: *mut LeanObject,
    mut v_x_5798_: *mut LeanObject,
    mut v_x_5799_: *mut LeanObject,
    mut v_x_5800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    v___x_5801_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__7_spec__14_spec__19_spec__30_spec__32___redArg(v_x_5797_, v_x_5798_, v_x_5799_, v_x_5800_);
    return v___x_5801_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(
    mut v_e_5802_: *mut LeanObject,
    mut v___y_5803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5805_: u8 = 0;
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5825_: u8 = 0;
    let mut v_unused_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5805_ = l_Lean_Expr_hasMVar(v_e_5802_);
                if v___x_5805_ == 0 {
                    v___x_5806_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5806_, 0, v_e_5802_);
                    return v___x_5806_;
                } else {
                    v___x_5807_ = lean_st_ref_get(v___y_5803_);
                    v_mctx_5808_ = lean_ctor_get(v___x_5807_, 0);
                    lean_inc_ref(v_mctx_5808_);
                    lean_dec(v___x_5807_);
                    v___x_5809_ = l_Lean_instantiateMVarsCore(v_mctx_5808_, v_e_5802_);
                    v_fst_5810_ = lean_ctor_get(v___x_5809_, 0);
                    lean_inc(v_fst_5810_);
                    v_snd_5811_ = lean_ctor_get(v___x_5809_, 1);
                    lean_inc(v_snd_5811_);
                    lean_dec_ref(v___x_5809_);
                    v___x_5812_ = lean_st_ref_take(v___y_5803_);
                    v_cache_5813_ = lean_ctor_get(v___x_5812_, 1);
                    v_zetaDeltaFVarIds_5814_ = lean_ctor_get(v___x_5812_, 2);
                    v_postponed_5815_ = lean_ctor_get(v___x_5812_, 3);
                    v_diag_5816_ = lean_ctor_get(v___x_5812_, 4);
                    v_isSharedCheck_5825_ = (!lean_is_exclusive(v___x_5812_)) as u8;
                    if v_isSharedCheck_5825_ == 0 {
                        v_unused_5826_ = lean_ctor_get(v___x_5812_, 0);
                        lean_dec(v_unused_5826_);
                        v___x_5818_ = v___x_5812_;
                        v_isShared_5819_ = v_isSharedCheck_5825_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_5816_);
                        lean_inc(v_postponed_5815_);
                        lean_inc(v_zetaDeltaFVarIds_5814_);
                        lean_inc(v_cache_5813_);
                        lean_dec(v___x_5812_);
                        v___x_5818_ = lean_box(0);
                        v_isShared_5819_ = v_isSharedCheck_5825_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5819_ == 0 {
                    lean_ctor_set(v___x_5818_, 0, v_snd_5811_);
                    v___x_5821_ = v___x_5818_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5824_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_snd_5811_);
                    lean_ctor_set(v_reuseFailAlloc_5824_, 1, v_cache_5813_);
                    lean_ctor_set(v_reuseFailAlloc_5824_, 2, v_zetaDeltaFVarIds_5814_);
                    lean_ctor_set(v_reuseFailAlloc_5824_, 3, v_postponed_5815_);
                    lean_ctor_set(v_reuseFailAlloc_5824_, 4, v_diag_5816_);
                    v___x_5821_ = v_reuseFailAlloc_5824_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5822_ = lean_st_ref_set(v___y_5803_, v___x_5821_);
                v___x_5823_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5823_, 0, v_fst_5810_);
                return v___x_5823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg___boxed(
    mut v_e_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5830_: *mut LeanObject = core::ptr::null_mut();
    v_res_5830_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_5827_, v___y_5828_);
    lean_dec(v___y_5828_);
    return v_res_5830_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2(
    mut v_e_5831_: *mut LeanObject,
    mut v___y_5832_: *mut LeanObject,
    mut v___y_5833_: *mut LeanObject,
    mut v___y_5834_: *mut LeanObject,
    mut v___y_5835_: *mut LeanObject,
    mut v___y_5836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    v___x_5838_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_e_5831_, v___y_5834_);
    return v___x_5838_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___boxed(
    mut v_e_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5846_: *mut LeanObject = core::ptr::null_mut();
    v_res_5846_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2(v_e_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
    lean_dec(v___y_5844_);
    lean_dec_ref(v___y_5843_);
    lean_dec(v___y_5842_);
    lean_dec_ref(v___y_5841_);
    lean_dec(v___y_5840_);
    return v_res_5846_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(
    mut v_m_5847_: *mut LeanObject,
    mut v_a_5848_: *mut LeanObject,
    mut v_b_5849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: u8 = 0;
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5869_: u8 = 0;
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: u8 = 0;
    let mut v_val_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5887_: u8 = 0;
    let mut v_unused_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5850_ = lean_ctor_get(v_m_5847_, 0);
                v_buckets_5851_ = lean_ctor_get(v_m_5847_, 1);
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
                    lean_inc_ref(v_buckets_5851_);
                    lean_inc(v_size_5850_);
                    v_isSharedCheck_5887_ = (!lean_is_exclusive(v_m_5847_)) as u8;
                    if v_isSharedCheck_5887_ == 0 {
                        v_unused_5888_ = lean_ctor_get(v_m_5847_, 1);
                        lean_dec(v_unused_5888_);
                        v_unused_5889_ = lean_ctor_get(v_m_5847_, 0);
                        lean_dec(v_unused_5889_);
                        v___x_5868_ = v_m_5847_;
                        v_isShared_5869_ = v_isSharedCheck_5887_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_5847_);
                        v___x_5868_ = lean_box(0);
                        v_isShared_5869_ = v_isSharedCheck_5887_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_5849_);
                    lean_dec_ref(v_a_5848_);
                    return v_m_5847_;
                }
            }
            1 => {
                v___x_5870_ = lean_unsigned_to_nat(1);
                v_size_x27_5871_ = lean_nat_add(v_size_5850_, v___x_5870_);
                lean_dec(v_size_5850_);
                lean_inc(v_bkt_5865_);
                v___x_5872_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5872_, 0, v_a_5848_);
                lean_ctor_set(v___x_5872_, 1, v_b_5849_);
                lean_ctor_set(v___x_5872_, 2, v_bkt_5865_);
                v_buckets_x27_5873_ = lean_array_uset(v_buckets_5851_, v___x_5864_, v___x_5872_);
                v___x_5874_ = lean_unsigned_to_nat(4);
                v___x_5875_ = lean_nat_mul(v_size_x27_5871_, v___x_5874_);
                v___x_5876_ = lean_unsigned_to_nat(3);
                v___x_5877_ = lean_nat_div(v___x_5875_, v___x_5876_);
                lean_dec(v___x_5875_);
                v___x_5878_ = lean_array_get_size(v_buckets_x27_5873_);
                v___x_5879_ = lean_nat_dec_le(v___x_5877_, v___x_5878_);
                lean_dec(v___x_5877_);
                if v___x_5879_ == 0 {
                    v_val_5880_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__0_spec__1___redArg(v_buckets_x27_5873_);
                    if v_isShared_5869_ == 0 {
                        lean_ctor_set(v___x_5868_, 1, v_val_5880_);
                        lean_ctor_set(v___x_5868_, 0, v_size_x27_5871_);
                        v___x_5882_ = v___x_5868_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5883_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5883_, 0, v_size_x27_5871_);
                        lean_ctor_set(v_reuseFailAlloc_5883_, 1, v_val_5880_);
                        v___x_5882_ = v_reuseFailAlloc_5883_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_5869_ == 0 {
                        lean_ctor_set(v___x_5868_, 1, v_buckets_x27_5873_);
                        lean_ctor_set(v___x_5868_, 0, v_size_x27_5871_);
                        v___x_5885_ = v___x_5868_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5886_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_size_x27_5871_);
                        lean_ctor_set(v_reuseFailAlloc_5886_, 1, v_buckets_x27_5873_);
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
    mut v_a_5890_: *mut LeanObject,
    mut v_x_5891_: *mut LeanObject,
) -> u8 {
    let mut v___x_5892_: u8 = 0;
    let mut v_key_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5891_) == 0 {
                    v___x_5892_ = 0;
                    return v___x_5892_;
                } else {
                    v_key_5893_ = lean_ctor_get(v_x_5891_, 0);
                    v_tail_5894_ = lean_ctor_get(v_x_5891_, 2);
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
    mut v_a_5897_: *mut LeanObject,
    mut v_x_5898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5899_: u8 = 0;
    let mut v_r_5900_: *mut LeanObject = core::ptr::null_mut();
    v_res_5899_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_5897_, v_x_5898_);
    lean_dec(v_x_5898_);
    lean_dec(v_a_5897_);
    v_r_5900_ = lean_box((v_res_5899_) as usize);
    return v_r_5900_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(
    mut v_x_5901_: *mut LeanObject,
    mut v_x_5902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5908_: u8 = 0;
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5902_) == 0 {
                    return v_x_5901_;
                } else {
                    v_key_5903_ = lean_ctor_get(v_x_5902_, 0);
                    v_value_5904_ = lean_ctor_get(v_x_5902_, 1);
                    v_tail_5905_ = lean_ctor_get(v_x_5902_, 2);
                    v_isSharedCheck_5928_ = (!lean_is_exclusive(v_x_5902_)) as u8;
                    if v_isSharedCheck_5928_ == 0 {
                        v___x_5907_ = v_x_5902_;
                        v_isShared_5908_ = v_isSharedCheck_5928_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5905_);
                        lean_inc(v_value_5904_);
                        lean_inc(v_key_5903_);
                        lean_dec(v_x_5902_);
                        v___x_5907_ = lean_box(0);
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
                lean_inc(v___x_5922_);
                if v_isShared_5908_ == 0 {
                    lean_ctor_set(v___x_5907_, 2, v___x_5922_);
                    v___x_5924_ = v___x_5907_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5927_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_key_5903_);
                    lean_ctor_set(v_reuseFailAlloc_5927_, 1, v_value_5904_);
                    lean_ctor_set(v_reuseFailAlloc_5927_, 2, v___x_5922_);
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
    mut v_i_5929_: *mut LeanObject,
    mut v_source_5930_: *mut LeanObject,
    mut v_target_5931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: u8 = 0;
    let mut v_es_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5932_ = lean_array_get_size(v_source_5930_);
                v___x_5933_ = lean_nat_dec_lt(v_i_5929_, v___x_5932_);
                if v___x_5933_ == 0 {
                    lean_dec_ref(v_source_5930_);
                    lean_dec(v_i_5929_);
                    return v_target_5931_;
                } else {
                    v_es_5934_ = lean_array_fget(v_source_5930_, v_i_5929_);
                    v___x_5935_ = lean_box(0);
                    v_source_5936_ = lean_array_fset(v_source_5930_, v_i_5929_, v___x_5935_);
                    v_target_5937_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_target_5931_, v_es_5934_);
                    v___x_5938_ = lean_unsigned_to_nat(1);
                    v___x_5939_ = lean_nat_add(v_i_5929_, v___x_5938_);
                    lean_dec(v_i_5929_);
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
    mut v_data_5941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    v___x_5942_ = lean_array_get_size(v_data_5941_);
    v___x_5943_ = lean_unsigned_to_nat(2);
    v_nbuckets_5944_ = lean_nat_mul(v___x_5942_, v___x_5943_);
    v___x_5945_ = lean_unsigned_to_nat(0);
    v___x_5946_ = lean_box(0);
    v___x_5947_ = lean_mk_array(v_nbuckets_5944_, v___x_5946_);
    v___x_5948_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v___x_5945_, v_data_5941_, v___x_5947_);
    return v___x_5948_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1___redArg(
    mut v_m_5949_: *mut LeanObject,
    mut v_a_5950_: *mut LeanObject,
    mut v_b_5951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: u8 = 0;
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5971_: u8 = 0;
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: u8 = 0;
    let mut v_val_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5989_: u8 = 0;
    let mut v_unused_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5952_ = lean_ctor_get(v_m_5949_, 0);
                v_buckets_5953_ = lean_ctor_get(v_m_5949_, 1);
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
                    lean_inc_ref(v_buckets_5953_);
                    lean_inc(v_size_5952_);
                    v_isSharedCheck_5989_ = (!lean_is_exclusive(v_m_5949_)) as u8;
                    if v_isSharedCheck_5989_ == 0 {
                        v_unused_5990_ = lean_ctor_get(v_m_5949_, 1);
                        lean_dec(v_unused_5990_);
                        v_unused_5991_ = lean_ctor_get(v_m_5949_, 0);
                        lean_dec(v_unused_5991_);
                        v___x_5970_ = v_m_5949_;
                        v_isShared_5971_ = v_isSharedCheck_5989_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_5949_);
                        v___x_5970_ = lean_box(0);
                        v_isShared_5971_ = v_isSharedCheck_5989_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_5951_);
                    lean_dec(v_a_5950_);
                    return v_m_5949_;
                }
            }
            1 => {
                v___x_5972_ = lean_unsigned_to_nat(1);
                v_size_x27_5973_ = lean_nat_add(v_size_5952_, v___x_5972_);
                lean_dec(v_size_5952_);
                lean_inc(v_bkt_5967_);
                v___x_5974_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5974_, 0, v_a_5950_);
                lean_ctor_set(v___x_5974_, 1, v_b_5951_);
                lean_ctor_set(v___x_5974_, 2, v_bkt_5967_);
                v_buckets_x27_5975_ = lean_array_uset(v_buckets_5953_, v___x_5966_, v___x_5974_);
                v___x_5976_ = lean_unsigned_to_nat(4);
                v___x_5977_ = lean_nat_mul(v_size_x27_5973_, v___x_5976_);
                v___x_5978_ = lean_unsigned_to_nat(3);
                v___x_5979_ = lean_nat_div(v___x_5977_, v___x_5978_);
                lean_dec(v___x_5977_);
                v___x_5980_ = lean_array_get_size(v_buckets_x27_5975_);
                v___x_5981_ = lean_nat_dec_le(v___x_5979_, v___x_5980_);
                lean_dec(v___x_5979_);
                if v___x_5981_ == 0 {
                    v_val_5982_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_buckets_x27_5975_);
                    if v_isShared_5971_ == 0 {
                        lean_ctor_set(v___x_5970_, 1, v_val_5982_);
                        lean_ctor_set(v___x_5970_, 0, v_size_x27_5973_);
                        v___x_5984_ = v___x_5970_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5985_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_size_x27_5973_);
                        lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_val_5982_);
                        v___x_5984_ = v_reuseFailAlloc_5985_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_5971_ == 0 {
                        lean_ctor_set(v___x_5970_, 1, v_buckets_x27_5975_);
                        lean_ctor_set(v___x_5970_, 0, v_size_x27_5973_);
                        v___x_5987_ = v___x_5970_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5988_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5988_, 0, v_size_x27_5973_);
                        lean_ctor_set(v_reuseFailAlloc_5988_, 1, v_buckets_x27_5975_);
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
    mut v___x_5992_: *mut LeanObject,
    mut v_a_5993_: *mut LeanObject,
    mut v_e_5994_: *mut LeanObject,
    mut v___y_5995_: *mut LeanObject,
    mut v___y_5996_: *mut LeanObject,
    mut v___y_5997_: *mut LeanObject,
    mut v___y_5998_: *mut LeanObject,
    mut v___y_5999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6006_: u8 = 0;
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantHyps_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6016_: u8 = 0;
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6023_: u8 = 0;
    let mut v_reuseFailAlloc_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6001_ = lean_st_ref_take(v___y_5995_);
                v_relevantTerms_6002_ = lean_ctor_get(v___x_6001_, 0);
                v_relevantHyps_6003_ = lean_ctor_get(v___x_6001_, 1);
                v_isSharedCheck_6025_ = (!lean_is_exclusive(v___x_6001_)) as u8;
                if v_isSharedCheck_6025_ == 0 {
                    v___x_6005_ = v___x_6001_;
                    v_isShared_6006_ = v_isSharedCheck_6025_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_relevantHyps_6003_);
                    lean_inc(v_relevantTerms_6002_);
                    lean_dec(v___x_6001_);
                    v___x_6005_ = lean_box(0);
                    v_isShared_6006_ = v_isSharedCheck_6025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6007_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_relevantTerms_6002_, v_e_5994_, v___x_5992_);
                if v_isShared_6006_ == 0 {
                    lean_ctor_set(v___x_6005_, 0, v___x_6007_);
                    v___x_6009_ = v___x_6005_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6024_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6024_, 0, v___x_6007_);
                    lean_ctor_set(v_reuseFailAlloc_6024_, 1, v_relevantHyps_6003_);
                    v___x_6009_ = v_reuseFailAlloc_6024_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6010_ = lean_st_ref_set(v___y_5995_, v___x_6009_);
                v___x_6011_ = lean_st_ref_take(v___y_5995_);
                v_relevantTerms_6012_ = lean_ctor_get(v___x_6011_, 0);
                v_relevantHyps_6013_ = lean_ctor_get(v___x_6011_, 1);
                v_isSharedCheck_6023_ = (!lean_is_exclusive(v___x_6011_)) as u8;
                if v_isSharedCheck_6023_ == 0 {
                    v___x_6015_ = v___x_6011_;
                    v_isShared_6016_ = v_isSharedCheck_6023_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_relevantHyps_6013_);
                    lean_inc(v_relevantTerms_6012_);
                    lean_dec(v___x_6011_);
                    v___x_6015_ = lean_box(0);
                    v_isShared_6016_ = v_isSharedCheck_6023_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6017_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_relevantHyps_6013_, v_a_5993_, v___x_5992_);
                if v_isShared_6016_ == 0 {
                    lean_ctor_set(v___x_6015_, 1, v___x_6017_);
                    v___x_6019_ = v___x_6015_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6022_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_relevantTerms_6012_);
                    lean_ctor_set(v_reuseFailAlloc_6022_, 1, v___x_6017_);
                    v___x_6019_ = v_reuseFailAlloc_6022_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6020_ = lean_st_ref_set(v___y_5995_, v___x_6019_);
                v___x_6021_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6021_, 0, v___x_5992_);
                return v___x_6021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed(
    mut v___x_6026_: *mut LeanObject,
    mut v_a_6027_: *mut LeanObject,
    mut v_e_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
    mut v___y_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
    mut v___y_6034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6035_: *mut LeanObject = core::ptr::null_mut();
    v_res_6035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1(v___x_6026_, v_a_6027_, v_e_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_);
    lean_dec(v___y_6033_);
    lean_dec_ref(v___y_6032_);
    lean_dec(v___y_6031_);
    lean_dec_ref(v___y_6030_);
    lean_dec(v___y_6029_);
    return v_res_6035_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(
    mut v_e_6045_: *mut LeanObject,
) -> u8 {
    let mut v___y_6047_: u8 = 0;
    let mut v___x_6048_: u8 = 0;
    let mut v___x_6049_: u8 = 0;
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: u8 = 0;
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0___closed__2;
                v___x_6051_ = lean_unsigned_to_nat(1);
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
    mut v_e_6055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6056_: u8 = 0;
    let mut v_r_6057_: *mut LeanObject = core::ptr::null_mut();
    v_res_6056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__0(v_e_6055_);
    lean_dec_ref(v_e_6055_);
    v_r_6057_ = lean_box((v_res_6056_) as usize);
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
    mut v_e_6061_: *mut LeanObject,
    mut v_a_6062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: usize = 0;
    let mut v___x_6067_: usize = 0;
    let mut v___x_6068_: usize = 0;
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: usize = 0;
    let mut v___x_6071_: u8 = 0;
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6077_: u8 = 0;
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6085_: u8 = 0;
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6064_ = lean_st_ref_get(v_a_6062_);
                v_visited_6065_ = lean_ctor_get(v___x_6064_, 0);
                lean_inc_ref(v_visited_6065_);
                lean_dec(v___x_6064_);
                v___x_6066_ = lean_ptr_addr(v_e_6061_);
                v___x_6067_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0_once), _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___closed__0);
                v___x_6068_ = lean_usize_mod(v___x_6066_, v___x_6067_);
                v___x_6069_ = lean_array_uget(v_visited_6065_, v___x_6068_);
                lean_dec_ref(v_visited_6065_);
                v___x_6070_ = lean_ptr_addr(v___x_6069_);
                lean_dec(v___x_6069_);
                v___x_6071_ = lean_usize_dec_eq(v___x_6070_, v___x_6066_);
                if v___x_6071_ == 0 {
                    v___x_6072_ = lean_st_ref_take(v_a_6062_);
                    v_visited_6073_ = lean_ctor_get(v___x_6072_, 0);
                    v_checked_6074_ = lean_ctor_get(v___x_6072_, 1);
                    v_isSharedCheck_6085_ = (!lean_is_exclusive(v___x_6072_)) as u8;
                    if v_isSharedCheck_6085_ == 0 {
                        v___x_6076_ = v___x_6072_;
                        v_isShared_6077_ = v_isSharedCheck_6085_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_checked_6074_);
                        lean_inc(v_visited_6073_);
                        lean_dec(v___x_6072_);
                        v___x_6076_ = lean_box(0);
                        v_isShared_6077_ = v_isSharedCheck_6085_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_6061_);
                    v___x_6086_ = lean_box((v___x_6071_) as usize);
                    v___x_6087_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6087_, 0, v___x_6086_);
                    return v___x_6087_;
                }
            }
            1 => {
                v___x_6078_ = lean_array_uset(v_visited_6073_, v___x_6068_, v_e_6061_);
                if v_isShared_6077_ == 0 {
                    lean_ctor_set(v___x_6076_, 0, v___x_6078_);
                    v___x_6080_ = v___x_6076_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6084_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6084_, 0, v___x_6078_);
                    lean_ctor_set(v_reuseFailAlloc_6084_, 1, v_checked_6074_);
                    v___x_6080_ = v_reuseFailAlloc_6084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6081_ = lean_st_ref_set(v_a_6062_, v___x_6080_);
                v___x_6082_ = lean_box((v___x_6071_) as usize);
                v___x_6083_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6083_, 0, v___x_6082_);
                return v___x_6083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg___boxed(
    mut v_e_6088_: *mut LeanObject,
    mut v_a_6089_: *mut LeanObject,
    mut v___y_6090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6091_: *mut LeanObject = core::ptr::null_mut();
    v_res_6091_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_6088_, v_a_6089_);
    lean_dec(v_a_6089_);
    return v_res_6091_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(
    mut v_m_6092_: *mut LeanObject,
    mut v_a_6093_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: u8 = 0;
    v_buckets_6094_ = lean_ctor_get(v_m_6092_, 1);
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
    mut v_m_6110_: *mut LeanObject,
    mut v_a_6111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6112_: u8 = 0;
    let mut v_r_6113_: *mut LeanObject = core::ptr::null_mut();
    v_res_6112_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_6110_, v_a_6111_);
    lean_dec_ref(v_a_6111_);
    lean_dec_ref(v_m_6110_);
    v_r_6113_ = lean_box((v_res_6112_) as usize);
    return v_r_6113_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(
    mut v_e_6114_: *mut LeanObject,
    mut v_a_6115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: u8 = 0;
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6125_: u8 = 0;
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6134_: u8 = 0;
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6117_ = lean_st_ref_get(v_a_6115_);
                v_checked_6118_ = lean_ctor_get(v___x_6117_, 1);
                lean_inc_ref(v_checked_6118_);
                lean_dec(v___x_6117_);
                v___x_6119_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_checked_6118_, v_e_6114_);
                lean_dec_ref(v_checked_6118_);
                if v___x_6119_ == 0 {
                    v___x_6120_ = lean_st_ref_take(v_a_6115_);
                    v_visited_6121_ = lean_ctor_get(v___x_6120_, 0);
                    v_checked_6122_ = lean_ctor_get(v___x_6120_, 1);
                    v_isSharedCheck_6134_ = (!lean_is_exclusive(v___x_6120_)) as u8;
                    if v_isSharedCheck_6134_ == 0 {
                        v___x_6124_ = v___x_6120_;
                        v_isShared_6125_ = v_isSharedCheck_6134_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_checked_6122_);
                        lean_inc(v_visited_6121_);
                        lean_dec(v___x_6120_);
                        v___x_6124_ = lean_box(0);
                        v_isShared_6125_ = v_isSharedCheck_6134_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_6114_);
                    v___x_6135_ = lean_box((v___x_6119_) as usize);
                    v___x_6136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6136_, 0, v___x_6135_);
                    return v___x_6136_;
                }
            }
            1 => {
                v___x_6126_ = lean_box(0);
                v___x_6127_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_checked_6122_, v_e_6114_, v___x_6126_);
                if v_isShared_6125_ == 0 {
                    lean_ctor_set(v___x_6124_, 1, v___x_6127_);
                    v___x_6129_ = v___x_6124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6133_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6133_, 0, v_visited_6121_);
                    lean_ctor_set(v_reuseFailAlloc_6133_, 1, v___x_6127_);
                    v___x_6129_ = v_reuseFailAlloc_6133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6130_ = lean_st_ref_set(v_a_6115_, v___x_6129_);
                v___x_6131_ = lean_box((v___x_6119_) as usize);
                v___x_6132_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6132_, 0, v___x_6131_);
                return v___x_6132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg___boxed(
    mut v_e_6137_: *mut LeanObject,
    mut v_a_6138_: *mut LeanObject,
    mut v___y_6139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6140_: *mut LeanObject = core::ptr::null_mut();
    v_res_6140_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_6137_, v_a_6138_);
    lean_dec(v_a_6138_);
    return v_res_6140_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(
    mut v_p_6141_: *mut LeanObject,
    mut v_f_6142_: *mut LeanObject,
    mut v_stopWhenVisited_6143_: u8,
    mut v_e_6144_: *mut LeanObject,
    mut v_a_6145_: *mut LeanObject,
    mut v___y_6146_: *mut LeanObject,
    mut v___y_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
    mut v___y_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6194_: u8 = 0;
    let mut v___x_6195_: u8 = 0;
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: u8 = 0;
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: u8 = 0;
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6204_: u8 = 0;
    let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6209_: u8 = 0;
    let mut v_unused_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6214_: u8 = 0;
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6218_: u8 = 0;
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6223_: u8 = 0;
    let mut v_a_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6227_: u8 = 0;
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_6144_);
                v___x_6190_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_6144_, v_a_6145_);
                if lean_obj_tag(v___x_6190_) == 0 {
                    v_a_6191_ = lean_ctor_get(v___x_6190_, 0);
                    v_isSharedCheck_6223_ = (!lean_is_exclusive(v___x_6190_)) as u8;
                    if v_isSharedCheck_6223_ == 0 {
                        v___x_6193_ = v___x_6190_;
                        v_isShared_6194_ = v_isSharedCheck_6223_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6191_);
                        lean_dec(v___x_6190_);
                        v___x_6193_ = lean_box(0);
                        v_isShared_6194_ = v_isSharedCheck_6223_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_6144_);
                    lean_dec_ref(v_f_6142_);
                    lean_dec_ref(v_p_6141_);
                    v_a_6224_ = lean_ctor_get(v___x_6190_, 0);
                    v_isSharedCheck_6231_ = (!lean_is_exclusive(v___x_6190_)) as u8;
                    if v_isSharedCheck_6231_ == 0 {
                        v___x_6226_ = v___x_6190_;
                        v_isShared_6227_ = v_isSharedCheck_6231_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_6224_);
                        lean_dec(v___x_6190_);
                        v___x_6226_ = lean_box(0);
                        v_isShared_6227_ = v_isSharedCheck_6231_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_f_6142_);
                lean_inc_ref(v_p_6141_);
                v___x_6161_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6141_, v_f_6142_, v_stopWhenVisited_6143_, v_d_6158_, v___y_6160_, v___y_6157_, v___y_6153_, v___y_6155_, v___y_6156_, v___y_6154_);
                if lean_obj_tag(v___x_6161_) == 0 {
                    lean_dec_ref_known(v___x_6161_, 1);
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
                    lean_dec_ref(v_b_6159_);
                    lean_dec_ref(v_f_6142_);
                    lean_dec_ref(v_p_6141_);
                    return v___x_6161_;
                }
            }
            2 => match lean_obj_tag(v_e_6144_) {
                7 => {
                    v_binderType_6170_ = lean_ctor_get(v_e_6144_, 1);
                    lean_inc_ref(v_binderType_6170_);
                    v_body_6171_ = lean_ctor_get(v_e_6144_, 2);
                    lean_inc_ref(v_body_6171_);
                    lean_dec_ref_known(v_e_6144_, 3);
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
                    v_binderType_6172_ = lean_ctor_get(v_e_6144_, 1);
                    lean_inc_ref(v_binderType_6172_);
                    v_body_6173_ = lean_ctor_get(v_e_6144_, 2);
                    lean_inc_ref(v_body_6173_);
                    lean_dec_ref_known(v_e_6144_, 3);
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
                    v_type_6174_ = lean_ctor_get(v_e_6144_, 1);
                    lean_inc_ref(v_type_6174_);
                    v_value_6175_ = lean_ctor_get(v_e_6144_, 2);
                    lean_inc_ref(v_value_6175_);
                    v_body_6176_ = lean_ctor_get(v_e_6144_, 3);
                    lean_inc_ref(v_body_6176_);
                    lean_dec_ref_known(v_e_6144_, 4);
                    lean_inc_ref(v_f_6142_);
                    lean_inc_ref(v_p_6141_);
                    v___x_6177_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6141_, v_f_6142_, v_stopWhenVisited_6143_, v_type_6174_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
                    if lean_obj_tag(v___x_6177_) == 0 {
                        lean_dec_ref_known(v___x_6177_, 1);
                        lean_inc_ref(v_f_6142_);
                        lean_inc_ref(v_p_6141_);
                        v___x_6178_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6141_, v_f_6142_, v_stopWhenVisited_6143_, v_value_6175_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
                        if lean_obj_tag(v___x_6178_) == 0 {
                            lean_dec_ref_known(v___x_6178_, 1);
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
                            lean_dec_ref(v_body_6176_);
                            lean_dec_ref(v_f_6142_);
                            lean_dec_ref(v_p_6141_);
                            return v___x_6178_;
                        }
                    } else {
                        lean_dec_ref(v_body_6176_);
                        lean_dec_ref(v_value_6175_);
                        lean_dec_ref(v_f_6142_);
                        lean_dec_ref(v_p_6141_);
                        return v___x_6177_;
                    }
                }
                5 => {
                    v_fn_6180_ = lean_ctor_get(v_e_6144_, 0);
                    lean_inc_ref(v_fn_6180_);
                    v_arg_6181_ = lean_ctor_get(v_e_6144_, 1);
                    lean_inc_ref(v_arg_6181_);
                    lean_dec_ref_known(v_e_6144_, 2);
                    lean_inc_ref(v_f_6142_);
                    lean_inc_ref(v_p_6141_);
                    v___x_6182_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6141_, v_f_6142_, v_stopWhenVisited_6143_, v_fn_6180_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
                    if lean_obj_tag(v___x_6182_) == 0 {
                        lean_dec_ref_known(v___x_6182_, 1);
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
                        lean_dec_ref(v_arg_6181_);
                        lean_dec_ref(v_f_6142_);
                        lean_dec_ref(v_p_6141_);
                        return v___x_6182_;
                    }
                }
                10 => {
                    v_expr_6184_ = lean_ctor_get(v_e_6144_, 1);
                    lean_inc_ref(v_expr_6184_);
                    lean_dec_ref_known(v_e_6144_, 2);
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
                    v_struct_6186_ = lean_ctor_get(v_e_6144_, 2);
                    lean_inc_ref(v_struct_6186_);
                    lean_dec_ref_known(v_e_6144_, 3);
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
                    lean_dec_ref(v_e_6144_);
                    lean_dec_ref(v_f_6142_);
                    lean_dec_ref(v_p_6141_);
                    v___x_6188_ = lean_box(0);
                    v___x_6189_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6189_, 0, v___x_6188_);
                    return v___x_6189_;
                }
            },
            3 => {
                v___x_6195_ = (lean_unbox(v_a_6191_) as u8);
                lean_dec(v_a_6191_);
                if v___x_6195_ == 0 {
                    lean_del_object(v___x_6193_);
                    lean_inc_ref(v_p_6141_);
                    lean_inc_ref(v_e_6144_);
                    v___x_6196_ = lean_apply_1(v_p_6141_, v_e_6144_);
                    v___x_6197_ = (lean_unbox(v___x_6196_) as u8);
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
                        lean_inc_ref(v_e_6144_);
                        v___x_6198_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_6144_, v_a_6145_);
                        if lean_obj_tag(v___x_6198_) == 0 {
                            v_a_6199_ = lean_ctor_get(v___x_6198_, 0);
                            lean_inc(v_a_6199_);
                            lean_dec_ref_known(v___x_6198_, 1);
                            v___x_6200_ = (lean_unbox(v_a_6199_) as u8);
                            lean_dec(v_a_6199_);
                            if v___x_6200_ == 0 {
                                lean_inc_ref(v_f_6142_);
                                lean_inc(v___y_6150_);
                                lean_inc_ref(v___y_6149_);
                                lean_inc(v___y_6148_);
                                lean_inc_ref(v___y_6147_);
                                lean_inc(v___y_6146_);
                                lean_inc_ref(v_e_6144_);
                                v___x_6201_ = lean_apply_7(
                                    v_f_6142_,
                                    v_e_6144_,
                                    v___y_6146_,
                                    v___y_6147_,
                                    v___y_6148_,
                                    v___y_6149_,
                                    v___y_6150_,
                                    lean_box(0),
                                );
                                if lean_obj_tag(v___x_6201_) == 0 {
                                    v_isSharedCheck_6209_ = (!lean_is_exclusive(v___x_6201_)) as u8;
                                    if v_isSharedCheck_6209_ == 0 {
                                        v_unused_6210_ = lean_ctor_get(v___x_6201_, 0);
                                        lean_dec(v_unused_6210_);
                                        v___x_6203_ = v___x_6201_;
                                        v_isShared_6204_ = v_isSharedCheck_6209_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v___x_6201_);
                                        v___x_6203_ = lean_box(0);
                                        v_isShared_6204_ = v_isSharedCheck_6209_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_e_6144_);
                                    lean_dec_ref(v_f_6142_);
                                    lean_dec_ref(v_p_6141_);
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
                            lean_dec_ref(v_e_6144_);
                            lean_dec_ref(v_f_6142_);
                            lean_dec_ref(v_p_6141_);
                            v_a_6211_ = lean_ctor_get(v___x_6198_, 0);
                            v_isSharedCheck_6218_ = (!lean_is_exclusive(v___x_6198_)) as u8;
                            if v_isSharedCheck_6218_ == 0 {
                                v___x_6213_ = v___x_6198_;
                                v_isShared_6214_ = v_isSharedCheck_6218_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6211_);
                                lean_dec(v___x_6198_);
                                v___x_6213_ = lean_box(0);
                                v_isShared_6214_ = v_isSharedCheck_6218_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_6144_);
                    lean_dec_ref(v_f_6142_);
                    lean_dec_ref(v_p_6141_);
                    v___x_6219_ = lean_box(0);
                    if v_isShared_6194_ == 0 {
                        lean_ctor_set(v___x_6193_, 0, v___x_6219_);
                        v___x_6221_ = v___x_6193_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6222_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6222_, 0, v___x_6219_);
                        v___x_6221_ = v_reuseFailAlloc_6222_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_stopWhenVisited_6143_ == 0 {
                    lean_del_object(v___x_6203_);
                    v___y_6164_ = v_a_6145_;
                    v___y_6165_ = v___y_6146_;
                    v___y_6166_ = v___y_6147_;
                    v___y_6167_ = v___y_6148_;
                    v___y_6168_ = v___y_6149_;
                    v___y_6169_ = v___y_6150_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_e_6144_);
                    lean_dec_ref(v_f_6142_);
                    lean_dec_ref(v_p_6141_);
                    v___x_6205_ = lean_box(0);
                    if v_isShared_6204_ == 0 {
                        lean_ctor_set(v___x_6203_, 0, v___x_6205_);
                        v___x_6207_ = v___x_6203_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6208_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6208_, 0, v___x_6205_);
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
                    v_reuseFailAlloc_6217_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6217_, 0, v_a_6211_);
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
                    v_reuseFailAlloc_6230_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6230_, 0, v_a_6224_);
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
    mut v_p_6232_: *mut LeanObject,
    mut v_f_6233_: *mut LeanObject,
    mut v_stopWhenVisited_6234_: *mut LeanObject,
    mut v_e_6235_: *mut LeanObject,
    mut v_a_6236_: *mut LeanObject,
    mut v___y_6237_: *mut LeanObject,
    mut v___y_6238_: *mut LeanObject,
    mut v___y_6239_: *mut LeanObject,
    mut v___y_6240_: *mut LeanObject,
    mut v___y_6241_: *mut LeanObject,
    mut v___y_6242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stopWhenVisited_boxed_6243_: u8 = 0;
    let mut v_res_6244_: *mut LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_6243_ = (lean_unbox(v_stopWhenVisited_6234_) as u8);
    v_res_6244_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6232_, v_f_6233_, v_stopWhenVisited_boxed_6243_, v_e_6235_, v_a_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
    lean_dec(v___y_6241_);
    lean_dec_ref(v___y_6240_);
    lean_dec(v___y_6239_);
    lean_dec_ref(v___y_6238_);
    lean_dec(v___y_6237_);
    lean_dec(v_a_6236_);
    return v_res_6244_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3(
    mut v_p_6245_: *mut LeanObject,
    mut v_f_6246_: *mut LeanObject,
    mut v_e_6247_: *mut LeanObject,
    mut v_stopWhenVisited_6248_: u8,
    mut v___y_6249_: *mut LeanObject,
    mut v___y_6250_: *mut LeanObject,
    mut v___y_6251_: *mut LeanObject,
    mut v___y_6252_: *mut LeanObject,
    mut v___y_6253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6261_: u8 = 0;
    let mut v___x_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6266_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6255_ = l_Lean_ForEachExprWhere_initCache;
                v___x_6256_ = lean_st_mk_ref(v___x_6255_);
                v___x_6257_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5(v_p_6245_, v_f_6246_, v_stopWhenVisited_6248_, v_e_6247_, v___x_6256_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
                if lean_obj_tag(v___x_6257_) == 0 {
                    v_a_6258_ = lean_ctor_get(v___x_6257_, 0);
                    v_isSharedCheck_6266_ = (!lean_is_exclusive(v___x_6257_)) as u8;
                    if v_isSharedCheck_6266_ == 0 {
                        v___x_6260_ = v___x_6257_;
                        v_isShared_6261_ = v_isSharedCheck_6266_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6258_);
                        lean_dec(v___x_6257_);
                        v___x_6260_ = lean_box(0);
                        v_isShared_6261_ = v_isSharedCheck_6266_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6256_);
                    return v___x_6257_;
                }
            }
            1 => {
                v___x_6262_ = lean_st_ref_get(v___x_6256_);
                lean_dec(v___x_6256_);
                lean_dec(v___x_6262_);
                if v_isShared_6261_ == 0 {
                    v___x_6264_ = v___x_6260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6265_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6265_, 0, v_a_6258_);
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
    mut v_p_6267_: *mut LeanObject,
    mut v_f_6268_: *mut LeanObject,
    mut v_e_6269_: *mut LeanObject,
    mut v_stopWhenVisited_6270_: *mut LeanObject,
    mut v___y_6271_: *mut LeanObject,
    mut v___y_6272_: *mut LeanObject,
    mut v___y_6273_: *mut LeanObject,
    mut v___y_6274_: *mut LeanObject,
    mut v___y_6275_: *mut LeanObject,
    mut v___y_6276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stopWhenVisited_boxed_6277_: u8 = 0;
    let mut v_res_6278_: *mut LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_6277_ = (lean_unbox(v_stopWhenVisited_6270_) as u8);
    v_res_6278_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3(v_p_6267_, v_f_6268_, v_e_6269_, v_stopWhenVisited_boxed_6277_, v___y_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
    lean_dec(v___y_6275_);
    lean_dec_ref(v___y_6274_);
    lean_dec(v___y_6273_);
    lean_dec_ref(v___y_6272_);
    lean_dec(v___y_6271_);
    return v_res_6278_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4(
    mut v_as_6280_: *mut LeanObject,
    mut v_sz_6281_: usize,
    mut v_i_6282_: usize,
    mut v_b_6283_: *mut LeanObject,
    mut v___y_6284_: *mut LeanObject,
    mut v___y_6285_: *mut LeanObject,
    mut v___y_6286_: *mut LeanObject,
    mut v___y_6287_: *mut LeanObject,
    mut v___y_6288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6290_: u8 = 0;
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: usize = 0;
    let mut v___x_6302_: usize = 0;
    let mut v_a_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6307_: u8 = 0;
    let mut v___x_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6311_: u8 = 0;
    let mut v_a_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6315_: u8 = 0;
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6290_ = lean_usize_dec_lt(v_i_6282_, v_sz_6281_);
                if v___x_6290_ == 0 {
                    v___x_6291_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6291_, 0, v_b_6283_);
                    return v___x_6291_;
                } else {
                    v_a_6292_ = lean_array_uget_borrowed(v_as_6280_, v_i_6282_);
                    lean_inc(v_a_6292_);
                    v___x_6293_ = l_Lean_FVarId_getType___redArg(
                        v_a_6292_,
                        v___y_6285_,
                        v___y_6287_,
                        v___y_6288_,
                    );
                    if lean_obj_tag(v___x_6293_) == 0 {
                        v_a_6294_ = lean_ctor_get(v___x_6293_, 0);
                        lean_inc(v_a_6294_);
                        lean_dec_ref_known(v___x_6293_, 1);
                        v___x_6295_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__2___redArg(v_a_6294_, v___y_6286_);
                        if lean_obj_tag(v___x_6295_) == 0 {
                            v_a_6296_ = lean_ctor_get(v___x_6295_, 0);
                            lean_inc(v_a_6296_);
                            lean_dec_ref_known(v___x_6295_, 1);
                            v___f_6297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___closed__0;
                            v___x_6298_ = lean_box(0);
                            lean_inc(v_a_6292_);
                            v___f_6299_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4___lam__1___boxed as *mut core::ffi::c_void, 9, 2);
                            lean_closure_set(v___f_6299_, 0, v___x_6298_);
                            lean_closure_set(v___f_6299_, 1, v_a_6292_);
                            v___x_6300_ = l_Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3(v___f_6297_, v___f_6299_, v_a_6296_, v___x_6290_, v___y_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_);
                            if lean_obj_tag(v___x_6300_) == 0 {
                                lean_dec_ref_known(v___x_6300_, 1);
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
                            v_a_6304_ = lean_ctor_get(v___x_6295_, 0);
                            v_isSharedCheck_6311_ = (!lean_is_exclusive(v___x_6295_)) as u8;
                            if v_isSharedCheck_6311_ == 0 {
                                v___x_6306_ = v___x_6295_;
                                v_isShared_6307_ = v_isSharedCheck_6311_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_6304_);
                                lean_dec(v___x_6295_);
                                v___x_6306_ = lean_box(0);
                                v_isShared_6307_ = v_isSharedCheck_6311_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_6312_ = lean_ctor_get(v___x_6293_, 0);
                        v_isSharedCheck_6319_ = (!lean_is_exclusive(v___x_6293_)) as u8;
                        if v_isSharedCheck_6319_ == 0 {
                            v___x_6314_ = v___x_6293_;
                            v_isShared_6315_ = v_isSharedCheck_6319_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6312_);
                            lean_dec(v___x_6293_);
                            v___x_6314_ = lean_box(0);
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
                    v_reuseFailAlloc_6310_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_a_6304_);
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
                    v_reuseFailAlloc_6318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6318_, 0, v_a_6312_);
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
    mut v_as_6320_: *mut LeanObject,
    mut v_sz_6321_: *mut LeanObject,
    mut v_i_6322_: *mut LeanObject,
    mut v_b_6323_: *mut LeanObject,
    mut v___y_6324_: *mut LeanObject,
    mut v___y_6325_: *mut LeanObject,
    mut v___y_6326_: *mut LeanObject,
    mut v___y_6327_: *mut LeanObject,
    mut v___y_6328_: *mut LeanObject,
    mut v___y_6329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6330_: usize = 0;
    let mut v_i_boxed_6331_: usize = 0;
    let mut v_res_6332_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6330_ = lean_unbox_usize(v_sz_6321_);
    lean_dec(v_sz_6321_);
    v_i_boxed_6331_ = lean_unbox_usize(v_i_6322_);
    lean_dec(v_i_6322_);
    v_res_6332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4(v_as_6320_, v_sz_boxed_6330_, v_i_boxed_6331_, v_b_6323_, v___y_6324_, v___y_6325_, v___y_6326_, v___y_6327_, v___y_6328_);
    lean_dec(v___y_6328_);
    lean_dec_ref(v___y_6327_);
    lean_dec(v___y_6326_);
    lean_dec_ref(v___y_6325_);
    lean_dec(v___y_6324_);
    lean_dec_ref(v_as_6320_);
    return v_res_6332_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0(
    mut v___y_6333_: *mut LeanObject,
    mut v___y_6334_: *mut LeanObject,
    mut v___y_6335_: *mut LeanObject,
    mut v___y_6336_: *mut LeanObject,
    mut v___y_6337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6342_: usize = 0;
    let mut v___x_6343_: usize = 0;
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6347_: u8 = 0;
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_relevantTerms_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: u8 = 0;
    let mut v___x_6353_: u8 = 0;
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: u8 = 0;
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6363_: u8 = 0;
    let mut v_unused_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6368_: u8 = 0;
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6372_: u8 = 0;
    let mut v_a_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6376_: u8 = 0;
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6339_ =
                    l_Lean_Meta_getPropHyps(v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_);
                if lean_obj_tag(v___x_6339_) == 0 {
                    v_a_6340_ = lean_ctor_get(v___x_6339_, 0);
                    lean_inc(v_a_6340_);
                    lean_dec_ref_known(v___x_6339_, 1);
                    v___x_6341_ = lean_box(0);
                    v_sz_6342_ = lean_array_size(v_a_6340_);
                    v___x_6343_ = 0usize;
                    v___x_6344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__4(v_a_6340_, v_sz_6342_, v___x_6343_, v___x_6341_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_, v___y_6337_);
                    lean_dec(v_a_6340_);
                    if lean_obj_tag(v___x_6344_) == 0 {
                        v_isSharedCheck_6363_ = (!lean_is_exclusive(v___x_6344_)) as u8;
                        if v_isSharedCheck_6363_ == 0 {
                            v_unused_6364_ = lean_ctor_get(v___x_6344_, 0);
                            lean_dec(v_unused_6364_);
                            v___x_6346_ = v___x_6344_;
                            v_isShared_6347_ = v_isSharedCheck_6363_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_6344_);
                            v___x_6346_ = lean_box(0);
                            v_isShared_6347_ = v_isSharedCheck_6363_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6365_ = lean_ctor_get(v___x_6344_, 0);
                        v_isSharedCheck_6372_ = (!lean_is_exclusive(v___x_6344_)) as u8;
                        if v_isSharedCheck_6372_ == 0 {
                            v___x_6367_ = v___x_6344_;
                            v_isShared_6368_ = v_isSharedCheck_6372_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6365_);
                            lean_dec(v___x_6344_);
                            v___x_6367_ = lean_box(0);
                            v_isShared_6368_ = v_isSharedCheck_6372_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_6373_ = lean_ctor_get(v___x_6339_, 0);
                    v_isSharedCheck_6380_ = (!lean_is_exclusive(v___x_6339_)) as u8;
                    if v_isSharedCheck_6380_ == 0 {
                        v___x_6375_ = v___x_6339_;
                        v_isShared_6376_ = v_isSharedCheck_6380_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6373_);
                        lean_dec(v___x_6339_);
                        v___x_6375_ = lean_box(0);
                        v_isShared_6376_ = v_isSharedCheck_6380_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6348_ = lean_st_ref_get(v___y_6333_);
                v_relevantTerms_6349_ = lean_ctor_get(v___x_6348_, 0);
                lean_inc_ref(v_relevantTerms_6349_);
                lean_dec(v___x_6348_);
                v_size_6350_ = lean_ctor_get(v_relevantTerms_6349_, 0);
                lean_inc(v_size_6350_);
                lean_dec_ref(v_relevantTerms_6349_);
                v___x_6351_ = lean_unsigned_to_nat(0);
                v___x_6352_ = lean_nat_dec_eq(v_size_6350_, v___x_6351_);
                lean_dec(v_size_6350_);
                if v___x_6352_ == 0 {
                    v___x_6353_ = 1;
                    v___x_6354_ = lean_box((v___x_6353_) as usize);
                    if v_isShared_6347_ == 0 {
                        lean_ctor_set(v___x_6346_, 0, v___x_6354_);
                        v___x_6356_ = v___x_6346_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6357_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6357_, 0, v___x_6354_);
                        v___x_6356_ = v_reuseFailAlloc_6357_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6358_ = 0;
                    v___x_6359_ = lean_box((v___x_6358_) as usize);
                    if v_isShared_6347_ == 0 {
                        lean_ctor_set(v___x_6346_, 0, v___x_6359_);
                        v___x_6361_ = v___x_6346_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6362_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6362_, 0, v___x_6359_);
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
                    v_reuseFailAlloc_6371_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6371_, 0, v_a_6365_);
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
                    v_reuseFailAlloc_6379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6379_, 0, v_a_6373_);
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
    mut v___y_6381_: *mut LeanObject,
    mut v___y_6382_: *mut LeanObject,
    mut v___y_6383_: *mut LeanObject,
    mut v___y_6384_: *mut LeanObject,
    mut v___y_6385_: *mut LeanObject,
    mut v___y_6386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6387_: *mut LeanObject = core::ptr::null_mut();
    v_res_6387_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___lam__0(v___y_6381_, v___y_6382_, v___y_6383_, v___y_6384_, v___y_6385_);
    lean_dec(v___y_6385_);
    lean_dec_ref(v___y_6384_);
    lean_dec(v___y_6383_);
    lean_dec_ref(v___y_6382_);
    lean_dec(v___y_6381_);
    return v_res_6387_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize(
    mut v_goal_6389_: *mut LeanObject,
    mut v_a_6390_: *mut LeanObject,
    mut v_a_6391_: *mut LeanObject,
    mut v_a_6392_: *mut LeanObject,
    mut v_a_6393_: *mut LeanObject,
    mut v_a_6394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    v___f_6396_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___closed__0;
    v___x_6397_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize_spec__14___redArg(v_goal_6389_, v___f_6396_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_, v_a_6394_);
    return v___x_6397_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize___boxed(
    mut v_goal_6398_: *mut LeanObject,
    mut v_a_6399_: *mut LeanObject,
    mut v_a_6400_: *mut LeanObject,
    mut v_a_6401_: *mut LeanObject,
    mut v_a_6402_: *mut LeanObject,
    mut v_a_6403_: *mut LeanObject,
    mut v_a_6404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6405_: *mut LeanObject = core::ptr::null_mut();
    v_res_6405_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize(v_goal_6398_, v_a_6399_, v_a_6400_, v_a_6401_, v_a_6402_, v_a_6403_);
    lean_dec(v_a_6403_);
    lean_dec_ref(v_a_6402_);
    lean_dec(v_a_6401_);
    lean_dec_ref(v_a_6400_);
    lean_dec(v_a_6399_);
    return v_res_6405_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0(
    mut v_00_u03b2_6406_: *mut LeanObject,
    mut v_m_6407_: *mut LeanObject,
    mut v_a_6408_: *mut LeanObject,
    mut v_b_6409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    v___x_6410_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__0___redArg(v_m_6407_, v_a_6408_, v_b_6409_);
    return v___x_6410_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1(
    mut v_00_u03b2_6411_: *mut LeanObject,
    mut v_m_6412_: *mut LeanObject,
    mut v_a_6413_: *mut LeanObject,
    mut v_b_6414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6415_: *mut LeanObject = core::ptr::null_mut();
    v___x_6415_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1___redArg(v_m_6412_, v_a_6413_, v_b_6414_);
    return v___x_6415_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(
    mut v_00_u03b2_6416_: *mut LeanObject,
    mut v_a_6417_: *mut LeanObject,
    mut v_x_6418_: *mut LeanObject,
) -> u8 {
    let mut v___x_6419_: u8 = 0;
    v___x_6419_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___redArg(v_a_6417_, v_x_6418_);
    return v___x_6419_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1___boxed(
    mut v_00_u03b2_6420_: *mut LeanObject,
    mut v_a_6421_: *mut LeanObject,
    mut v_x_6422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6423_: u8 = 0;
    let mut v_r_6424_: *mut LeanObject = core::ptr::null_mut();
    v_res_6423_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__1(v_00_u03b2_6420_, v_a_6421_, v_x_6422_);
    lean_dec(v_x_6422_);
    lean_dec(v_a_6421_);
    v_r_6424_ = lean_box((v_res_6423_) as usize);
    return v_r_6424_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2(
    mut v_00_u03b2_6425_: *mut LeanObject,
    mut v_data_6426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    v___x_6427_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2___redArg(v_data_6426_);
    return v___x_6427_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(
    mut v_e_6428_: *mut LeanObject,
    mut v_a_6429_: *mut LeanObject,
    mut v___y_6430_: *mut LeanObject,
    mut v___y_6431_: *mut LeanObject,
    mut v___y_6432_: *mut LeanObject,
    mut v___y_6433_: *mut LeanObject,
    mut v___y_6434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    v___x_6436_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___redArg(v_e_6428_, v_a_6429_);
    return v___x_6436_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7___boxed(
    mut v_e_6437_: *mut LeanObject,
    mut v_a_6438_: *mut LeanObject,
    mut v___y_6439_: *mut LeanObject,
    mut v___y_6440_: *mut LeanObject,
    mut v___y_6441_: *mut LeanObject,
    mut v___y_6442_: *mut LeanObject,
    mut v___y_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6445_: *mut LeanObject = core::ptr::null_mut();
    v_res_6445_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__7(v_e_6437_, v_a_6438_, v___y_6439_, v___y_6440_, v___y_6441_, v___y_6442_, v___y_6443_);
    lean_dec(v___y_6443_);
    lean_dec_ref(v___y_6442_);
    lean_dec(v___y_6441_);
    lean_dec_ref(v___y_6440_);
    lean_dec(v___y_6439_);
    lean_dec(v_a_6438_);
    return v_res_6445_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4(
    mut v_00_u03b2_6446_: *mut LeanObject,
    mut v_i_6447_: *mut LeanObject,
    mut v_source_6448_: *mut LeanObject,
    mut v_target_6449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6450_: *mut LeanObject = core::ptr::null_mut();
    v___x_6450_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4___redArg(v_i_6447_, v_source_6448_, v_target_6449_);
    return v___x_6450_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(
    mut v_e_6451_: *mut LeanObject,
    mut v_a_6452_: *mut LeanObject,
    mut v___y_6453_: *mut LeanObject,
    mut v___y_6454_: *mut LeanObject,
    mut v___y_6455_: *mut LeanObject,
    mut v___y_6456_: *mut LeanObject,
    mut v___y_6457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    v___x_6459_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___redArg(v_e_6451_, v_a_6452_);
    return v___x_6459_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8___boxed(
    mut v_e_6460_: *mut LeanObject,
    mut v_a_6461_: *mut LeanObject,
    mut v___y_6462_: *mut LeanObject,
    mut v___y_6463_: *mut LeanObject,
    mut v___y_6464_: *mut LeanObject,
    mut v___y_6465_: *mut LeanObject,
    mut v___y_6466_: *mut LeanObject,
    mut v___y_6467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6468_: *mut LeanObject = core::ptr::null_mut();
    v_res_6468_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8(v_e_6460_, v_a_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_);
    lean_dec(v___y_6466_);
    lean_dec_ref(v___y_6465_);
    lean_dec(v___y_6464_);
    lean_dec_ref(v___y_6463_);
    lean_dec(v___y_6462_);
    lean_dec(v_a_6461_);
    return v_res_6468_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7(
    mut v_00_u03b2_6469_: *mut LeanObject,
    mut v_x_6470_: *mut LeanObject,
    mut v_x_6471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    v___x_6472_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__1_spec__2_spec__4_spec__7___redArg(v_x_6470_, v_x_6471_);
    return v___x_6472_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(
    mut v_00_u03b2_6473_: *mut LeanObject,
    mut v_m_6474_: *mut LeanObject,
    mut v_a_6475_: *mut LeanObject,
) -> u8 {
    let mut v___x_6476_: u8 = 0;
    v___x_6476_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___redArg(v_m_6474_, v_a_6475_);
    return v___x_6476_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11___boxed(
    mut v_00_u03b2_6477_: *mut LeanObject,
    mut v_m_6478_: *mut LeanObject,
    mut v_a_6479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6480_: u8 = 0;
    let mut v_r_6481_: *mut LeanObject = core::ptr::null_mut();
    v_res_6480_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_6477_, v_m_6478_, v_a_6479_);
    lean_dec_ref(v_a_6479_);
    lean_dec_ref(v_m_6478_);
    v_r_6481_ = lean_box((v_res_6480_) as usize);
    return v_r_6481_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize(
    mut v_goal_6482_: *mut LeanObject,
    mut v_a_6483_: *mut LeanObject,
    mut v_a_6484_: *mut LeanObject,
    mut v_a_6485_: *mut LeanObject,
    mut v_a_6486_: *mut LeanObject,
    mut v_a_6487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6493_: u8 = 0;
    let mut v___x_6494_: u8 = 0;
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6499_: u8 = 0;
    let mut v_a_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6503_: u8 = 0;
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_goal_6482_);
                v___x_6489_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_detectSize(v_goal_6482_, v_a_6483_, v_a_6484_, v_a_6485_, v_a_6486_, v_a_6487_);
                if lean_obj_tag(v___x_6489_) == 0 {
                    v_a_6490_ = lean_ctor_get(v___x_6489_, 0);
                    v_isSharedCheck_6499_ = (!lean_is_exclusive(v___x_6489_)) as u8;
                    if v_isSharedCheck_6499_ == 0 {
                        v___x_6492_ = v___x_6489_;
                        v_isShared_6493_ = v_isSharedCheck_6499_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6490_);
                        lean_dec(v___x_6489_);
                        v___x_6492_ = lean_box(0);
                        v_isShared_6493_ = v_isSharedCheck_6499_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_goal_6482_);
                    v_a_6500_ = lean_ctor_get(v___x_6489_, 0);
                    v_isSharedCheck_6507_ = (!lean_is_exclusive(v___x_6489_)) as u8;
                    if v_isSharedCheck_6507_ == 0 {
                        v___x_6502_ = v___x_6489_;
                        v_isShared_6503_ = v_isSharedCheck_6507_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6500_);
                        lean_dec(v___x_6489_);
                        v___x_6502_ = lean_box(0);
                        v_isShared_6503_ = v_isSharedCheck_6507_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6494_ = (lean_unbox(v_a_6490_) as u8);
                lean_dec(v_a_6490_);
                if v___x_6494_ == 0 {
                    if v_isShared_6493_ == 0 {
                        lean_ctor_set(v___x_6492_, 0, v_goal_6482_);
                        v___x_6496_ = v___x_6492_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6497_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6497_, 0, v_goal_6482_);
                        v___x_6496_ = v_reuseFailAlloc_6497_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6492_);
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
                    v_reuseFailAlloc_6506_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6506_, 0, v_a_6500_);
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
    mut v_goal_6508_: *mut LeanObject,
    mut v_a_6509_: *mut LeanObject,
    mut v_a_6510_: *mut LeanObject,
    mut v_a_6511_: *mut LeanObject,
    mut v_a_6512_: *mut LeanObject,
    mut v_a_6513_: *mut LeanObject,
    mut v_a_6514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6515_: *mut LeanObject = core::ptr::null_mut();
    v_res_6515_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize(v_goal_6508_, v_a_6509_, v_a_6510_, v_a_6511_, v_a_6512_, v_a_6513_);
    lean_dec(v_a_6513_);
    lean_dec_ref(v_a_6512_);
    lean_dec(v_a_6511_);
    lean_dec_ref(v_a_6510_);
    lean_dec(v_a_6509_);
    return v_res_6515_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    v___x_6518_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6518_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    v___x_6519_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__1,
    );
    v___x_6520_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6520_, 0, v___x_6519_);
    return v___x_6520_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    v___x_6521_ = lean_unsigned_to_nat(0);
    v___x_6522_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2,
    );
    v___x_6523_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6523_, 0, v___x_6522_);
    lean_ctor_set(v___x_6523_, 1, v___x_6521_);
    return v___x_6523_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    v___x_6524_ = lean_unsigned_to_nat(32);
    v___x_6525_ = lean_mk_empty_array_with_capacity(v___x_6524_);
    v___x_6526_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6526_, 0, v___x_6525_);
    return v___x_6526_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_6527_: usize = 0;
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    v___x_6527_ = 5usize;
    v___x_6528_ = lean_unsigned_to_nat(0);
    v___x_6529_ = lean_unsigned_to_nat(32);
    v___x_6530_ = lean_mk_empty_array_with_capacity(v___x_6529_);
    v___x_6531_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__4,
    );
    v___x_6532_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_6532_, 0, v___x_6531_);
    lean_ctor_set(v___x_6532_, 1, v___x_6530_);
    lean_ctor_set(v___x_6532_, 2, v___x_6528_);
    lean_ctor_set(v___x_6532_, 3, v___x_6528_);
    lean_ctor_set_usize(v___x_6532_, 4, v___x_6527_);
    return v___x_6532_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    v___x_6533_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__5,
    );
    v___x_6534_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__2,
    );
    v___x_6535_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_6535_, 0, v___x_6534_);
    lean_ctor_set(v___x_6535_, 1, v___x_6534_);
    lean_ctor_set(v___x_6535_, 2, v___x_6534_);
    lean_ctor_set(v___x_6535_, 3, v___x_6533_);
    return v___x_6535_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut LeanObject = core::ptr::null_mut();
    v___x_6536_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__6,
    );
    v___x_6537_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__3,
    );
    v___x_6538_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6538_, 0, v___x_6537_);
    lean_ctor_set(v___x_6538_, 1, v___x_6536_);
    return v___x_6538_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8()
-> *mut LeanObject {
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    v___x_6539_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_replaceSize___lam__4___closed__12);
    v___x_6540_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6540_, 0, v___x_6539_);
    lean_ctor_set(v___x_6540_, 1, v___x_6539_);
    return v___x_6540_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(
    mut v_goal_6541_: *mut LeanObject,
    mut v___y_6542_: *mut LeanObject,
    mut v___y_6543_: *mut LeanObject,
    mut v___y_6544_: *mut LeanObject,
    mut v___y_6545_: *mut LeanObject,
    mut v___y_6546_: *mut LeanObject,
    mut v___y_6547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxSteps_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: u8 = 0;
    let mut v___x_6557_: u8 = 0;
    let mut v___x_6558_: u8 = 0;
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6575_: u8 = 0;
    let mut v_fst_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6580_: u8 = 0;
    let mut v_snd_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6588_: u8 = 0;
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6596_: u8 = 0;
    let mut v_a_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6600_: u8 = 0;
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6604_: u8 = 0;
    let mut v_isSharedCheck_6605_: u8 = 0;
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6609_: u8 = 0;
    let mut v_a_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6613_: u8 = 0;
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6617_: u8 = 0;
    let mut v_a_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6621_: u8 = 0;
    let mut v___x_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6625_: u8 = 0;
    let mut v_a_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6629_: u8 = 0;
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6633_: u8 = 0;
    let mut v_a_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6637_: u8 = 0;
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6641_: u8 = 0;
    let mut v_a_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6645_: u8 = 0;
    let mut v___x_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6549_ = l_Lean_Meta_Tactic_BVDecide_intToBitVecExt;
                v___x_6550_ =
                    l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_6549_, v___y_6547_);
                if lean_obj_tag(v___x_6550_) == 0 {
                    v_a_6551_ = lean_ctor_get(v___x_6550_, 0);
                    lean_inc(v_a_6551_);
                    lean_dec_ref_known(v___x_6550_, 1);
                    v___x_6552_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v___y_6547_);
                    if lean_obj_tag(v___x_6552_) == 0 {
                        v_a_6553_ = lean_ctor_get(v___x_6552_, 0);
                        lean_inc(v_a_6553_);
                        lean_dec_ref_known(v___x_6552_, 1);
                        v_maxSteps_6554_ = lean_ctor_get(v___y_6542_, 1);
                        v___x_6555_ = lean_unsigned_to_nat(2);
                        v___x_6556_ = 0;
                        v___x_6557_ = 1;
                        v___x_6558_ = 0;
                        v___x_6559_ = lean_box(0);
                        lean_inc(v_maxSteps_6554_);
                        v___x_6560_ = lean_alloc_ctor(0, 3, (29) as u32);
                        lean_ctor_set(v___x_6560_, 0, v_maxSteps_6554_);
                        lean_ctor_set(v___x_6560_, 1, v___x_6555_);
                        lean_ctor_set(v___x_6560_, 2, v___x_6559_);
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 5) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 6) as u32,
                            v___x_6558_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 7) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 9) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 10) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 11) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 12) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 13) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 14) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 15) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 17) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 18) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 19) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 20) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 21) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 22) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 23) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 24) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 25) as u32,
                            v___x_6557_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 26) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 27) as u32,
                            v___x_6556_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6560_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 28) as u32,
                            v___x_6557_,
                        );
                        v___x_6561_ = lean_unsigned_to_nat(1);
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
                        if lean_obj_tag(v___x_6565_) == 0 {
                            v_a_6566_ = lean_ctor_get(v___x_6565_, 0);
                            lean_inc(v_a_6566_);
                            lean_dec_ref_known(v___x_6565_, 1);
                            lean_inc(v_goal_6541_);
                            v___x_6567_ = l_Lean_MVarId_getNondepPropHyps(
                                v_goal_6541_,
                                v___y_6544_,
                                v___y_6545_,
                                v___y_6546_,
                                v___y_6547_,
                            );
                            if lean_obj_tag(v___x_6567_) == 0 {
                                v_a_6568_ = lean_ctor_get(v___x_6567_, 0);
                                lean_inc(v_a_6568_);
                                lean_dec_ref_known(v___x_6567_, 1);
                                v___x_6569_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__0;
                                v___x_6570_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__7);
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
                                if lean_obj_tag(v___x_6571_) == 0 {
                                    v_a_6572_ = lean_ctor_get(v___x_6571_, 0);
                                    v_isSharedCheck_6609_ = (!lean_is_exclusive(v___x_6571_)) as u8;
                                    if v_isSharedCheck_6609_ == 0 {
                                        v___x_6574_ = v___x_6571_;
                                        v_isShared_6575_ = v_isSharedCheck_6609_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6572_);
                                        lean_dec(v___x_6571_);
                                        v___x_6574_ = lean_box(0);
                                        v_isShared_6575_ = v_isSharedCheck_6609_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_6610_ = lean_ctor_get(v___x_6571_, 0);
                                    v_isSharedCheck_6617_ = (!lean_is_exclusive(v___x_6571_)) as u8;
                                    if v_isSharedCheck_6617_ == 0 {
                                        v___x_6612_ = v___x_6571_;
                                        v_isShared_6613_ = v_isSharedCheck_6617_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6610_);
                                        lean_dec(v___x_6571_);
                                        v___x_6612_ = lean_box(0);
                                        v_isShared_6613_ = v_isSharedCheck_6617_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_6566_);
                                lean_dec(v_goal_6541_);
                                v_a_6618_ = lean_ctor_get(v___x_6567_, 0);
                                v_isSharedCheck_6625_ = (!lean_is_exclusive(v___x_6567_)) as u8;
                                if v_isSharedCheck_6625_ == 0 {
                                    v___x_6620_ = v___x_6567_;
                                    v_isShared_6621_ = v_isSharedCheck_6625_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_6618_);
                                    lean_dec(v___x_6567_);
                                    v___x_6620_ = lean_box(0);
                                    v_isShared_6621_ = v_isSharedCheck_6625_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_goal_6541_);
                            v_a_6626_ = lean_ctor_get(v___x_6565_, 0);
                            v_isSharedCheck_6633_ = (!lean_is_exclusive(v___x_6565_)) as u8;
                            if v_isSharedCheck_6633_ == 0 {
                                v___x_6628_ = v___x_6565_;
                                v_isShared_6629_ = v_isSharedCheck_6633_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_6626_);
                                lean_dec(v___x_6565_);
                                v___x_6628_ = lean_box(0);
                                v_isShared_6629_ = v_isSharedCheck_6633_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6551_);
                        lean_dec(v_goal_6541_);
                        v_a_6634_ = lean_ctor_get(v___x_6552_, 0);
                        v_isSharedCheck_6641_ = (!lean_is_exclusive(v___x_6552_)) as u8;
                        if v_isSharedCheck_6641_ == 0 {
                            v___x_6636_ = v___x_6552_;
                            v_isShared_6637_ = v_isSharedCheck_6641_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_6634_);
                            lean_dec(v___x_6552_);
                            v___x_6636_ = lean_box(0);
                            v_isShared_6637_ = v_isSharedCheck_6641_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_goal_6541_);
                    v_a_6642_ = lean_ctor_get(v___x_6550_, 0);
                    v_isSharedCheck_6649_ = (!lean_is_exclusive(v___x_6550_)) as u8;
                    if v_isSharedCheck_6649_ == 0 {
                        v___x_6644_ = v___x_6550_;
                        v_isShared_6645_ = v_isSharedCheck_6649_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_6642_);
                        lean_dec(v___x_6550_);
                        v___x_6644_ = lean_box(0);
                        v_isShared_6645_ = v_isSharedCheck_6649_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6576_ = lean_ctor_get(v_a_6572_, 0);
                lean_inc(v_fst_6576_);
                lean_dec(v_a_6572_);
                if lean_obj_tag(v_fst_6576_) == 1 {
                    lean_del_object(v___x_6574_);
                    v_val_6577_ = lean_ctor_get(v_fst_6576_, 0);
                    v_isSharedCheck_6605_ = (!lean_is_exclusive(v_fst_6576_)) as u8;
                    if v_isSharedCheck_6605_ == 0 {
                        v___x_6579_ = v_fst_6576_;
                        v_isShared_6580_ = v_isSharedCheck_6605_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_6577_);
                        lean_dec(v_fst_6576_);
                        v___x_6579_ = lean_box(0);
                        v_isShared_6580_ = v_isSharedCheck_6605_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_6576_);
                    if v_isShared_6575_ == 0 {
                        lean_ctor_set(v___x_6574_, 0, v___x_6559_);
                        v___x_6607_ = v___x_6574_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6608_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6608_, 0, v___x_6559_);
                        v___x_6607_ = v_reuseFailAlloc_6608_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_6581_ = lean_ctor_get(v_val_6577_, 1);
                lean_inc(v_snd_6581_);
                lean_dec(v_val_6577_);
                v___x_6582_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8_once), _init_l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0___closed__8);
                v___x_6583_ = lean_st_mk_ref(v___x_6582_);
                v___x_6584_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec_0__Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass_handleSize(v_snd_6581_, v___x_6583_, v___y_6544_, v___y_6545_, v___y_6546_, v___y_6547_);
                if lean_obj_tag(v___x_6584_) == 0 {
                    v_a_6585_ = lean_ctor_get(v___x_6584_, 0);
                    v_isSharedCheck_6596_ = (!lean_is_exclusive(v___x_6584_)) as u8;
                    if v_isSharedCheck_6596_ == 0 {
                        v___x_6587_ = v___x_6584_;
                        v_isShared_6588_ = v_isSharedCheck_6596_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6585_);
                        lean_dec(v___x_6584_);
                        v___x_6587_ = lean_box(0);
                        v_isShared_6588_ = v_isSharedCheck_6596_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6583_);
                    lean_del_object(v___x_6579_);
                    v_a_6597_ = lean_ctor_get(v___x_6584_, 0);
                    v_isSharedCheck_6604_ = (!lean_is_exclusive(v___x_6584_)) as u8;
                    if v_isSharedCheck_6604_ == 0 {
                        v___x_6599_ = v___x_6584_;
                        v_isShared_6600_ = v_isSharedCheck_6604_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6597_);
                        lean_dec(v___x_6584_);
                        v___x_6599_ = lean_box(0);
                        v_isShared_6600_ = v_isSharedCheck_6604_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6589_ = lean_st_ref_get(v___x_6583_);
                lean_dec(v___x_6583_);
                lean_dec(v___x_6589_);
                if v_isShared_6580_ == 0 {
                    lean_ctor_set(v___x_6579_, 0, v_a_6585_);
                    v___x_6591_ = v___x_6579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6595_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6595_, 0, v_a_6585_);
                    v___x_6591_ = v_reuseFailAlloc_6595_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6588_ == 0 {
                    lean_ctor_set(v___x_6587_, 0, v___x_6591_);
                    v___x_6593_ = v___x_6587_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6594_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 0, v___x_6591_);
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
                    v_reuseFailAlloc_6603_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6603_, 0, v_a_6597_);
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
                    v_reuseFailAlloc_6616_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6616_, 0, v_a_6610_);
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
                    v_reuseFailAlloc_6624_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6624_, 0, v_a_6618_);
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
                    v_reuseFailAlloc_6632_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6632_, 0, v_a_6626_);
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
                    v_reuseFailAlloc_6640_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6640_, 0, v_a_6634_);
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
                    v_reuseFailAlloc_6648_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6648_, 0, v_a_6642_);
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
    mut v_goal_6650_: *mut LeanObject,
    mut v___y_6651_: *mut LeanObject,
    mut v___y_6652_: *mut LeanObject,
    mut v___y_6653_: *mut LeanObject,
    mut v___y_6654_: *mut LeanObject,
    mut v___y_6655_: *mut LeanObject,
    mut v___y_6656_: *mut LeanObject,
    mut v___y_6657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6658_: *mut LeanObject = core::ptr::null_mut();
    v_res_6658_ = l_Lean_Meta_Tactic_BVDecide_Normalize_intToBitVecPass___lam__0(
        v_goal_6650_,
        v___y_6651_,
        v___y_6652_,
        v___y_6653_,
        v___y_6654_,
        v___y_6655_,
        v___y_6656_,
    );
    lean_dec(v___y_6656_);
    lean_dec_ref(v___y_6655_);
    lean_dec(v___y_6654_);
    lean_dec_ref(v___y_6653_);
    lean_dec(v___y_6652_);
    lean_dec_ref(v___y_6651_);
    return v_res_6658_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Normalize_IntToBitVec(builtin);
}
